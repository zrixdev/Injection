// MLBInject — internal ESP for MLBB (arm64, injected via ElleKit/TrollFools)
// MANUAL Metal rendering: own CAMetalLayer + CADisplayLink, explicit drawable
// acquisition and clear. No MTKView. Plus a plain-UIView red marker to split
// window-vs-Metal diagnosis.
// Logs to MLBB Documents/mlbesp_log.txt.

#import <UIKit/UIKit.h>
#import <Metal/Metal.h>
#import <QuartzCore/CAMetalLayer.h>
#import <objc/runtime.h>
#import <os/lock.h>
#import <mach/mach.h>
#import <mach-o/dyld.h>
#import <unistd.h>
#import <time.h>
#import <cmath>
#import <cstdio>
#import <cstring>
#import <stdarg.h>

#include "imgui.h"
#include "backends/imgui_impl_metal.h"

extern "C" {
kern_return_t mach_vm_read_overwrite(vm_map_t, mach_vm_address_t,
                        mach_vm_size_t, mach_vm_address_t, mach_vm_size_t *);
kern_return_t mach_vm_region(vm_map_t, mach_vm_address_t *, mach_vm_size_t *,
                        vm_region_flavor_t, vm_region_info_t,
                        mach_msg_type_number_t *, mach_port_t *);
}

// ---------------- logging ----------------
static void mlog(const char *fmt, ...) {
    static char path[512] = {0};
    if (!path[0]) {
        NSArray *dirs = NSSearchPathForDirectoriesInDomains(
            NSDocumentDirectory, NSUserDomainMask, YES);
        if (![dirs count]) return;
        NSString *doc = [dirs objectAtIndex:0];
        snprintf(path, sizeof(path), "%s/mlbesp_log.txt",
                 doc.fileSystemRepresentation);
    }
    FILE *f = fopen(path, "a");
    if (!f) return;
    time_t t = time(NULL);
    struct tm tmv; localtime_r(&t, &tmv);
    fprintf(f, "[%02d:%02d:%02d] ", tmv.tm_hour, tmv.tm_min, tmv.tm_sec);
    va_list ap; va_start(ap, fmt);
    vfprintf(f, fmt, ap);
    va_end(ap);
    fprintf(f, "\n");
    fclose(f);
}

// ---------------- verified constants ----------------
#define RVA_BM_CLASS_SLOT    0x7BFBF70ULL
#define OFF_CLASS_NAME       0x10
#define OFF_CLASS_STATICS    0xA8
#define OFF_STATICS_INSTANCE 0x0

#define OFF_ENT_HP           0x1AC
#define OFF_ENT_HPMAX        0x1B0
#define OFF_ENT_CANSIGHT     0x254
#define OFF_ENT_POS_A        0x1D0
#define OFF_ENT_POS_B        0x298
#define OFF_ENT_DEATH        0xD0

#define BOX_K                240.0f
#define GAME_W               667.0f
#define GAME_H               375.0f
#define MAX_ENTS             64

// ---------------- shared frame ----------------
typedef struct {
    float sx, sy, box_h, box_w;
    int32_t hp, hpmax, visible, dead;
} EspEnt;

typedef struct {
    uint32_t entity_count, matrix_ok, pos_sel;
    char status[128];
    EspEnt ents[MAX_ENTS];
} EspFrame;

static EspFrame       g_frame;
static os_unfair_lock g_lock = OS_UNFAIR_LOCK_INIT;

// ---------------- safe self-reads ----------------
static bool rd(uint64_t addr, void *out, size_t len) {
    if (!addr) return false;
    mach_vm_size_t got = 0;
    return mach_vm_read_overwrite(mach_task_self(), (mach_vm_address_t)addr,
            (mach_vm_size_t)len, (mach_vm_address_t)(uintptr_t)out, &got)
            == KERN_SUCCESS && got == len;
}
static uint64_t rd64(uint64_t a)  { uint64_t v = 0; return rd(a, &v, 8) ? v : 0; }
static int32_t  rdi32(uint64_t a) { int32_t  v = 0; return rd(a, &v, 4) ? v : 0; }
static bool rd_vec3(uint64_t a, float o[3]) { return rd(a, o, 12); }

static bool rd_cstr(uint64_t addr, char *out, size_t cap) {
    if (!addr || !rd(addr, out, cap)) return false;
    out[cap - 1] = 0;
    return out[0] != 0;
}

static uint64_t uf_base(void) {
    for (uint32_t i = 0; i < _dyld_image_count(); i++) {
        const char *n = _dyld_get_image_name(i);
        if (n && strstr(n, "UnityFramework"))
            return (uint64_t)_dyld_get_image_header(i);
    }
    return 0;
}

// ---------------- resolve / walk ----------------
static uint64_t g_uf = 0;
static float    g_vp[16];
static bool     g_mat_ok = false;
static int      g_list_off = -1;
static int      g_pos_sel = 0;
static int      g_static_a_ticks = 0;

typedef struct KlassCache { uint64_t obj; bool hero; } KlassCache;
static KlassCache g_kcache[512];
static int g_kcache_n = 0;

static bool is_hero_obj(uint64_t obj) {
    if (!obj) return false;
    for (int i = 0; i < g_kcache_n; i++)
        if (g_kcache[i].obj == obj) return g_kcache[i].hero;
    uint64_t k = rd64(obj);
    char nm[64];
    bool hero = k && rd_cstr(rd64(k + OFF_CLASS_NAME), nm, sizeof(nm)) &&
                strncmp(nm, "ShowPlayer", 10) == 0;
    if (g_kcache_n < 512) {
        g_kcache[g_kcache_n].obj = obj;
        g_kcache[g_kcache_n].hero = hero;
        g_kcache_n++;
    }
    return hero;
}

static bool list_valid(uint64_t lst) {
    uint64_t arr  = rd64(lst + 0x10);
    int32_t  size = rdi32(lst + 0x18);
    if (!arr || size < 1 || size > 512) return false;
    if (rdi32(arr + 0x18) != size) return false;
    for (int i = 0; i < size && i < 8; i++) {
        uint64_t e = rd64(arr + 0x20 + 8ull * i);
        if (!e) continue;
        uint64_t k = rd64(e);
        if (!k) continue;
        char nm[64];
        if (rd_cstr(rd64(k + OFF_CLASS_NAME), nm, sizeof(nm)) && strstr(nm, "Show"))
            return true;
    }
    return false;
}

static int discover_list(uint64_t bm) {
    static const int cands[] = { 0x198, 0x78, 0x188, 0x190, 0x1A0, 0x1A8,
                                 0x1B0, 0x80, 0x88, 0x90, 0x70 };
    for (size_t i = 0; i < sizeof(cands) / sizeof(cands[0]); i++) {
        uint64_t lst = rd64(bm + cands[i]);
        if (lst && list_valid(lst)) {
            mlog("entity list @ BM+0x%x", cands[i]);
            return cands[i];
        }
    }
    return -1;
}

// ---------------- camera matrix scan ----------------
typedef struct Snap { float x, y, z; } Snap;

static int vp_score(const float m[16], const Snap *es, int n) {
    int total = 0, on = 0;
    for (int i = 0; i < n; i++) {
        if (fabsf(es[i].x) > 300 || fabsf(es[i].z) > 300 ||
            es[i].y < -100 || es[i].y > 500) continue;
        float cx = m[0]*es[i].x + m[4]*es[i].y + m[8]*es[i].z  + m[12];
        float cy = m[1]*es[i].x + m[5]*es[i].y + m[9]*es[i].z  + m[13];
        float cw = m[3]*es[i].x + m[7]*es[i].y + m[11]*es[i].z + m[15];
        total++;
        if (cw > 0.01f) {
            float nx = cx / cw, ny = cy / cw;
            if (fabsf(nx) <= 1.3f && fabsf(ny) <= 1.3f) on++;
        }
    }
    return (total >= 3 && on * 10 >= total * 6) ? on : -1;
}

static bool scan_region_for_vp(uint64_t addr, uint64_t len,
                               const Snap *es, int n) {
    static uint8_t buf[256 * 1024 + 64];
    const uint64_t chunk = 256 * 1024;
    for (uint64_t off = 0; off < len; off += chunk) {
        uint64_t want = chunk + 64;
        if (off + want > len) want = len - off;
        if (!rd(addr + off, buf, want)) return false;
        for (uint64_t o = 0; o + 64 <= chunk && off + o + 64 <= want; o += 16) {
            const float *m = (const float *)(buf + o);
            if (!(m[15] != 0.0f && (fabsf(m[3]) + fabsf(m[7]) + fabsf(m[11])) > 1e-6f))
                continue;
            bool finite = true;
            for (int i = 0; i < 16; i++)
                if (!(fabsf(m[i]) < 1e9f)) { finite = false; break; }
            if (!finite) continue;
            if (vp_score(m, es, n) > 0) {
                memcpy(g_vp, m, sizeof(g_vp));
                return true;
            }
        }
    }
    return false;
}

static bool scan_matrix(const Snap *es, int n) {
    mach_vm_address_t addr = 1;
    uint64_t budget = 96ull * 1024 * 1024;
    while (budget > 0) {
        mach_vm_size_t size = 0;
        vm_region_basic_info_data_64_t info;
        mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64;
        mach_port_t obj = MACH_PORT_NULL;
        kern_return_t kr = mach_vm_region(mach_task_self(), &addr, &size,
                VM_REGION_BASIC_INFO_64, (vm_region_info_t)&info, &cnt, &obj);
        if (kr != KERN_SUCCESS) return false;
        if (obj) mach_port_deallocate(mach_task_self(), obj);
        if (addr < size) return false;
        if ((info.protection & VM_PROT_READ) &&
            !(info.protection & VM_PROT_EXECUTE) &&
            size <= 512ull * 1024 * 1024) {
            if (scan_region_for_vp(addr, size, es, n)) return true;
            budget = (size < budget) ? budget - size : 0;
        }
        addr += size;
    }
    return false;
}

static bool project(float x, float y, float z, float *sx, float *sy, float *cw) {
    float cx = g_vp[0]*x + g_vp[4]*y + g_vp[8]*z  + g_vp[12];
    float cy = g_vp[1]*x + g_vp[5]*y + g_vp[9]*z  + g_vp[13];
    float w  = g_vp[3]*x + g_vp[7]*y + g_vp[11]*z + g_vp[15];
    *cw = w;
    if (w <= 0.001f) return false;
    *sx = (cx / w * 0.5f + 0.5f) * GAME_W;
    *sy = (1.0f - (cy / w * 0.5f + 0.5f)) * GAME_H;
    return true;
}

// ---------------- worker thread ----------------
static void worker_loop(void) {
    static float prev_a[MAX_ENTS][3], prev_b[MAX_ENTS][3];
    static int prev_n = 0;

    for (;;) {
        if (!g_uf) {
            g_uf = uf_base();
            if (!g_uf) {
                EspFrame f; memset(&f, 0, sizeof f);
                snprintf(f.status, sizeof f.status, "waiting for UnityFramework...");
                os_unfair_lock_lock(&g_lock); g_frame = f; os_unfair_lock_unlock(&g_lock);
                sleep(1); continue;
            }
            mlog("UnityFramework @ 0x%llx", (unsigned long long)g_uf);
        }

        uint64_t klass = rd64(g_uf + RVA_BM_CLASS_SLOT);
        char nm[64];
        if (!klass || !rd_cstr(rd64(klass + OFF_CLASS_NAME), nm, sizeof(nm)) ||
            strcmp(nm, "BattleManager") != 0) {
            EspFrame f; memset(&f, 0, sizeof f);
            snprintf(f.status, sizeof f.status, "menu / lobby");
            os_unfair_lock_lock(&g_lock); g_frame = f; os_unfair_lock_unlock(&g_lock);
            g_list_off = -1; g_mat_ok = false; g_kcache_n = 0;
            g_pos_sel = 0; g_uf = 0;
            sleep(1); continue;
        }
        uint64_t statics = rd64(klass + OFF_CLASS_STATICS);
        uint64_t bm = statics ? rd64(statics + OFF_STATICS_INSTANCE) : 0;
        if (!bm) {
            EspFrame f; memset(&f, 0, sizeof f);
            snprintf(f.status, sizeof f.status, "lobby (no battle instance)");
            os_unfair_lock_lock(&g_lock); g_frame = f; os_unfair_lock_unlock(&g_lock);
            g_list_off = -1; g_mat_ok = false; g_kcache_n = 0; g_pos_sel = 0;
            usleep(500000); continue;
        }
        if (g_list_off < 0) {
            g_list_off = discover_list(bm);
            if (g_list_off < 0) {
                EspFrame f; memset(&f, 0, sizeof f);
                snprintf(f.status, sizeof f.status, "list not found yet");
                os_unfair_lock_lock(&g_lock); g_frame = f; os_unfair_lock_unlock(&g_lock);
                usleep(500000); continue;
            }
        }

        uint64_t lst = rd64(bm + g_list_off);
        uint64_t arr = lst ? rd64(lst + 0x10) : 0;
        int32_t  size = lst ? rdi32(lst + 0x18) : 0;
        if (!arr || size < 1 || size > 512) { g_list_off = -1; continue; }

        Snap snaps[MAX_ENTS];
        int snap_n = 0, count = 0;
        float move_a = 0, move_b = 0;
        EspFrame f;
        memset(&f, 0, sizeof f);

        for (int32_t i = 0; i < size && count < MAX_ENTS; i++) {
            uint64_t e = rd64(arr + 0x20 + 8ull * (uint64_t)i);
            if (!e || !is_hero_obj(e)) continue;

            float pa[3] = {0}, pb[3] = {0};
            if (!rd_vec3(e + OFF_ENT_POS_A, pa) || !rd_vec3(e + OFF_ENT_POS_B, pb))
                continue;
            if (count < prev_n) {
                move_a += fabsf(pa[0]-prev_a[count][0]) + fabsf(pa[2]-prev_a[count][2]);
                move_b += fabsf(pb[0]-prev_b[count][0]) + fabsf(pb[2]-prev_b[count][2]);
            }
            memcpy(prev_a[count], pa, 12);
            memcpy(prev_b[count], pb, 12);

            EspEnt *en = &f.ents[count];
            en->hp      = rdi32(e + OFF_ENT_HP);
            en->hpmax   = rdi32(e + OFF_ENT_HPMAX);
            en->visible = rdi32(e + OFF_ENT_CANSIGHT);
            en->dead    = (en->hp <= 0) || (rdi32(e + OFF_ENT_DEATH) != 0);

            if (snap_n < MAX_ENTS) {
                snaps[snap_n].x = (g_pos_sel == 0) ? pa[0] : pb[0];
                snaps[snap_n].y = (g_pos_sel == 0) ? pa[1] : pb[1];
                snaps[snap_n].z = (g_pos_sel == 0) ? pa[2] : pb[2];
                snap_n++;
            }
            count++;
        }
        prev_n = count;

        if (move_a < 0.01f && move_b > 0.5f) {
            if (++g_static_a_ticks >= 5) { g_pos_sel = 1; g_static_a_ticks = 0; }
        } else g_static_a_ticks = 0;

        if (!g_mat_ok && snap_n >= 3) g_mat_ok = scan_matrix(snaps, snap_n);

        f.matrix_ok = g_mat_ok ? 1 : 0;
        f.pos_sel   = (uint32_t)g_pos_sel;
        f.entity_count = 0;
        if (g_mat_ok) {
            for (int i = 0; i < count; i++) {
                float cw = 0;
                if (project(snaps[i].x, snaps[i].y, snaps[i].z,
                            &f.ents[i].sx, &f.ents[i].sy, &cw)) {
                    f.ents[i].box_h = BOX_K / cw;
                    f.ents[i].box_w = f.ents[i].box_h * 0.55f;
                    f.ents[f.entity_count++] = f.ents[i];
                }
            }
            snprintf(f.status, sizeof f.status, "ents=%u pos=%c",
                     f.entity_count, g_pos_sel ? 'B' : 'A');
        } else {
            snprintf(f.status, sizeof f.status, "scanning camera matrix... ents=%d", snap_n);
        }

        os_unfair_lock_lock(&g_lock);
        g_frame = f;
        os_unfair_lock_unlock(&g_lock);

        usleep(100000);
    }
}

// ---------------- config ----------------
struct EspCfg {
    bool esp_on, boxes, hp_bars, snaplines, vision_only, status_text;
    bool rot_right;
};
static EspCfg g_cfg = { true, true, true, false, true, true, true };

// ---------------- overlay state ----------------
static bool   g_menu_open = false;
static bool   g_initialized = false;
static bool   g_logged_first_frame = false;
static CGRect g_btn_rect_v = CGRectMake(GAME_W - 56, 8, 48, 48);
static id<MTLDevice>        g_dev = nil;
static id<MTLCommandQueue>  g_queue = nil;
static ImGuiContext        *g_imgui = nil;

static void feed_touch(UITouch *t, UIView *v, bool down, bool ended) {
    ImGuiIO &io = ImGui::GetIO();
    CGPoint p = [v convertPoint:[t locationInView:v] fromView:v];
    io.AddMousePosEvent(p.x, p.y);
    io.AddMouseButtonEvent(0, down && !ended);
}

// ---------------- MANUAL Metal view (no MTKView) ----------------
@interface ESPMetalView : UIView
@end

@implementation ESPMetalView
+ (Class)layerClass { return [CAMetalLayer class]; }

- (CAMetalLayer *)mlayer { return (CAMetalLayer *)self.layer; }

- (void)configure:(id<MTLDevice>)dev {
    CAMetalLayer *l = self.mlayer;
    l.device = dev;
    l.pixelFormat = MTLPixelFormatBGRA8Unorm;   // alpha-capable
    l.opaque = NO;                              // transparent compositing
    l.backgroundColor = NULL;
    l.framebufferOnly = YES;
    l.presentsWithTransaction = NO;
    l.maximumDrawableCount = 2;
    self.opaque = NO;
    self.backgroundColor = [UIColor clearColor];
    [self syncSize];
}

- (void)syncSize {
    CAMetalLayer *l = self.mlayer;
    CGFloat scale = self.window.screen.scale ?: 2.0;
    CGSize px = CGSizeMake(self.bounds.size.width * scale,
                           self.bounds.size.height * scale);
    if (l.drawableSize.width != px.width || l.drawableSize.height != px.height)
        l.drawableSize = px;
}

- (void)drawFrame {
    if (!g_initialized) return;
    [self syncSize];

    CAMetalLayer *l = self.mlayer;
    id<CAMetalDrawable> d = [l nextDrawable];
    if (!d) { static int nd=0; if(++nd==60) mlog("nextDrawable nil x60"); return; }

    MTLRenderPassDescriptor *rp = [MTLRenderPassDescriptor renderPassDescriptor];
    rp.colorAttachments[0].texture = d.texture;
    rp.colorAttachments[0].loadAction = MTLLoadActionClear;
    rp.colorAttachments[0].storeAction = MTLStoreActionStore;
    rp.colorAttachments[0].clearColor = MTLClearColorMake(0, 0, 0, 0);  // transparent

    if (!g_logged_first_frame) {
        g_logged_first_frame = true;
        mlog("manual metal first frame (%.0fx%.0f px)",
             l.drawableSize.width, l.drawableSize.height);
    }

    ImGui::SetCurrentContext(g_imgui);
    ImGuiIO &io = ImGui::GetIO();
    io.DisplaySize = ImVec2(self.bounds.size.width, self.bounds.size.height);
    io.DisplayFramebufferScale = ImVec2(l.drawableSize.width / self.bounds.size.width,
                                        l.drawableSize.height / self.bounds.size.height);
    io.DeltaTime = 1.0f / 30.0f;

    ImGui_ImplMetal_NewFrame(rp);
    ImGui::NewFrame();

    EspFrame f;
    os_unfair_lock_lock(&g_lock);
    f = g_frame;
    os_unfair_lock_unlock(&g_lock);

    ImDrawList *dl = ImGui::GetBackgroundDrawList();

    // ImGui-side ALIVE marker (proves the Metal pipeline renders)
    dl->AddRectFilled(ImVec2(4, 4), ImVec2(24, 24), IM_COL32(255, 0, 0, 255));
    dl->AddText(ImVec2(28, 8), IM_COL32(255, 60, 60, 255), "MLB ALIVE");

    if (g_cfg.esp_on && f.matrix_ok) {
        for (uint32_t i = 0; i < f.entity_count && i < MAX_ENTS; i++) {
            const EspEnt &e = f.ents[i];
            if (g_cfg.vision_only && !e.visible) continue;
            if (e.dead) continue;

            float h = e.box_h, w = e.box_w;
            float x0 = e.sx - w * 0.5f, y0 = e.sy - h;
            float x1 = e.sx + w * 0.5f, y1 = e.sy;
            ImU32 white = IM_COL32(255, 255, 255, 255);

            if (g_cfg.boxes)
                dl->AddRect(ImVec2(x0, y0), ImVec2(x1, y1), white, 0.0f, 0, 2.0f);

            if (g_cfg.hp_bars && e.hpmax > 0) {
                float pct = (float)e.hp / (float)e.hpmax;
                if (pct < 0) pct = 0; if (pct > 1) pct = 1;
                float bx = x0 - 6.0f;
                dl->AddRectFilled(ImVec2(bx, y0), ImVec2(bx + 3, y1), IM_COL32(20,20,20,200));
                ImU32 col = IM_COL32((int)(255 * (1 - pct)), (int)(255 * pct), 0, 255);
                dl->AddRectFilled(ImVec2(bx, y1 - (y1 - y0) * pct), ImVec2(bx + 3, y1), col);
            }

            if (g_cfg.snaplines)
                dl->AddLine(ImVec2(GAME_W * 0.5f, GAME_H), ImVec2(e.sx, y1), white, 1.0f);
        }
    }

    // toggle button
    ImGui::SetNextWindowPos(ImVec2(GAME_W - 56, 8));
    ImGui::PushStyleColor(ImGuiCol_WindowBg, 0);
    ImGui::Begin("##btn", nullptr, ImGuiWindowFlags_NoDecoration | ImGuiWindowFlags_NoMove |
                 ImGuiWindowFlags_NoNav | ImGuiWindowFlags_NoBackground |
                 ImGuiWindowFlags_AlwaysAutoResize | ImGuiWindowFlags_NoBringToFrontOnFocus);
    ImGui::InvisibleButton("btn", ImVec2(40, 40));
    if (ImGui::IsItemClicked()) g_menu_open = !g_menu_open;
    {
        ImVec2 mn = ImGui::GetItemRectMin(), mx = ImGui::GetItemRectMax();
        ImVec2 cc((mn.x + mx.x) * 0.5f, (mn.y + mx.y) * 0.5f);
        dl->AddCircleFilled(cc, 17.0f, g_menu_open ? IM_COL32(0,200,255,220) : IM_COL32(255,255,255,160));
        dl->AddCircle(cc, 17.0f, IM_COL32(0,0,0,255), 0, 2.0f);
    }
    ImGui::End();
    ImGui::PopStyleColor();

    if (g_cfg.status_text) {
        dl->AddText(ImVec2(8, 30), IM_COL32(0, 220, 255, 255), f.status);
        if (!f.matrix_ok)
            dl->AddText(ImVec2(8, 46), IM_COL32(255,200,0,255), "matrix: scanning...");
    }

    if (g_menu_open) {
        ImGui::SetNextWindowPos(ImVec2(60, 40), ImGuiCond_Once);
        ImGui::Begin("MLBB ESP", &g_menu_open, ImGuiWindowFlags_AlwaysAutoResize);
        ImGui::Checkbox("ESP enabled",    &g_cfg.esp_on);
        ImGui::Checkbox("Boxes",          &g_cfg.boxes);
        ImGui::Checkbox("HP bars",        &g_cfg.hp_bars);
        ImGui::Checkbox("Snaplines",      &g_cfg.snaplines);
        ImGui::Checkbox("Vision only (safe)", &g_cfg.vision_only);
        ImGui::Checkbox("Status text",    &g_cfg.status_text);
        ImGui::Separator();
        ImGui::Text("ents: %u  mat: %s  pos: %c", f.entity_count,
                    f.matrix_ok ? "ok" : "no", f.pos_sel ? 'B' : 'A');
        ImGui::End();
    }

    ImGui::Render();

    id<MTLCommandBuffer> cb = [g_queue commandBuffer];
    id<MTLRenderCommandEncoder> enc = [cb renderCommandEncoderWithDescriptor:rp];
    ImGui_ImplMetal_RenderDrawData(ImGui::GetDrawData(), cb, enc);
    [enc endEncoding];
    [cb presentDrawable:d];
    [cb commit];
}

- (void)touchesBegan:(NSSet<UITouch *> *)ts withEvent:(UIEvent *)e {
    for (UITouch *t in ts) feed_touch(t, self, true, false);
}
- (void)touchesMoved:(NSSet<UITouch *> *)ts withEvent:(UIEvent *)e {
    for (UITouch *t in ts) feed_touch(t, self, true, false);
}
- (void)touchesEnded:(NSSet<UITouch *> *)ts withEvent:(UIEvent *)e {
    for (UITouch *t in ts) feed_touch(t, self, false, true);
}
- (void)touchesCancelled:(NSSet<UITouch *> *)ts withEvent:(UIEvent *)e {
    for (UITouch *t in ts) feed_touch(t, self, false, true);
}
@end

@interface ESPWindow : UIWindow
@end
@implementation ESPWindow
- (UIView *)hitTest:(CGPoint)p withEvent:(UIEvent *)e {
    ESPMetalView *v = (ESPMetalView *)self.rootViewController.view;
    if (!v) return nil;
    CGPoint local = [v convertPoint:p fromView:self];
    if (g_menu_open) return v;
    if (CGRectContainsPoint(g_btn_rect_v, local)) return v;
    return nil;
}
@end

// ---------------- scene-aware creation ----------------
static UIWindow *g_win = nil;

static UIWindowScene *find_scene(void) {
    for (UIScene *s in [UIApplication sharedApplication].connectedScenes) {
        if (s.activationState == UISceneActivationStateForegroundActive &&
            [s isKindOfClass:[UIWindowScene class]])
            return (UIWindowScene *)s;
    }
    return nil;
}

static void try_create(void) {
    if (g_initialized) return;

    UIWindowScene *scene = find_scene();
    if (!scene) return;

    static bool logged = false;
    if (!logged) { logged = true; mlog("scene found, creating overlay"); }

    g_dev = MTLCreateSystemDefaultDevice();
    if (!g_dev) { mlog("ERROR: no Metal device"); return; }
    g_queue = [g_dev newCommandQueue];

    g_win = [[UIWindow alloc] initWithWindowScene:scene];
    g_win.windowLevel = UIWindowLevelAlert + 100.0;
    g_win.opaque = NO;
    g_win.backgroundColor = [UIColor clearColor];
    g_win.userInteractionEnabled = YES;
    g_win.rootViewController = [UIViewController new];
    g_win.rootViewController.view.backgroundColor = [UIColor clearColor];

    // diagnostic #1: plain UIView red square — no Metal involved
    UIView *redSquare = [[UIView alloc] initWithFrame:CGRectMake(30, 30, 20, 20)];
    redSquare.backgroundColor = [UIColor redColor];
    redSquare.userInteractionEnabled = NO;

    // manual Metal view (landscape space, rotated)
    ESPMetalView *v = [[ESPMetalView alloc] initWithFrame:CGRectMake(0, 0, GAME_W, GAME_H)];
    [v configure:g_dev];

    g_win.rootViewController.view = v;
    [g_win.rootViewController.view addSubview:redSquare];  // sits above Metal view

    // ImGui context + backend
    IMGUI_CHECKVERSION();
    g_imgui = ImGui::CreateContext();
    ImGui::GetIO().IniFilename = nullptr;
    ImGui::StyleColorsDark();
    ImGui_ImplMetal_Init(g_dev);

    UIScreen *scr = scene.screen;
    v.center = CGPointMake(scr.bounds.size.width * 0.5f, scr.bounds.size.height * 0.5f);
    v.transform = CGAffineTransformMakeRotation(M_PI_2);

    g_win.hidden = NO;
    objc_setAssociatedObject(g_win, "keep", g_win, OBJC_ASSOCIATION_RETAIN);
    objc_setAssociatedObject(redSquare, "keep", redSquare, OBJC_ASSOCIATION_RETAIN);

    // drive rendering with CADisplayLink (main thread, 30fps)
    CADisplayLink *dl = [CADisplayLink
        displayLinkWithTarget:v selector:@selector(drawFrame)];
    dl.preferredFramesPerSecond = 30;
    [dl addToRunLoop:[NSRunLoop mainRunLoop] forMode:NSRunLoopCommonModes];
    objc_setAssociatedObject(v, "dl", dl, OBJC_ASSOCIATION_RETAIN);

    g_initialized = true;
    mlog("overlay up (manual metal + display link)");
}

static void create_loop(void) {
    if (g_initialized) return;
    dispatch_async(dispatch_get_main_queue(), ^{ try_create(); });
    static int attempts = 0;
    attempts++;
    if (attempts == 3 || attempts == 30 || attempts == 150)
        mlog("still hunting scene (attempt %d)...", attempts);
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(2 * NSEC_PER_SEC)),
                   dispatch_get_global_queue(QOS_CLASS_UTILITY, 0), ^{ create_loop(); });
}

__attribute__((constructor))
static void mlb_inject_ctor(void) {
    mlog("=== ctor fired, dylib loaded ===");
    create_loop();
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_UTILITY, 0), ^{
        sleep(3);
        worker_loop();
    });
}
