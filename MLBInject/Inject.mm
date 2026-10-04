// MLBInject — internal ESP for MLBB (arm64, injected via ElleKit/TrollFools)
// v18: FULL AUTO-CALIBRATION. Evidence: both matrix storage interpretations
// produced degenerate projections (v15 ny~2.6 pinned, v16 x~-5.24 pinned) —
// the get_main pointer may be a Moonton WRAPPER, not the raw Camera. So:
//   - self candidates: get_main ptr AND *(void**)ptr (wrapper->real camera)
//   - storage layout auto-detected per candidate (bottom-row 0,0,0,1 test)
//   - both multiply orders scored
//   - 8 combos graded per tick by live on-screen count; clear winner locks
//   - raw matrix floats dumped to log once per candidate (ground truth)
// Local hero via BattleManager+0x50 (m_LocalPlayerShow, runtime-validated)
// -> CYAN box; snaplines local hero -> enemy box CENTERS. Carried: landscape
// gate + resync, non-key window, dead=hp-only, e0 status.
//
// Data offsets (verified via iGODGame disassembly):
//   BM class slot 0x7BFBF70 / statics 0xA8 / Instance 0x0  <- get_battleManager
//   Hp 0x1AC / HpMax 0x1B0  <- get_m_HpPer
//   CanSight 0x254          <- get_m_CanSight
//   Pos A 0x1D0 / Pos B 0x298 <- get_Position tail paths (B verified live)
//   Local player: BM+0x50 (m_LocalPlayerShow — runtime-validated)
//   List: auto-probe (locks BM+0x78 m_ShowPlayers)

#import <UIKit/UIKit.h>
#import <Metal/Metal.h>
#import <QuartzCore/CAMetalLayer.h>
#import <objc/runtime.h>
#import <os/lock.h>
#import <mach/mach.h>
#import <mach-o/dyld.h>
#import <dlfcn.h>
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
#define OFF_BM_LOCALSHOW     0x50

#define HERO_H               2.2f
#define MAX_ENTS             64

static float g_screen_w = 667.0f;
static float g_screen_h = 375.0f;

static UIWindowScene *find_scene(void);

// ---------------- shared frame (worker -> renderer) ----------------
typedef struct {
    float wx, wy, wz;
    int32_t hp, hpmax, visible, dead;
} EspEnt;

typedef struct {
    uint32_t entity_count, pos_sel;
    int32_t  local_ok;
    float    lwx, lwy, lwz;
    char     status[192];
    EspEnt   ents[MAX_ENTS];
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

// ---------------- resolve / walk state ----------------
static uint64_t g_uf = 0;
static int      g_list_off = -1;
static int      g_pos_sel = 1;

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

// ---------------- worker thread (data only — no Unity calls here) --------
static void worker_loop(void) {
    static float prev_a[MAX_ENTS][3], prev_b[MAX_ENTS][3];
    static int prev_n = 0;
    static uint64_t probe_bm = 0;
    static bool probe_logged = false, probe_fail_logged = false;

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
            g_list_off = -1; g_kcache_n = 0;
            g_pos_sel = 1; g_uf = 0;
            sleep(1); continue;
        }
        uint64_t statics = rd64(klass + OFF_CLASS_STATICS);
        uint64_t bm = statics ? rd64(statics + OFF_STATICS_INSTANCE) : 0;
        if (!bm) {
            EspFrame f; memset(&f, 0, sizeof f);
            snprintf(f.status, sizeof f.status, "lobby (no battle instance)");
            os_unfair_lock_lock(&g_lock); g_frame = f; os_unfair_lock_unlock(&g_lock);
            g_list_off = -1; g_kcache_n = 0; g_pos_sel = 1;
            usleep(500000); continue;
        }
        if (g_list_off < 0) {
            g_list_off = discover_list(bm);
            if (g_list_off < 0) {
                EspFrame f; memset(&f, 0, sizeof f);
                snprintf(f.status, sizeof f.status, "list not found yet (enter a match)");
                os_unfair_lock_lock(&g_lock); g_frame = f; os_unfair_lock_unlock(&g_lock);
                usleep(500000); continue;
            }
        }
        if (probe_bm != bm) { probe_bm = bm; probe_logged = false; probe_fail_logged = false; }

        uint64_t lst = rd64(bm + g_list_off);
        uint64_t arr = lst ? rd64(lst + 0x10) : 0;
        int32_t  size = lst ? rdi32(lst + 0x18) : 0;
        if (!arr || size < 1 || size > 512) { g_list_off = -1; continue; }

        int count = 0;
        float move_a = 0, move_b = 0;
        EspFrame f;
        memset(&f, 0, sizeof f);

        for (int32_t i = 0; i < size && count < MAX_ENTS; i++) {
            uint64_t e = rd64(arr + 0x20 + 8ull * (uint64_t)i);
            if (!e || !is_hero_obj(e)) continue;

            float pa[3] = {0}, pb[3] = {0};
            if (!rd_vec3(e + OFF_ENT_POS_A, pa)) continue;
            if (!rd_vec3(e + OFF_ENT_POS_B, pb)) continue;

            if (count < prev_n) {
                move_a += fabsf(pa[0]-prev_a[count][0]) + fabsf(pa[2]-prev_a[count][2]);
                move_b += fabsf(pb[0]-prev_b[count][0]) + fabsf(pb[2]-prev_b[count][2]);
            }
            memcpy(prev_a[count], pa, 12);
            memcpy(prev_b[count], pb, 12);

            EspEnt *en = &f.ents[count];
            en->wx = (g_pos_sel == 0) ? pa[0] : pb[0];
            en->wy = (g_pos_sel == 0) ? pa[1] : pb[1];
            en->wz = (g_pos_sel == 0) ? pa[2] : pb[2];
            en->hp      = rdi32(e + OFF_ENT_HP);
            en->hpmax   = rdi32(e + OFF_ENT_HPMAX);
            en->visible = rdi32(e + OFF_ENT_CANSIGHT);
            en->dead    = (en->hp <= 0);

            count++;
        }
        prev_n = count;

        // local player probe: BM+0x50 = m_LocalPlayerShow (validated)
        f.local_ok = 0;
        uint64_t lshow = rd64(bm + OFF_BM_LOCALSHOW);
        if (lshow && is_hero_obj(lshow)) {
            float la[3] = {0}, lb[3] = {0};
            if (rd_vec3(lshow + OFF_ENT_POS_A, la) && rd_vec3(lshow + OFF_ENT_POS_B, lb)) {
                f.lwx = (g_pos_sel == 0) ? la[0] : lb[0];
                f.lwy = (g_pos_sel == 0) ? la[1] : lb[1];
                f.lwz = (g_pos_sel == 0) ? la[2] : lb[2];
                f.local_ok = 1;
                if (!probe_logged) {
                    probe_logged = true;
                    mlog("local player via BM+0x50: ShowPlayer @ 0x%llx",
                         (unsigned long long)lshow);
                }
            }
        }
        if (!f.local_ok && !probe_fail_logged && count > 0) {
            probe_fail_logged = true;
            mlog("BM+0x50 probe failed (ptr=%llx) — center heuristic fallback",
                 (unsigned long long)lshow);
        }

        if (move_a < 0.01f && move_b > 0.5f && g_pos_sel == 0) {
            g_pos_sel = 1;
            mlog("auto-flip A->B (A frozen)");
        } else if (move_b < 0.01f && move_a > 0.5f && g_pos_sel == 1) {
            g_pos_sel = 0;
            mlog("auto-flip B->A (B frozen)");
        }

        f.pos_sel = (uint32_t)g_pos_sel;
        f.entity_count = count;
        snprintf(f.status, sizeof f.status, "ents=%d pos=%c", count, g_pos_sel ? 'B' : 'A');

        os_unfair_lock_lock(&g_lock);
        g_frame = f;
        os_unfair_lock_unlock(&g_lock);

        usleep(100000);
    }
}

// ---------------- il2cpp metadata bridge (zero RVA) ----------------
typedef void*       Il2CppDomain;
typedef void*       Il2CppAssembly;
typedef void*       Il2CppImage;
typedef void*       Il2CppClass;
typedef void        MethodInfo;      // opaque — we hold MethodInfo*

typedef Il2CppDomain (*fn_domain_get)(void);
typedef void**       (*fn_domain_get_assemblies)(Il2CppDomain, size_t*);
typedef Il2CppImage  (*fn_assembly_get_image)(Il2CppAssembly);
typedef Il2CppClass  (*fn_class_from_name)(Il2CppImage, const char*, const char*);
typedef MethodInfo*  (*fn_class_get_method)(Il2CppClass, const char*, int);
typedef void*        (*fn_runtime_invoke)(MethodInfo*, void*, void**, void**);

static fn_domain_get            p_domain_get;
static fn_domain_get_assemblies p_domain_get_assemblies;
static fn_assembly_get_image    p_assembly_get_image;
static fn_class_from_name       p_class_from_name;
static fn_class_get_method      p_class_get_method_from_name;
static fn_runtime_invoke        p_runtime_invoke;

static bool        g_il2cpp_ok = false;
static MethodInfo *g_mi_main  = nullptr;
static MethodInfo *g_mi_w2cm  = nullptr;
static MethodInfo *g_mi_proj  = nullptr;
static MethodInfo *g_mi_scr_w = nullptr;
static MethodInfo *g_mi_scr_h = nullptr;
static void*       g_cam = nullptr;
static void*       g_last_cam = nullptr;
static int         g_cam_stable = 0;

struct V3 { float x, y, z; };

static bool il2cpp_bridge_init(void) {
    p_domain_get                 = (fn_domain_get)dlsym(RTLD_DEFAULT, "il2cpp_domain_get");
    p_domain_get_assemblies      = (fn_domain_get_assemblies)dlsym(RTLD_DEFAULT, "il2cpp_domain_get_assemblies");
    p_assembly_get_image         = (fn_assembly_get_image)dlsym(RTLD_DEFAULT, "il2cpp_assembly_get_image");
    p_class_from_name            = (fn_class_from_name)dlsym(RTLD_DEFAULT, "il2cpp_class_from_name");
    p_class_get_method_from_name = (fn_class_get_method)dlsym(RTLD_DEFAULT, "il2cpp_class_get_method_from_name");
    p_runtime_invoke             = (fn_runtime_invoke)dlsym(RTLD_DEFAULT, "il2cpp_runtime_invoke");

    if (!p_domain_get || !p_domain_get_assemblies || !p_assembly_get_image ||
        !p_class_from_name || !p_class_get_method_from_name || !p_runtime_invoke) {
        mlog("il2cpp API: dlsym failed");
        return false;
    }
    mlog("il2cpp API: dlsym OK");

    Il2CppDomain dom = p_domain_get();
    if (!dom) { mlog("il2cpp: domain null"); return false; }

    size_t nasm = 0;
    void **asms = p_domain_get_assemblies(dom, &nasm);
    if (!asms || !nasm) { mlog("il2cpp: no assemblies"); return false; }
    mlog("il2cpp: %zu assemblies", nasm);

    Il2CppClass camKlass = nullptr, scrKlass = nullptr;
    for (size_t i = 0; i < nasm && (!camKlass || !scrKlass); i++) {
        Il2CppImage img = p_assembly_get_image(asms[i]);
        if (!img) continue;
        if (!camKlass) camKlass = p_class_from_name(img, "UnityEngine", "Camera");
        if (!scrKlass) scrKlass = p_class_from_name(img, "UnityEngine", "Screen");
    }
    if (!camKlass) { mlog("il2cpp: Camera not found"); return false; }
    mlog("il2cpp: Camera @ %p  Screen @ %p", camKlass, scrKlass);

    g_mi_main = p_class_get_method_from_name(camKlass, "get_main", 0);
    g_mi_w2cm = p_class_get_method_from_name(camKlass, "get_worldToCameraMatrix", 0);
    g_mi_proj = p_class_get_method_from_name(camKlass, "get_projectionMatrix", 0);
    mlog("il2cpp: main=%p w2cm=%p proj=%p",
         (void*)g_mi_main, (void*)g_mi_w2cm, (void*)g_mi_proj);
    if (!g_mi_main || !g_mi_w2cm || !g_mi_proj) {
        mlog("il2cpp: camera methods missing");
        return false;
    }

    if (scrKlass) {
        g_mi_scr_w = p_class_get_method_from_name(scrKlass, "get_width", 0);
        g_mi_scr_h = p_class_get_method_from_name(scrKlass, "get_height", 0);
    }
    mlog("il2cpp: Screen w/h = %p/%p", (void*)g_mi_scr_w, (void*)g_mi_scr_h);
    return true;
}

static void *mi_fn(MethodInfo *mi) {
    if (!mi) return nullptr;
    return *(void **)mi;
}

static void* cam_get_main(void) {
    void *fn = mi_fn(g_mi_main);
    if (!fn) return nullptr;
    return ((void *(*)(MethodInfo *))fn)(g_mi_main);
}

// runtime_invoke boxes value-type returns — Matrix4x4 box data at +0x10
static bool invoke_mat4(MethodInfo *mi, void *self, float out[16]) {
    void *fn = mi_fn(mi);
    if (!fn || !p_runtime_invoke) return false;
    void *exc = nullptr;
    void *boxed = p_runtime_invoke(mi, self, nullptr, &exc);
    if (!boxed || exc) return false;
    return rd((uint64_t)boxed + 0x10, out, 64);
}

static int32_t screen_get_w(void) {
    void *fn = mi_fn(g_mi_scr_w);
    if (!fn) return 0;
    return ((int32_t(*)(MethodInfo *))fn)(g_mi_scr_w);
}
static int32_t screen_get_h(void) {
    void *fn = mi_fn(g_mi_scr_h);
    if (!fn) return 0;
    return ((int32_t(*)(MethodInfo *))fn)(g_mi_scr_h);
}

// ---------------- matrix math, BOTH storage layouts ----------------
// row-major storage: m[r*4+c]
static void mat_vec_rm(const float m[16], const V3 &v, float w, float out[4]) {
    for (int r = 0; r < 4; r++)
        out[r] = m[r*4+0]*v.x + m[r*4+1]*v.y + m[r*4+2]*v.z + m[r*4+3]*w;
}
static void mat_mul_rm(float out[16], const float a[16], const float b[16]) {
    for (int r = 0; r < 4; r++)
        for (int c = 0; c < 4; c++) {
            float s = 0;
            for (int k = 0; k < 4; k++) s += a[r*4+k] * b[k*4+c];
            out[r*4+c] = s;
        }
}
// column-major storage: m[c*4+r]
static void mat_vec_cm(const float m[16], const V3 &v, float w, float out[4]) {
    for (int r = 0; r < 4; r++)
        out[r] = m[0*4+r]*v.x + m[1*4+r]*v.y + m[2*4+r]*v.z + m[3*4+r]*w;
}
static void mat_mul_cm(float out[16], const float a[16], const float b[16]) {
    for (int c = 0; c < 4; c++)
        for (int r = 0; r < 4; r++) {
            float s = 0;
            for (int k = 0; k < 4; k++) s += a[k*4+r] * b[c*4+k];
            out[c*4+r] = s;
        }
}
static void mat_vec_by(const float m[16], int layout, const V3 &v, float w, float out[4]) {
    if (layout == 1) mat_vec_rm(m, v, w, out);
    else             mat_vec_cm(m, v, w, out);
}
static void mat_mul_by(float out[16], const float a[16], const float b[16], int layout, int order) {
    if (layout == 1) { if (order == 0) mat_mul_rm(out, a, b); else mat_mul_rm(out, b, a); }
    else             { if (order == 0) mat_mul_cm(out, a, b); else mat_mul_cm(out, b, a); }
}

// ---------------- config (in-memory) ----------------
struct EspCfg {
    bool esp_on, boxes, hp_bars, snaplines, vision_only, status_text;
};
static EspCfg g_cfg = { true, true, true, true, false, true };

// ---------------- overlay state ----------------
static bool   g_menu_open = false;
static bool   g_initialized = false;
static bool   g_logged_first_frame = false;
static CGRect g_btn_rect_v = CGRectMake(611.0f, 8, 48, 48);
static id<MTLDevice>        g_dev = nil;
static id<MTLCommandQueue>  g_queue = nil;
static ImGuiContext        *g_imgui = nil;

static void feed_touch(UITouch *t, UIView *v, bool down, bool ended) {
    ImGuiIO &io = ImGui::GetIO();
    CGPoint p = [v convertPoint:[t locationInView:v] fromView:v];
    io.AddMousePosEvent(p.x, p.y);
    io.AddMouseButtonEvent(0, down && !ended);
}

// ---------------- MANUAL Metal view ----------------
@interface ESPMetalView : UIView
@end

@implementation ESPMetalView
+ (Class)layerClass { return [CAMetalLayer class]; }

- (CAMetalLayer *)mlayer { return (CAMetalLayer *)self.layer; }

- (void)configure:(id<MTLDevice>)dev {
    CAMetalLayer *l = self.mlayer;
    l.device = dev;
    l.pixelFormat = MTLPixelFormatBGRA8Unorm;
    l.opaque = NO;
    l.backgroundColor = NULL;
    l.framebufferOnly = YES;
    l.presentsWithTransaction = NO;
    l.maximumDrawableCount = 3;
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
    if (!g_initialized || !g_uf) return;

    // orientation re-sync (~2x/sec)
    static int _sync = 0;
    if ((++_sync % 15) == 0) {
        UIWindowScene *scn = find_scene();
        if (scn) {
            CGRect sb = scn.screen.bounds;
            if (std::abs((double)sb.size.width  - (double)self.bounds.size.width)  > 0.5 ||
                std::abs((double)sb.size.height - (double)self.bounds.size.height) > 0.5) {
                self.frame = CGRectMake(0, 0, sb.size.width, sb.size.height);
                g_screen_w = (float)sb.size.width;
                g_screen_h = (float)sb.size.height;
                [self syncSize];
                mlog("resync view -> %.0fx%.0f", sb.size.width, sb.size.height);
            }
        }
    }

    [self syncSize];

    CAMetalLayer *l = self.mlayer;
    id<CAMetalDrawable> d = [l nextDrawable];
    if (!d) { static int ndl=0; if(++ndl==60) mlog("nextDrawable nil x60"); return; }

    MTLRenderPassDescriptor *rp = [MTLRenderPassDescriptor renderPassDescriptor];
    rp.colorAttachments[0].texture = d.texture;
    rp.colorAttachments[0].loadAction = MTLLoadActionClear;
    rp.colorAttachments[0].storeAction = MTLStoreActionStore;
    rp.colorAttachments[0].clearColor = MTLClearColorMake(0, 0, 0, 0);

    if (!g_logged_first_frame) {
        g_logged_first_frame = true;
        mlog("first frame view=%.0fx%.0f window=%.0fx%.0f",
             self.bounds.size.width, self.bounds.size.height,
             self.window.bounds.size.width, self.window.bounds.size.height);
    }

    static bool bridged = false;
    if (!bridged) {
        bridged = true;
        g_il2cpp_ok = il2cpp_bridge_init();
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

    // ---- camera: refresh every frame while battle live, 3-frame stability ----
    bool battle_live = g_il2cpp_ok && f.entity_count > 0;
    if (battle_live) {
        void *c = cam_get_main();
        if (c && c == g_last_cam) { if (g_cam_stable < 3) g_cam_stable++; }
        else g_cam_stable = 0;
        g_last_cam = c;
        if (c != g_cam) { g_cam = c; mlog("camera = %p", c); }
    } else {
        g_cam = nullptr; g_cam_stable = 0;
    }
    bool cam_ok = battle_live && g_cam && g_cam_stable >= 3;

    // ---- Unity screen size (measured) ----
    static float su_w = 0, su_h = 0;
    static int   su_tick = 0;
    if (cam_ok && (++su_tick % 60) == 1) {
        int w = screen_get_w(), h = screen_get_h();
        if (w > 0 && h > 0) { su_w = (float)w; su_h = (float)h; }
    }
    if (cam_ok && su_w <= 0) {
        su_w = (float)l.drawableSize.width;
        su_h = (float)l.drawableSize.height;
    }
    float mx = su_w > 0 ? g_screen_w / su_w : 1.0f;
    float my = su_h > 0 ? g_screen_h / su_h : 1.0f;

    // ================= CAMERA SELF CANDIDATES =================
    // get_main may return a Moonton wrapper — candidate 0 = as-is,
    // candidate 1 = *(void**)ptr (wrapper -> real camera)
    void *cands[2] = { g_cam, nullptr };
    int   ncand = 1;
    if (cam_ok) {
        void *inner = nullptr;
        rd((uint64_t)g_cam, &inner, sizeof(inner));
        if (inner && inner != g_cam) cands[ncand++] = inner;
    }

    static float    cV[2][16], cP[2][16];
    static bool     cOK[2]  = { false, false };
    static int      cLayout[2] = { -1, -1 };
    static void*    cSeen[2]   = { nullptr, nullptr };

    for (int ci = 0; ci < ncand; ci++) {
        cOK[ci] = invoke_mat4(g_mi_w2cm, cands[ci], cV[ci]) &&
                  invoke_mat4(g_mi_proj,  cands[ci], cP[ci]);
        if (cOK[ci] && cSeen[ci] != cands[ci]) {
            cSeen[ci] = cands[ci];
            // storage-layout detection: the view matrix bottom row must be
            // (0,0,0,1) in the TRUE orientation
            float eCol = fabsf(cV[ci][3]) + fabsf(cV[ci][7]) + fabsf(cV[ci][11]) +
                         fabsf(cV[ci][15] - 1.0f);
            float eRow = fabsf(cV[ci][12]) + fabsf(cV[ci][13]) + fabsf(cV[ci][14]) +
                         fabsf(cV[ci][15] - 1.0f);
            cLayout[ci] = (eRow <= eCol) ? 1 : 0;
            mlog("cand%d self=%p layout=%s (errCol=%.4f errRow=%.4f)",
                 ci, cands[ci], cLayout[ci] ? "row" : "col", eCol, eRow);
            mlog("cand%d V = %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f",
                 ci, cV[ci][0], cV[ci][1], cV[ci][2], cV[ci][3],
                 cV[ci][4], cV[ci][5], cV[ci][6], cV[ci][7],
                 cV[ci][8], cV[ci][9], cV[ci][10], cV[ci][11],
                 cV[ci][12], cV[ci][13], cV[ci][14], cV[ci][15]);
        }
    }

    // ================= COMBO CALIBRATION (ci x layout x order) =================
    // 8 combos scored per tick by on-screen count of ALIVE entities.
    // Lock: >=4 on-screen AND beats runner-up by >=2, 2 consecutive ticks.
    struct Draw { float sx, sy, bh, bw; int hp, hpmax; bool ok; };
    static Draw draws[MAX_ENTS];
    int nd = 0, valid = 0;

    static int  lock_ci = -1, lock_layout = -1, lock_order = -1;
    static void *lock_self = nullptr;
    static int   lock_good = 0;
    static int   calib_dbg = 0;

    bool haveVP = false;
    float VP[16];

    if (cam_ok && ncand > 0) {
        // resolve locked candidate index
        if (lock_ci >= 0) {
            bool found = false;
            for (int ci = 0; ci < ncand; ci++)
                if (cands[ci] == lock_self) { lock_ci = ci; found = true; break; }
            if (!found) {
                mlog("lock reset: camera candidate gone");
                lock_ci = -1; lock_self = nullptr; lock_good = 0;
            }
        }

        if (lock_ci >= 0 && cOK[lock_ci] && cLayout[lock_ci] >= 0) {
            mat_mul_by(VP, cP[lock_ci], cV[lock_ci], lock_layout, lock_order);
            haveVP = true;
        } else if (f.entity_count >= 5) {
            // score all combos
            int score[8] = {0,0,0,0,0,0,0,0};
            V3  dbg[8];
            float dbgW[8];
            bool  got[8];
            for (int k = 0; k < 8; k++) { dbg[k] = {0,0,0}; dbgW[k] = 0; got[k] = false; }

            for (int ci = 0; ci < ncand; ci++) {
                if (!cOK[ci] || cLayout[ci] < 0) continue;
                for (int layout = 0; layout < 2; layout++) {
                    for (int order = 0; order < 2; order++) {
                        float vp[16];
                        mat_mul_by(vp, cP[ci], cV[ci], layout, order);
                        int id = ci*4 + layout*2 + order;
                        int on = 0;
                        for (uint32_t i = 0; i < f.entity_count && i < MAX_ENTS; i++) {
                            EspEnt &e = f.ents[i];
                            if (e.dead || e.hpmax <= 0 || e.hp > e.hpmax*4) continue;
                            float o[4];
                            mat_vec_by(vp, layout, {e.wx, e.wy, e.wz}, 1.0f, o);
                            if (o[3] <= 0.001f) continue;
                            float nx = o[0]/o[3], ny = o[1]/o[3];
                            if (!(fabsf(nx) < 10 && fabsf(ny) < 10)) continue;
                            if (!got[id]) { dbg[id] = {nx, ny, o[2]}; dbgW[id] = o[3]; got[id] = true; }
                            float sfx = (nx*0.5f + 0.5f) * su_w * mx;
                            float sfy = (1.0f - (ny*0.5f + 0.5f)) * su_h * my;
                            if (sfx >= 0 && sfx <= g_screen_w && sfy >= 0 && sfy <= g_screen_h)
                                on++;
                        }
                        score[id] = on;
                    }
                }
            }
            int best = -1, bestOn = -1, second = -1;
            for (int k = 0; k < 8; k++) {
                if (score[k] > bestOn) { second = bestOn; bestOn = score[k]; best = k; }
                else if (score[k] > second) second = score[k];
            }
            if (++calib_dbg % 20 == 1) {
                mlog("calib scores: c0[l%d%d%d%d] c1[l%d%d%d%d] best=%d",
                     score[0], score[1], score[2], score[3],
                     score[4], score[5], score[6], score[7], bestOn);
                if (best >= 0 && got[best])
                    mlog("calib best combo %d raw ndc = %.3f,%.3f,%.3f w=%.3f",
                         best, dbg[best].x, dbg[best].y, dbg[best].z, dbgW[best]);
            }
            bool strong = (best >= 0) && (bestOn >= 4) && (bestOn >= second + 2);
            if (strong) {
                if (++lock_good >= 2) {
                    lock_ci      = best / 4;
                    lock_layout  = (best / 2) % 2;
                    lock_order   = best % 2;
                    lock_self    = cands[lock_ci];
                    mlog("COMBO LOCKED: cand=%d layout=%s order=%s (on=%d vs %d)",
                         lock_ci, lock_layout ? "row" : "col",
                         lock_order ? "V*P" : "P*V", bestOn, second);
                }
            } else lock_good = 0;
        }

        // project entities with the locked combo
        if (haveVP) {
            for (uint32_t i = 0; i < f.entity_count && i < MAX_ENTS; i++) {
                EspEnt &e = f.ents[i];
                Draw &dd = draws[nd];
                dd.sx = dd.sy = dd.bh = dd.bw = 0; dd.ok = false;
                dd.hp = e.hp; dd.hpmax = e.hpmax;

                float oF[4], oH[4];
                mat_vec_by(VP, lock_layout, {e.wx, e.wy, e.wz}, 1.0f, oF);
                mat_vec_by(VP, lock_layout, {e.wx, e.wy + HERO_H, e.wz}, 1.0f, oH);
                if (oF[3] > 0.001f && oH[3] > 0.001f) {
                    float sfx = (oF[0]/oF[3]*0.5f + 0.5f) * su_w * mx;
                    float sfy = (1.0f - (oF[1]/oF[3]*0.5f + 0.5f)) * su_h * my;
                    float shy = (1.0f - (oH[1]/oH[3]*0.5f + 0.5f)) * su_h * my;
                    float bh = fabsf(sfy - shy);
                    if (bh >= 2.0f && bh <= 2000.0f) {
                        dd.sx = sfx; dd.sy = sfy;
                        dd.bh = bh; dd.bw = bh * 0.55f;
                        dd.ok = true;
                        valid++;
                    }
                }
                if (!dd.ok && oF[3] > 0.001f) {
                    dd.sx = (oF[0]/oF[3]*0.5f + 0.5f) * su_w * mx;
                    dd.sy = (1.0f - (oF[1]/oF[3]*0.5f + 0.5f)) * su_h * my;
                }
                nd++;
            }
        }
    }

    // ---- local hero: PRIMARY = BM+0x50 projected; FALLBACK = center heuristic
    static float local_sx = 0, local_sy = 0, local_bh = 0;
    static bool  local_valid = false;
    static int   local_streak = 0;
    local_valid = false;
    if (haveVP && f.local_ok) {
        float oF[4], oH[4];
        mat_vec_by(VP, lock_layout, {f.lwx, f.lwy, f.lwz}, 1.0f, oF);
        mat_vec_by(VP, lock_layout, {f.lwx, f.lwy + HERO_H, f.lwz}, 1.0f, oH);
        if (oF[3] > 0.001f && oH[3] > 0.001f) {
            local_sx = (oF[0]/oF[3]*0.5f + 0.5f) * su_w * mx;
            local_sy = (1.0f - (oF[1]/oF[3]*0.5f + 0.5f)) * su_h * my;
            float shy = (1.0f - (oH[1]/oH[3]*0.5f + 0.5f)) * su_h * my;
            local_bh = fabsf(local_sy - shy);
            local_valid = (local_bh >= 2.0f && local_bh <= 2000.0f);
        }
    }
    if (!local_valid && haveVP) {
        int best = -1;
        float bestD = 1e9f;
        float cx = io.DisplaySize.x * 0.5f, cy = io.DisplaySize.y * 0.5f;
        for (int i = 0; i < nd; i++) {
            if (!draws[i].ok) continue;
            if (draws[i].hp <= 0 || draws[i].hpmax <= 0 ||
                draws[i].hp > draws[i].hpmax * 4) continue;
            float bcx = draws[i].sx;
            float bcy = draws[i].sy - draws[i].bh * 0.5f;
            float dd2 = (bcx-cx)*(bcx-cx) + (bcy-cy)*(bcy-cy);
            if (dd2 < bestD) { bestD = dd2; best = i; }
        }
        if (best >= 0 && bestD < 220.0f * 220.0f) {
            if (local_streak < 10) local_streak++;
            if (local_streak >= 5) {
                local_sx = draws[best].sx;
                local_sy = draws[best].sy - draws[best].bh * 0.5f;
                local_bh = draws[best].bh;
                local_valid = true;
            }
        } else {
            local_streak = 0;
        }
    }

    ImDrawList *dl = ImGui::GetBackgroundDrawList();

    if (g_cfg.esp_on && haveVP) {
        const ImU32 col_box   = IM_COL32(255, 165, 0, 255);   // orange
        const ImU32 col_line  = IM_COL32(255, 165, 0, 180);
        const ImU32 col_hpbg  = IM_COL32(0, 0, 0, 180);
        const ImU32 col_hp    = IM_COL32(80, 220, 60, 255);
        const ImU32 col_local = IM_COL32(0, 220, 255, 255);   // cyan = YOU

        // entity boxes
        for (int i = 0; i < nd; i++) {
            const Draw &dd = draws[i];
            if (dd.hp <= 0 || !dd.ok) continue;

            float h = dd.bh, w = dd.bw;
            float x0 = dd.sx - w * 0.5f, y0 = dd.sy - h;
            float x1 = dd.sx + w * 0.5f, y1 = dd.sy;

            if (g_cfg.boxes)
                dl->AddRect(ImVec2(x0, y0), ImVec2(x1, y1), col_box, 0.0f, 0, 2.0f);

            if (g_cfg.hp_bars && dd.hpmax > 0) {
                float pct = (float)dd.hp / (float)dd.hpmax;
                if (pct < 0) pct = 0; if (pct > 1) pct = 1;
                float bx = x0 - 7.0f;
                dl->AddRectFilled(ImVec2(bx - 1, y0 - 1), ImVec2(bx + 4, y1 + 1), col_hpbg);
                dl->AddRectFilled(ImVec2(bx, y1 - (y1 - y0) * pct), ImVec2(bx + 3, y1), col_hp);
            }
        }

        // YOUR hero: cyan box
        if (local_valid && local_bh >= 2.0f) {
            float w = local_bh * 0.55f, h = local_bh;
            float x0 = local_sx - w * 0.5f, y0 = local_sy - h;
            float x1 = local_sx + w * 0.5f, y1 = local_sy;
            dl->AddRect(ImVec2(x0, y0), ImVec2(x1, y1), col_local, 0.0f, 0, 2.0f);
        }

        // snaplines: YOUR hero -> box centers
        if (g_cfg.snaplines && local_valid) {
            for (int i = 0; i < nd; i++) {
                const Draw &dd = draws[i];
                if (dd.hp <= 0 || !dd.ok) continue;
                dl->AddLine(ImVec2(local_sx, local_sy),
                            ImVec2(dd.sx, dd.sy - dd.bh * 0.5f), col_line, 1.2f);
            }
        }
    }

    // toggle button
    ImGui::SetNextWindowPos(ImVec2(io.DisplaySize.x - 56, 8));
    ImGui::PushStyleColor(ImGuiCol_WindowBg, 0);
    ImGui::Begin("##btn", nullptr, ImGuiWindowFlags_NoDecoration | ImGuiWindowFlags_NoMove |
                 ImGuiWindowFlags_NoNav | ImGuiWindowFlags_NoBackground |
                 ImGuiWindowFlags_AlwaysAutoResize | ImGuiWindowFlags_NoBringToFrontOnFocus);
    ImGui::InvisibleButton("btn", ImVec2(40, 40));
    if (ImGui::IsItemClicked()) g_menu_open = !g_menu_open;
    {
        ImVec2 mn = ImGui::GetItemRectMin(), mx2 = ImGui::GetItemRectMax();
        ImVec2 cc((mn.x + mx2.x) * 0.5f, (mn.y + mx2.y) * 0.5f);
        dl->AddCircleFilled(cc, 17.0f, g_menu_open ? IM_COL32(0,200,255,220) : IM_COL32(255,255,255,160));
        dl->AddCircle(cc, 17.0f, IM_COL32(0,0,0,255), 0, 2.0f);
    }
    ImGui::End();
    ImGui::PopStyleColor();
    g_btn_rect_v = CGRectMake(io.DisplaySize.x - 56, 8, 48, 48);

    if (g_cfg.status_text) {
        char st[224];
        snprintf(st, sizeof st,
                 "ents=%u dr=%d pos=%c cam=%s shp=%s su=%.0fx%.0f loc=%s | e0 w=%.1f,%.1f,%.1f",
                 f.entity_count, valid, f.pos_sel ? 'B' : 'A',
                 cam_ok ? "ok" : "wait",
                 haveVP ? "lock" : "cal",
                 su_w, su_h,
                 f.local_ok ? "ptr" : (local_valid ? "heu" : "no"),
                 f.entity_count ? f.ents[0].wx : 0.f,
                 f.entity_count ? f.ents[0].wy : 0.f,
                 f.entity_count ? f.ents[0].wz : 0.f);
        dl->AddText(ImVec2(8, 30), IM_COL32(0, 220, 255, 255), st);
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
- (BOOL)canBecomeKeyWindow { return NO; }

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

    CGRect sb = scene.screen.bounds;
    if (sb.size.width < sb.size.height) {
        static bool logged_wait = false;
        if (!logged_wait) { logged_wait = true; mlog("waiting for landscape orientation..."); }
        return;
    }

    static bool logged = false;
    if (!logged) { logged = true; mlog("scene found (landscape), creating overlay"); }

    g_dev = MTLCreateSystemDefaultDevice();
    if (!g_dev) { mlog("ERROR: no Metal device"); return; }
    g_queue = [g_dev newCommandQueue];

    g_win = [[ESPWindow alloc] initWithWindowScene:scene];
    g_win.windowLevel = UIWindowLevelAlert + 100.0;
    g_win.opaque = NO;
    g_win.backgroundColor = [UIColor clearColor];
    g_win.userInteractionEnabled = YES;
    g_win.rootViewController = [UIViewController new];
    g_win.rootViewController.view.backgroundColor = [UIColor clearColor];

    g_screen_w = (float)sb.size.width;
    g_screen_h = (float)sb.size.height;
    mlog("screen pts: %.0f x %.0f", g_screen_w, g_screen_h);

    ESPMetalView *v = [[ESPMetalView alloc] initWithFrame:sb];
    [v configure:g_dev];

    g_win.rootViewController.view = v;

    IMGUI_CHECKVERSION();
    g_imgui = ImGui::CreateContext();
    ImGui::GetIO().IniFilename = nullptr;
    ImGui::StyleColorsDark();
    ImGui_ImplMetal_Init(g_dev);

    g_win.hidden = NO;
    objc_setAssociatedObject(g_win, "keep", g_win, OBJC_ASSOCIATION_RETAIN);

    CADisplayLink *dl = [CADisplayLink
        displayLinkWithTarget:v selector:@selector(drawFrame)];
    dl.preferredFramesPerSecond = 30;
    [dl addToRunLoop:[NSRunLoop mainRunLoop] forMode:NSRunLoopCommonModes];
    objc_setAssociatedObject(v, "dl", dl, OBJC_ASSOCIATION_RETAIN);

    g_initialized = true;
    mlog("overlay up (v18 full-calibration)");
}

static void create_loop(void) {
    if (g_initialized) return;
    dispatch_async(dispatch_get_main_queue(), ^{ try_create(); });
    static int attempts = 0;
    attempts++;
    if (attempts == 3 || attempts == 30 || attempts == 150)
        mlog("hunting scene/orientation (attempt %d)...", attempts);
    dispatch_after(dispatch_time(DISPATCH_TIME_NOW, (int64_t)(2 * NSEC_PER_SEC)),
                   dispatch_get_global_queue(QOS_CLASS_UTILITY, 0), ^{ create_loop(); });
}

__attribute__((constructor))
static void mlb_inject_ctor(void) {
    mlog("=== ctor fired: VERSION 18 BUILD (full-calibration) ===");
    create_loop();
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_UTILITY, 0), ^{
        sleep(3);
        worker_loop();
    });
}
