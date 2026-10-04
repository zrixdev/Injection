// MLBInject — internal ESP for MLBB (arm64, injected via ElleKit/TrollFools)
// v22: confirmation-gated matrix adoption + scan-both-positions + grid overlay.
//   MATRIX: candidates must pass strict scoring (>=70% ents, bh 15-400px)
//           on 3 CONSECUTIVE ticks with fresh positions each tick before
//           adoption. Engine rewrites true VP every frame, so the real
//           matrix keeps passing as heroes move; static garbage fails.
//   POS:    every candidate scored against BOTH pos A and pos B snap sets;
//           best combo adopted and pos selection locked from it.
//   GRID:   world-space grid on the y=0 plane — with a true matrix the grid
//           aligns with the map floor. Instant visual ground truth.
//   HERO_H: runtime slider (2-12) in menu — no rebuild to tune.
//   DUMP:   now logs BOTH world positions per entity.
//
// Carried: HERO_H default 4.5, VP slot cache, strict scorer, loose
// revalidation, local auto-probe (centrality lock), fallback snapline
// origin, PAGEZERO fix, pos_sel fix.

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
#define OFF_BM_LOCALSHOW     0x50

#define DEFAULT_HERO_H       4.5f
#define MAX_ENTS             64

static float g_screen_w = 667.0f;
static float g_screen_h = 375.0f;
static float g_hero_h   = DEFAULT_HERO_H;   // runtime-tunable

static UIWindowScene *find_scene(void);

// ---------------- shared frame (worker -> renderer) ----------------
typedef struct {
    float sx, sy, box_h, box_w;
    int32_t hp, hpmax, visible, dead;
} EspEnt;

typedef struct {
    uint32_t entity_count;
    uint32_t matrix_ok;
    int32_t  pos_sel;
    int32_t  pos_mode;
    int32_t  mat_score;
    int32_t  mat_state;               // 0=scan 1=confirming 2=ok
    int32_t  conf_step;               // confirmation progress
    int32_t  local_ok;
    int32_t  local_off;
    float    local_sx, local_sy, local_bh;
    int32_t  local_drawn;
    float    vp[16];                  // for grid overlay
    char     status[160];
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
static int      g_pos_mode = 0;          // 0=auto 1=A 2=B
static uint64_t g_last_vp_addr = 0;

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

// ---------------- projection ----------------
static float g_vp[16];
static bool  g_mat_ok = false;
static int   g_adopt_score = 0;

static bool project(float x, float y, float z, float *sx, float *sy, float *cw) {
    float cx = g_vp[0]*x + g_vp[4]*y + g_vp[8]*z  + g_vp[12];
    float cy = g_vp[1]*x + g_vp[5]*y + g_vp[9]*z  + g_vp[13];
    float w  = g_vp[3]*x + g_vp[7]*y + g_vp[11]*z + g_vp[15];
    *cw = w;
    if (w <= 0.001f) return false;
    *sx = (cx / w * 0.5f + 0.5f) * g_screen_w;
    *sy = (1.0f - (cy / w * 0.5f + 0.5f)) * g_screen_h;
    return true;
}

static float project_box(float x, float y, float z,
                         float *sx, float *sy, float *cw_out) {
    float sfx, sfy, shx, shy, cwf, cwh;
    if (!project(x, y, z, &sfx, &sfy, &cwf)) return 0;
    if (!project(x, y + g_hero_h, z, &shx, &shy, &cwh)) return 0;
    *sx = sfx; *sy = sfy;
    if (cw_out) *cw_out = cwf;
    float bh = fabsf(sfy - shy);
    if (bh < 2.0f || bh > 2000.0f) return 0;
    return bh;
}

// ---------------- matrix scanner ----------------
typedef struct Snap { float x, y, z; } Snap;

static int vp_score(const float m[16], const Snap *es, int n) {
    if (fabsf(m[0]) + fabsf(m[4]) + fabsf(m[8]) < 1e-4f) return -1;

    float save[16];
    memcpy(save, g_vp, sizeof(save));
    memcpy(g_vp, m, sizeof(save));

    int total = 0, on = 0;
    for (int i = 0; i < n; i++) {
        if (fabsf(es[i].x) > 300 || fabsf(es[i].z) > 300 ||
            es[i].y < -100 || es[i].y > 500) continue;
        float sx, sy, cw;
        float bh = project_box(es[i].x, es[i].y, es[i].z, &sx, &sy, &cw);
        total++;
        if (bh >= 15.0f && bh <= 400.0f &&
            sx >= -g_screen_w*0.1f && sx <= g_screen_w*1.1f &&
            sy >= -g_screen_h*0.2f && sy <= g_screen_h*1.2f)
            on++;
    }
    memcpy(g_vp, save, sizeof(save));
    return (total >= 3 && on * 10 >= total * 7) ? on : -1;
}

static bool vp_revalidate(const Snap *es, int n) {
    int total = 0, on = 0;
    for (int i = 0; i < n; i++) {
        if (fabsf(es[i].x) > 300 || fabsf(es[i].z) > 300 ||
            es[i].y < -100 || es[i].y > 500) continue;
        float sx, sy, cw;
        float bh = project_box(es[i].x, es[i].y, es[i].z, &sx, &sy, &cw);
        total++;
        if (bh >= 10.0f && bh <= 500.0f &&
            sx >= -g_screen_w*0.5f && sx <= g_screen_w*1.5f &&
            sy >= -g_screen_h*0.5f && sy <= g_screen_h*1.5f)
            on++;
    }
    return total >= 3 && on >= 2;
}

// candidate from a sweep — NOT adopted until confirmed
typedef struct {
    bool     valid;
    uint64_t addr;
    float    m[16];
    int      score;
    int      pos_sel;      // 0=A 1=B — which snap set won
} VpCand;

static VpCand   g_pending;
static int      g_conf_ticks = 0;

static float    g_best_vp[16];
static uint64_t g_best_addr = 0;
static int      g_best_score = 0;
static int      g_best_pos = 1;

static void scan_region_for_vp(uint64_t addr, uint64_t len,
                               const Snap *esA, int nA,
                               const Snap *esB, int nB) {
    static uint8_t buf[256 * 1024 + 64];
    const uint64_t chunk = 256 * 1024;
    for (uint64_t off = 0; off < len; off += chunk) {
        uint64_t want = chunk + 64;
        if (off + want > len) want = len - off;
        if (!rd(addr + off, buf, want)) continue;
        for (uint64_t o = 0; o + 64 <= chunk && off + o + 64 <= want; o += 16) {
            const float *m = (const float *)(buf + o);
            if (!(m[15] != 0.0f && (fabsf(m[3]) + fabsf(m[7]) + fabsf(m[11])) > 1e-6f))
                continue;
            bool finite = true;
            for (int i = 0; i < 16; i++)
                if (!(fabsf(m[i]) < 1e9f)) { finite = false; break; }
            if (!finite) continue;
            // v22: score against BOTH position sets, keep the better combo
            int sA = (g_pos_mode != 1) ? vp_score(m, esA, nA) : -1;
            int sB = (g_pos_mode != 2) ? vp_score(m, esB, nB) : -1;
            int sc; int psel;
            if (sA >= sB) { sc = sA; psel = 0; } else { sc = sB; psel = 1; }
            if (sc > g_best_score) {
                g_best_score = sc;
                memcpy(g_best_vp, m, sizeof(g_best_vp));
                g_best_addr = addr + off + o;
                g_best_pos  = psel;
                if (sc >= (nA > nB ? nA : nB)) return;   // perfect — stop
            }
        }
    }
}

static bool scan_matrix(const Snap *esA, int nA, const Snap *esB, int nB,
                        VpCand *out) {
    memset(out, 0, sizeof *out);

    // fast path: re-check last-known slot first (fresh read, both sets)
    if (g_last_vp_addr && g_pos_mode == 0) {
        float m[16];
        if (rd(g_last_vp_addr, m, sizeof m)) {
            int sA = vp_score(m, esA, nA);
            int sB = vp_score(m, esB, nB);
            int sc = (sA >= sB) ? sA : sB;
            if (sc >= g_adopt_score && sc > 0) {
                out->valid = true;
                out->addr = g_last_vp_addr;
                memcpy(out->m, m, sizeof out->m);
                out->score = sc;
                out->pos_sel = (sA >= sB) ? 0 : 1;
                return true;
            }
        }
    }

    static mach_vm_address_t cursor = 1;
    static bool wrapped = false;
    g_best_score = 0;

    uint64_t budget = 64ull * 1024 * 1024;
    while (budget > 0) {
        mach_vm_address_t addr = cursor;
        mach_vm_size_t size = 0;
        vm_region_basic_info_data_64_t info;
        mach_msg_type_number_t cnt = VM_REGION_BASIC_INFO_COUNT_64;
        mach_port_t obj = MACH_PORT_NULL;
        kern_return_t kr = mach_vm_region(mach_task_self(), &addr, &size,
                VM_REGION_BASIC_INFO_64, (vm_region_info_t)&info, &cnt, &obj);
        if (kr != KERN_SUCCESS) {
            if (!wrapped) { wrapped = true; cursor = 1; continue; }
            break;
        }
        if (obj) mach_port_deallocate(mach_task_self(), obj);
        cursor = addr + size;

        if ((info.protection & VM_PROT_READ) &&
            !(info.protection & VM_PROT_EXECUTE) &&
            size <= 512ull * 1024 * 1024) {
            scan_region_for_vp(addr, size, esA, nA, esB, nB);
            if (g_best_score >= (nA > nB ? nA : nB)) break;
        }
        budget = (size < budget) ? budget - size : 0;
    }

    if (g_best_score > 0) {
        out->valid = true;
        out->addr = g_best_addr;
        memcpy(out->m, g_best_vp, sizeof out->m);
        out->score = g_best_score;
        out->pos_sel = g_best_pos;
        cursor = g_best_addr + 64;
        wrapped = false;
        return true;
    }
    return false;
}

static void adopt_matrix(const VpCand *c) {
    memcpy(g_vp, c->m, sizeof g_vp);
    g_last_vp_addr = c->addr;
    g_adopt_score  = c->score;
    if (g_pos_mode == 0) g_pos_sel = c->pos_sel;
    g_mat_ok = true;
    char mb[200];
    int o = 0;
    for (int i = 0; i < 16; i++)
        o += snprintf(mb + o, sizeof(mb) - o, "%.3f ", g_vp[i]);
    mlog("matrix ADOPTED score=%d pos=%c @ 0x%llx\n  row-major: %s",
         c->score, g_pos_sel ? 'B' : 'A', (unsigned long long)c->addr, mb);
}

// ---------------- worker thread ----------------
static void worker_loop(void) {
    static float prev_a[MAX_ENTS][3], prev_b[MAX_ENTS][3];
    static int prev_n = 0;
    static uint64_t probe_bm = 0;
    static bool probe_logged = false, probe_fail_logged = false;
    static int rescans = 0;
    static int dbg_tick = 0;

    static const int lcands[] = { 0x50, 0x58, 0x60, 0x68, 0x70, 0x78, 0x80,
        0x88, 0x90, 0x98, 0xA0, 0xA8, 0xB0, 0xB8, 0xC0, 0xC8, 0xD0, 0xD8,
        0xE0, 0xE8, 0xF0, 0xF8, 0x100, 0x108 };
    static const int nl = (int)(sizeof(lcands) / sizeof(lcands[0]));
    static float lacc[nl]; static int ln[nl];
    static int lbest_prev = -1, lbest_run = 0;
    static int g_local_off = -1;

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
            g_pos_sel = 1; g_uf = 0;
            g_last_vp_addr = 0; g_adopt_score = 0;
            memset(&g_pending, 0, sizeof g_pending); g_conf_ticks = 0;
            g_local_off = -1; lbest_prev = -1; lbest_run = 0;
            memset(lacc, 0, sizeof lacc); memset(ln, 0, sizeof ln);
            sleep(1); continue;
        }
        uint64_t statics = rd64(klass + OFF_CLASS_STATICS);
        uint64_t bm = statics ? rd64(statics + OFF_STATICS_INSTANCE) : 0;
        if (!bm) {
            EspFrame f; memset(&f, 0, sizeof f);
            snprintf(f.status, sizeof f.status, "lobby (no battle instance)");
            os_unfair_lock_lock(&g_lock); g_frame = f; os_unfair_lock_unlock(&g_lock);
            g_list_off = -1; g_mat_ok = false; g_kcache_n = 0; g_pos_sel = 1;
            g_last_vp_addr = 0; g_adopt_score = 0;
            memset(&g_pending, 0, sizeof g_pending); g_conf_ticks = 0;
            g_local_off = -1; lbest_prev = -1; lbest_run = 0;
            memset(lacc, 0, sizeof lacc); memset(ln, 0, sizeof ln);
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
        if (probe_bm != bm) {
            probe_bm = bm; probe_logged = false; probe_fail_logged = false;
            g_local_off = -1; lbest_prev = -1; lbest_run = 0;
            memset(lacc, 0, sizeof lacc); memset(ln, 0, sizeof ln);
        }

        int sel = (g_pos_mode == 0) ? g_pos_sel : (g_pos_mode - 1);

        uint64_t lst = rd64(bm + g_list_off);
        uint64_t arr = lst ? rd64(lst + 0x10) : 0;
        int32_t  size = lst ? rdi32(lst + 0x18) : 0;
        if (!arr || size < 1 || size > 512) { g_list_off = -1; continue; }

        // v22: BOTH snap sets, always
        Snap snapsA[MAX_ENTS], snapsB[MAX_ENTS];
        int snapA_n = 0, snapB_n = 0;
        int count = 0;
        int skip_not_hero = 0, skip_nopos = 0;
        float move_a = 0, move_b = 0;
        EspFrame f;
        memset(&f, 0, sizeof f);

        bool dbg = (++dbg_tick % 20) == 0;
        static char dbgbuf[2048];
        int dbgoff = 0;

        if (dbg)
            dbgoff += snprintf(dbgbuf, sizeof(dbgbuf),
                "ents dump: list size=%d\n", size);

        for (int32_t i = 0; i < size && count < MAX_ENTS; i++) {
            uint64_t e = rd64(arr + 0x20 + 8ull * (uint64_t)i);
            if (!e || !is_hero_obj(e)) { skip_not_hero++; continue; }

            float pa[3] = {0}, pb[3] = {0};
            if (!rd_vec3(e + OFF_ENT_POS_A, pa) || !rd_vec3(e + OFF_ENT_POS_B, pb)) {
                skip_nopos++; continue;
            }

            if (count < prev_n) {
                move_a += fabsf(pa[0]-prev_a[count][0]) + fabsf(pa[2]-prev_a[count][2]);
                move_b += fabsf(pb[0]-prev_b[count][0]) + fabsf(pb[2]-prev_b[count][2]);
            }
            memcpy(prev_a[count], pa, 12);
            memcpy(prev_b[count], pb, 12);

            if (snapA_n < MAX_ENTS) {
                snapsA[snapA_n].x = pa[0]; snapsA[snapA_n].y = pa[1];
                snapsA[snapA_n].z = pa[2]; snapA_n++;
            }
            if (snapB_n < MAX_ENTS) {
                snapsB[snapB_n].x = pb[0]; snapsB[snapB_n].y = pb[1];
                snapsB[snapB_n].z = pb[2]; snapB_n++;
            }

            EspEnt *en = &f.ents[count];
            en->hp      = rdi32(e + OFF_ENT_HP);
            en->hpmax   = rdi32(e + OFF_ENT_HPMAX);
            en->visible = rdi32(e + OFF_ENT_CANSIGHT);
            en->dead    = (en->hp <= 0);
            en->sx = 0; en->sy = 0; en->box_h = 0; en->box_w = 0;

            float fx = (sel == 0) ? pa[0] : pb[0];
            float fy = (sel == 0) ? pa[1] : pb[1];
            float fz = (sel == 0) ? pa[2] : pb[2];

            float cw = 0;
            float bh = project_box(fx, fy, fz, &en->sx, &en->sy, &cw);
            if (bh > 0.0f) {
                en->box_h = bh;
                en->box_w = bh * 0.55f;
            }

            if (dbg && dbgoff < (int)sizeof(dbgbuf) - 260)
                dbgoff += snprintf(dbgbuf + dbgoff, sizeof(dbgbuf) - dbgoff,
                    "[%d] A=(%.1f,%.1f,%.1f) B=(%.1f,%.1f,%.1f) hp=%d/%d bh=%.0f sx=%.0f sy=%.0f\n",
                    count, pa[0], pa[1], pa[2], pb[0], pb[1], pb[2],
                    en->hp, en->hpmax, en->box_h, en->sx, en->sy);

            count++;
        }
        prev_n = count;

        if (dbg)
            mlog("%smatched=%d skipNH=%d skipNP=%d sel=%c", dbgbuf,
                 count, skip_not_hero, skip_nopos, sel ? 'B' : 'A');

        if (g_pos_mode == 0) {
            if (move_a < 0.01f && move_b > 0.5f && g_pos_sel == 0) {
                g_pos_sel = 1;
                mlog("auto-flip A->B (A frozen)");
            } else if (move_b < 0.01f && move_a > 0.5f && g_pos_sel == 1) {
                g_pos_sel = 0;
                mlog("auto-flip B->A (B frozen)");
            }
        }

        // ---- matrix state machine: scan -> confirm x3 -> adopted ----
        int snap_for_scan = (sel == 0) ? snapA_n : snapB_n;
        (void)snap_for_scan;

        int conf_step = 0;
        int mat_state = 0;   // 0 scan, 1 confirming, 2 ok

        if (g_mat_ok) {
            const Snap *cur = (g_pos_sel == 0) ? snapsA : snapsB;
            int cn = (g_pos_sel == 0) ? snapA_n : snapB_n;
            if (cn >= 3 && !vp_revalidate(cur, cn)) {
                g_mat_ok = false;
                memset(&g_pending, 0, sizeof g_pending);
                g_conf_ticks = 0;
                mlog("matrix stale — rescanning (#%d)", ++rescans);
            } else {
                mat_state = 2;
            }
        }

        if (!g_mat_ok && snapA_n >= 3 && snapB_n >= 3) {
            if (g_pending.valid) {
                // CONFIRMATION: re-read fresh values, rescore with fresh snaps
                float m[16];
                if (rd(g_pending.addr, m, sizeof m)) {
                    int sA = (g_pos_mode != 1) ? vp_score(m, snapsA, snapA_n) : -1;
                    int sB = (g_pos_mode != 2) ? vp_score(m, snapsB, snapB_n) : -1;
                    int sc = (sA >= sB) ? sA : sB;
                    int psel = (sA >= sB) ? 0 : 1;
                    int need = (7 * ((sA >= sB) ? snapA_n : snapB_n)) / 10;
                    if (sc >= (need > 3 ? need : 3)) {
                        g_conf_ticks++;
                        conf_step = g_conf_ticks;
                        mat_state = 1;
                        memcpy(g_pending.m, m, sizeof g_pending.m);
                        g_pending.score = sc;
                        g_pending.pos_sel = psel;
                        if (g_conf_ticks >= 3) {
                            adopt_matrix(&g_pending);
                            memset(&g_pending, 0, sizeof g_pending);
                            g_conf_ticks = 0;
                            mat_state = 2;
                        }
                    } else {
                        // failed confirmation — heroes moved, garbage died
                        mlog("candidate FAILED confirmation (tick %d, score %d)",
                             g_conf_ticks, sc);
                        memset(&g_pending, 0, sizeof g_pending);
                        g_conf_ticks = 0;
                    }
                } else {
                    memset(&g_pending, 0, sizeof g_pending);
                    g_conf_ticks = 0;
                }
            }

            if (!g_mat_ok && !g_pending.valid) {
                VpCand c;
                if (scan_matrix(snapsA, snapA_n, snapsB, snapB_n, &c)) {
                    g_pending = c;
                    g_conf_ticks = 0;
                    mat_state = 1;
                    conf_step = 0;
                    mlog("candidate @ 0x%llx score=%d pos=%c — confirming (3 ticks)",
                         (unsigned long long)c.addr, c.score,
                         c.pos_sel ? 'B' : 'A');
                }
            }
        }

        // ---- local player: centrality auto-probe (needs mat ok) ----
        f.local_ok = 0;
        f.local_drawn = 0;
        f.local_off = -1;

        uint64_t lshow = 0;
        int loff_used = -1;

        if (g_local_off > 0) {
            uint64_t p = rd64(bm + g_local_off);
            if (p && is_hero_obj(p)) { lshow = p; loff_used = g_local_off; }
            else { g_local_off = -1; lbest_prev = -1; lbest_run = 0; }
        }

        if (g_mat_ok && snapA_n >= 3 && g_local_off < 0) {
            float cx = g_screen_w * 0.5f, cy = g_screen_h * 0.5f;
            int best = -1; float bestd = 1e9f;
            for (int i = 0; i < nl; i++) {
                if (lcands[i] == g_list_off) continue;
                uint64_t p = rd64(bm + lcands[i]);
                if (!p || !is_hero_obj(p)) { lacc[i] = 0; ln[i] = 0; continue; }
                float la[3] = {0}, lb[3] = {0};
                if (!rd_vec3(p + OFF_ENT_POS_A, la) || !rd_vec3(p + OFF_ENT_POS_B, lb)) {
                    lacc[i] = 0; ln[i] = 0; continue;
                }
                float lx = (sel == 0) ? la[0] : lb[0];
                float ly = (sel == 0) ? la[1] : lb[1];
                float lz = (sel == 0) ? la[2] : lb[2];
                float sx, sy, cw;
                float bh = project_box(lx, ly, lz, &sx, &sy, &cw);
                if (bh < 10.0f ||
                    sx < -g_screen_w*0.2f || sx > g_screen_w*1.2f ||
                    sy < -g_screen_h*0.2f || sy > g_screen_h*1.2f) {
                    lacc[i] *= 0.7f; continue;
                }
                float d = fabsf(sx - cx) + fabsf(sy - cy);
                lacc[i] = lacc[i] * 0.9f + d;
                ln[i]++;
                if (ln[i] >= 3) {
                    float avg = lacc[i] / (float)ln[i];
                    if (avg < bestd) { bestd = avg; best = i; }
                }
            }
            if (best >= 0) {
                if (best == lbest_prev) lbest_run++;
                else { lbest_prev = best; lbest_run = 1; }
                if (lbest_run >= 8 && ln[best] >= 6) {
                    g_local_off = lcands[best];
                    mlog("local LOCKED @ BM+0x%x (avg dist %.0f)",
                         g_local_off, lacc[best] / (float)ln[best]);
                }
            } else { lbest_prev = -1; lbest_run = 0; }
        }

        if (lshow || (g_local_off > 0)) {
            if (!lshow) {
                uint64_t p = rd64(bm + g_local_off);
                if (p && is_hero_obj(p)) { lshow = p; loff_used = g_local_off; }
            }
            if (lshow) {
                float la[3] = {0}, lb[3] = {0};
                if (rd_vec3(lshow + OFF_ENT_POS_A, la) && rd_vec3(lshow + OFF_ENT_POS_B, lb)) {
                    float lx = (sel == 0) ? la[0] : lb[0];
                    float ly = (sel == 0) ? la[1] : lb[1];
                    float lz = (sel == 0) ? la[2] : lb[2];
                    f.local_ok = 1;
                    f.local_off = loff_used;
                    if (g_mat_ok) {
                        float cw = 0;
                        float bh = project_box(lx, ly, lz, &f.local_sx, &f.local_sy, &cw);
                        if (bh >= 2.0f && bh <= 2000.0f) {
                            f.local_bh = bh;
                            f.local_drawn = 1;
                        }
                    }
                    if (!probe_logged) {
                        probe_logged = true;
                        mlog("local ShowPlayer @ 0x%llx via BM+0x%x",
                             (unsigned long long)lshow, loff_used);
                    }
                    static int local_log_tick = 0;
                    if ((++local_log_tick % 20) == 1) {
                        mlog("LOCAL: off=0x%x ptr=0x%llx wp=(%.1f,%.1f,%.1f) sx=%.0f sy=%.0f drawn=%d",
                             loff_used, (unsigned long long)lshow, lx, ly, lz,
                             f.local_sx, f.local_sy, f.local_drawn);
                    }
                }
            }
        }
        if (!f.local_ok && !probe_fail_logged && count > 0) {
            probe_fail_logged = true;
            mlog("local unresolved — probing / fallback origin");
        }

        f.matrix_ok = g_mat_ok ? 1 : 0;
        f.mat_score = g_adopt_score;
        f.mat_state = mat_state;
        f.conf_step = conf_step;
        f.pos_sel   = sel;
        f.pos_mode  = g_pos_mode;
        f.entity_count = count;
        memcpy(f.vp, g_vp, sizeof f.vp);
        {
            const char *ms = mat_state == 2 ? "ok" : mat_state == 1 ? "conf" : "scan";
            snprintf(f.status, sizeof f.status, "ents=%d mat=%s(%d) pos=%c loc=%s",
                     count, ms, g_adopt_score, sel ? 'B' : 'A',
                     f.local_ok ? (f.local_drawn ? "scr" : "ptr") : "no");
        }

        os_unfair_lock_lock(&g_lock);
        g_frame = f;
        os_unfair_lock_unlock(&g_lock);

        usleep(100000);
    }
}

// ---------------- config ----------------
struct EspCfg {
    bool esp_on, boxes, hp_bars, snaplines, vision_only, status_text, grid;
};
static EspCfg g_cfg = { true, true, true, true, false, true, true };

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
    if (!g_initialized) return;

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

    // world-grid overlay: with a TRUE matrix the grid lies flat on the map
    // floor. If it doesn't, the matrix is wrong — no heroes needed to tell.
    if (g_cfg.grid && f.matrix_ok) {
        const ImU32 col_grid = IM_COL32(120, 120, 255, 70);
        float save[16];
        memcpy(save, g_vp, sizeof save);
        memcpy(g_vp, f.vp, sizeof save);
        for (int x = -80; x <= 80; x += 10) {
            float ax, ay, bx, by, cw;
            if (project((float)x, 0, -80, &ax, &ay, &cw) &&
                project((float)x, 0,  80, &bx, &by, &cw))
                dl->AddLine(ImVec2(ax, ay), ImVec2(bx, by), col_grid, 1.0f);
        }
        for (int z = -80; z <= 80; z += 10) {
            float ax, ay, bx, by, cw;
            if (project(-80, 0, (float)z, &ax, &ay, &cw) &&
                project( 80, 0, (float)z, &bx, &by, &cw))
                dl->AddLine(ImVec2(ax, ay), ImVec2(bx, by), col_grid, 1.0f);
        }
        memcpy(g_vp, save, sizeof save);
    }

    if (g_cfg.esp_on && f.matrix_ok) {
        const ImU32 col_box   = IM_COL32(255, 165, 0, 255);
        const ImU32 col_line  = IM_COL32(255, 165, 0, 180);
        const ImU32 col_hpbg  = IM_COL32(0, 0, 0, 180);
        const ImU32 col_hp    = IM_COL32(80, 220, 60, 255);
        const ImU32 col_local = IM_COL32(0, 220, 255, 255);

        float ox, oy;
        if (f.local_drawn) { ox = f.local_sx; oy = f.local_sy; }
        else { ox = io.DisplaySize.x * 0.5f; oy = io.DisplaySize.y; }

        for (uint32_t i = 0; i < f.entity_count && i < MAX_ENTS; i++) {
            const EspEnt &e = f.ents[i];
            if (e.dead) continue;
            if (g_cfg.vision_only && !e.visible) continue;
            if (e.box_h < 2.0f) continue;

            float h = e.box_h, w = e.box_w;
            float x0 = e.sx - w * 0.5f, y0 = e.sy - h;
            float x1 = e.sx + w * 0.5f, y1 = e.sy;

            if (g_cfg.boxes)
                dl->AddRect(ImVec2(x0, y0), ImVec2(x1, y1), col_box, 0.0f, 0, 2.0f);

            if (g_cfg.hp_bars && e.hpmax > 0) {
                float pct = (float)e.hp / (float)e.hpmax;
                if (pct < 0) pct = 0; if (pct > 1) pct = 1;
                float bx = x0 - 7.0f;
                dl->AddRectFilled(ImVec2(bx - 1, y0 - 1), ImVec2(bx + 4, y1 + 1), col_hpbg);
                dl->AddRectFilled(ImVec2(bx, y1 - (y1 - y0) * pct), ImVec2(bx + 3, y1), col_hp);
            }

            if (g_cfg.snaplines)
                dl->AddLine(ImVec2(ox, oy),
                            ImVec2(e.sx, e.sy - e.box_h * 0.5f), col_line, 1.2f);
        }

        if (f.local_drawn) {
            float w = f.local_bh * 0.55f, h = f.local_bh;
            float x0 = f.local_sx - w * 0.5f, y0 = f.local_sy - h;
            float x1 = f.local_sx + w * 0.5f, y1 = f.local_sy;
            dl->AddRect(ImVec2(x0, y0), ImVec2(x1, y1), col_local, 0.0f, 0, 2.0f);
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
        ImVec2 mn = ImGui::GetItemRectMin(), mx = ImGui::GetItemRectMax();
        ImVec2 cc((mn.x + mx.x) * 0.5f, (mn.y + mx.y) * 0.5f);
        dl->AddCircleFilled(cc, 17.0f, g_menu_open ? IM_COL32(0,200,255,220) : IM_COL32(255,255,255,160));
        dl->AddCircle(cc, 17.0f, IM_COL32(0,0,0,255), 0, 2.0f);
    }
    ImGui::End();
    ImGui::PopStyleColor();

    if (g_cfg.status_text) {
        char st[192];
        const char *ms = f.mat_state == 2 ? "ok" : f.mat_state == 1 ? "conf" : "scan";
        snprintf(st, sizeof st,
                 "ents=%u mat=%s(%d)%s%d pos=%c loc=%s | e0 sx=%.0f sy=%.0f bh=%.0f hp=%d",
                 f.entity_count, ms, f.mat_score,
                 f.mat_state == 1 ? "(" : "",
                 f.mat_state == 1 ? f.conf_step : 0,
                 f.mat_state == 1 ? "/3)" : "",
                 f.pos_sel ? 'B' : 'A',
                 f.local_ok ? (f.local_drawn ? "scr" : "ptr") : "no",
                 f.entity_count ? f.ents[0].sx : 0.f,
                 f.entity_count ? f.ents[0].sy : 0.f,
                 f.entity_count ? f.ents[0].box_h : 0.f,
                 f.entity_count ? f.ents[0].hp : 0);
        dl->AddText(ImVec2(8, 30), IM_COL32(0, 220, 255, 255), st);
    }

    if (g_menu_open) {
        ImGui::SetNextWindowPos(ImVec2(60, 40), ImGuiCond_Once);
        ImGui::Begin("MLBB ESP", &g_menu_open, ImGuiWindowFlags_AlwaysAutoResize);
        ImGui::Checkbox("ESP enabled",    &g_cfg.esp_on);
        ImGui::Checkbox("Boxes",          &g_cfg.boxes);
        ImGui::Checkbox("HP bars",        &g_cfg.hp_bars);
        ImGui::Checkbox("Snaplines",      &g_cfg.snaplines);
        ImGui::Checkbox("World grid (matrix check)", &g_cfg.grid);
        ImGui::Checkbox("Vision only (safe)", &g_cfg.vision_only);
        ImGui::Checkbox("Status text",    &g_cfg.status_text);
        ImGui::SliderFloat("Hero height", &g_hero_h, 2.0f, 12.0f, "%.1f");

        const char *pm = (f.pos_mode == 0) ? "pos: auto" : (f.pos_mode == 1) ? "pos: force A" : "pos: force B";
        if (ImGui::Button(pm)) g_pos_mode = (g_pos_mode + 1) % 3;
        if (ImGui::Button("Force matrix rescan")) {
            g_mat_ok = false;
            g_adopt_score = 0;
            g_last_vp_addr = 0;
            memset(&g_pending, 0, sizeof g_pending);
            g_conf_ticks = 0;
            mlog("manual rescan requested from menu");
        }
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
    mlog("overlay up (v22 confirmation-gated + scan-both-positions + grid)");
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
    mlog("=== ctor fired: VERSION 22 BUILD (confirm-gate + A/B scan + grid) ===");
    create_loop();
    dispatch_async(dispatch_get_global_queue(QOS_CLASS_UTILITY, 0), ^{
        sleep(3);
        worker_loop();
    });
}
