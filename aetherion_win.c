// AETHERION V2.5 // NVIDIA-Accelerated Native Windows C + OpenGL 4.6 Compute + NVML
// Compiles directly with build_windows.bat (MinGW-w64 gcc or MSVC cl, zero SDKs needed)
//
// CONTROLS:
//   Left-Drag            : Orbit camera        | Right-Drag / Shift+Drag : Pan
//   Mouse Wheel          : Zoom                | WASD + Q/E (+Shift)     : Free-Fly
//   1 - 4                : Switch Worlds       | Space                   : Auto-Director
//   F                    : Optical Filter (Cinema HDR / Bodycam UE5 / Anamorphic / Raw)
//   T                    : Tone Mapper (AgX / ACES / PBR-N / Hable)
//   V                    : Inspector Mode (Beauty / Normal / Depth / Water)
//   B  ( [ / ] )         : Split-Screen Wipe   | G : TAA  | X : Auto-Exposure
//   - / =                : Exposure Bias       | Up/Down : Sun Elevation | Left/Right : Water Clarity
//   F5 - F8              : Render Scale (0.50x / 0.75x / 1.00x / 1.25x)
//   R                    : Reset Camera        | U : VSync (Adaptive-NV / On / Off) | F11 : Fullscreen | ESC : Quit

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <GL/gl.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#pragma comment(lib, "opengl32.lib")
#pragma comment(lib, "gdi32.lib")
#pragma comment(lib, "user32.lib")

// Force discrete NVIDIA RTX GPU on hybrid/Optimus Windows systems
__declspec(dllexport) DWORD NvOptimusEnablement = 0x00000001;
__declspec(dllexport) int   AmdPowerXpressRequestHighPerformance = 1;

// ============================================================================
// RUNTIME NVIDIA MANAGEMENT LIBRARY (nvml.dll — ZERO SDK HEADERS REQUIRED)
// ============================================================================
typedef struct nvmlDevice_st *nvmlDevice_t;
typedef struct { unsigned int gpu; unsigned int memory; } nvmlUtilization_t;

typedef int (*PFN_nvmlInit_v2)(void);
typedef int (*PFN_nvmlShutdown)(void);
typedef int (*PFN_nvmlDeviceGetHandleByIndex_v2)(unsigned int, nvmlDevice_t *);
typedef int (*PFN_nvmlDeviceGetName)(nvmlDevice_t, char *, unsigned int);
typedef int (*PFN_nvmlDeviceGetTemperature)(nvmlDevice_t, int, unsigned int *);
typedef int (*PFN_nvmlDeviceGetUtilizationRates)(nvmlDevice_t, nvmlUtilization_t *);
typedef int (*PFN_nvmlDeviceGetClockInfo)(nvmlDevice_t, int, unsigned int *);
typedef int (*PFN_nvmlDeviceGetPowerUsage)(nvmlDevice_t, unsigned int *);

typedef struct {
  HMODULE dll;
  int active;
  nvmlDevice_t dev;
  char name[64];
  unsigned int tempC;
  unsigned int gpuUtil;
  unsigned int clkMHz;
  float powerW;
  PFN_nvmlShutdown shutdown;
  PFN_nvmlDeviceGetTemperature getTemp;
  PFN_nvmlDeviceGetUtilizationRates getUtil;
  PFN_nvmlDeviceGetClockInfo getClock;
  PFN_nvmlDeviceGetPowerUsage getPower;
} NvmlState;

static NvmlState g_nvml;

static void nvml_try_init(void) {
  memset(&g_nvml, 0, sizeof(g_nvml));
  g_nvml.dll = LoadLibraryA("nvml.dll");
  if (!g_nvml.dll) {
    g_nvml.dll = LoadLibraryA("C:\\Program Files\\NVIDIA Corporation\\NVSMI\\nvml.dll");
  }
  if (!g_nvml.dll) return;

  PFN_nvmlInit_v2 fnInit = (PFN_nvmlInit_v2)GetProcAddress(g_nvml.dll, "nvmlInit_v2");
  PFN_nvmlDeviceGetHandleByIndex_v2 fnHandle =
    (PFN_nvmlDeviceGetHandleByIndex_v2)GetProcAddress(g_nvml.dll, "nvmlDeviceGetHandleByIndex_v2");
  PFN_nvmlDeviceGetName fnName = (PFN_nvmlDeviceGetName)GetProcAddress(g_nvml.dll, "nvmlDeviceGetName");

  g_nvml.shutdown = (PFN_nvmlShutdown)GetProcAddress(g_nvml.dll, "nvmlShutdown");
  g_nvml.getTemp  = (PFN_nvmlDeviceGetTemperature)GetProcAddress(g_nvml.dll, "nvmlDeviceGetTemperature");
  g_nvml.getUtil  = (PFN_nvmlDeviceGetUtilizationRates)GetProcAddress(g_nvml.dll, "nvmlDeviceGetUtilizationRates");
  g_nvml.getClock = (PFN_nvmlDeviceGetClockInfo)GetProcAddress(g_nvml.dll, "nvmlDeviceGetClockInfo");
  g_nvml.getPower = (PFN_nvmlDeviceGetPowerUsage)GetProcAddress(g_nvml.dll, "nvmlDeviceGetPowerUsage");

  if (!fnInit || !fnHandle || fnInit() != 0) {
    FreeLibrary(g_nvml.dll);
    g_nvml.dll = NULL;
    return;
  }
  if (fnHandle(0, &g_nvml.dev) != 0) {
    if (g_nvml.shutdown) g_nvml.shutdown();
    FreeLibrary(g_nvml.dll);
    g_nvml.dll = NULL;
    return;
  }
  if (fnName) fnName(g_nvml.dev, g_nvml.name, sizeof(g_nvml.name));
  // Shorten "NVIDIA GeForce RTX 3070 Ti" -> "RTX 3070 Ti" for crisp titlebar
  const char *rtx = strstr(g_nvml.name, "RTX");
  if (!rtx) rtx = strstr(g_nvml.name, "GTX");
  if (rtx && rtx != g_nvml.name) memmove(g_nvml.name, rtx, strlen(rtx) + 1);
  g_nvml.active = 1;
}

static void nvml_poll(void) {
  if (!g_nvml.active) return;
  if (g_nvml.getTemp)  g_nvml.getTemp(g_nvml.dev, 0, &g_nvml.tempC);
  if (g_nvml.getClock) g_nvml.getClock(g_nvml.dev, 0, &g_nvml.clkMHz);
  if (g_nvml.getUtil) {
    nvmlUtilization_t u = {0, 0};
    if (g_nvml.getUtil(g_nvml.dev, &u) == 0) g_nvml.gpuUtil = u.gpu;
  }
  if (g_nvml.getPower) {
    unsigned int mw = 0;
    if (g_nvml.getPower(g_nvml.dev, &mw) == 0) g_nvml.powerW = (float)mw * 0.001f;
  }
}

static void nvml_cleanup(void) {
  if (g_nvml.active && g_nvml.shutdown) g_nvml.shutdown();
  if (g_nvml.dll) FreeLibrary(g_nvml.dll);
  memset(&g_nvml, 0, sizeof(g_nvml));
}

// ============================================================================
// OPENGL 4.6 CORE + NVIDIA EXTENSION CONSTANTS & FUNCTION POINTERS
// ============================================================================
#ifndef GL_FRAGMENT_SHADER
#define GL_FRAGMENT_SHADER                            0x8B30
#endif
#ifndef GL_VERTEX_SHADER
#define GL_VERTEX_SHADER                              0x8B31
#endif
#ifndef GL_COMPUTE_SHADER
#define GL_COMPUTE_SHADER                             0x91B9
#endif
#ifndef GL_COMPILE_STATUS
#define GL_COMPILE_STATUS                             0x8B81
#endif
#ifndef GL_LINK_STATUS
#define GL_LINK_STATUS                                0x8B82
#endif
#ifndef GL_CLAMP_TO_EDGE
#define GL_CLAMP_TO_EDGE                              0x812F
#endif
#ifndef GL_TEXTURE0
#define GL_TEXTURE0                                   0x84C0
#endif
#ifndef GL_RGBA16F
#define GL_RGBA16F                                    0x881A
#endif
#ifndef GL_R11F_G11F_B10F
#define GL_R11F_G11F_B10F                             0x8C3A
#endif
#ifndef GL_HALF_FLOAT
#define GL_HALF_FLOAT                                 0x140B
#endif
#ifndef GL_FRAMEBUFFER
#define GL_FRAMEBUFFER                                0x8D40
#endif
#ifndef GL_COLOR_ATTACHMENT0
#define GL_COLOR_ATTACHMENT0                          0x8CE0
#endif
#ifndef GL_FRAMEBUFFER_COMPLETE
#define GL_FRAMEBUFFER_COMPLETE                       0x8CD5
#endif
#ifndef GL_WRITE_ONLY
#define GL_WRITE_ONLY                                 0x88B9
#endif
#ifndef GL_SHADER_IMAGE_ACCESS_BARRIER_BIT
#define GL_SHADER_IMAGE_ACCESS_BARRIER_BIT            0x00000020
#endif
#ifndef GL_TEXTURE_FETCH_BARRIER_BIT
#define GL_TEXTURE_FETCH_BARRIER_BIT                  0x00000008
#endif
#ifndef GL_TIME_ELAPSED
#define GL_TIME_ELAPSED                               0x88BF
#endif
#ifndef GL_QUERY_RESULT
#define GL_QUERY_RESULT                               0x8866
#endif
#ifndef GL_QUERY_RESULT_AVAILABLE
#define GL_QUERY_RESULT_AVAILABLE                     0x8867
#endif
#ifndef GL_GPU_MEMORY_INFO_DEDICATED_VIDMEM_NVX
#define GL_GPU_MEMORY_INFO_DEDICATED_VIDMEM_NVX       0x9047
#define GL_GPU_MEMORY_INFO_CURRENT_AVAILABLE_VIDMEM_NVX 0x9049
#endif
#ifndef WGL_CONTEXT_MAJOR_VERSION_ARB
#define WGL_CONTEXT_MAJOR_VERSION_ARB                 0x2091
#define WGL_CONTEXT_MINOR_VERSION_ARB                 0x2092
#define WGL_CONTEXT_PROFILE_MASK_ARB                  0x9126
#define WGL_CONTEXT_CORE_PROFILE_BIT_ARB              0x00000001
#endif

typedef HGLRC  (WINAPI   *PFNWGLCREATECONTEXTATTRIBSARBPROC)(HDC, HGLRC, const int*);
typedef BOOL   (WINAPI   *PFNWGLSWAPINTERVALEXTPROC)(int);
typedef GLuint (APIENTRY *PFNGLCREATESHADERPROC)(GLenum);
typedef void   (APIENTRY *PFNGLSHADERSOURCEPROC)(GLuint, GLsizei, const char* const*, const GLint*);
typedef void   (APIENTRY *PFNGLCOMPILESHADERPROC)(GLuint);
typedef void   (APIENTRY *PFNGLGETSHADERIVPROC)(GLuint, GLenum, GLint*);
typedef void   (APIENTRY *PFNGLGETSHADERINFOLOGPROC)(GLuint, GLsizei, GLsizei*, char*);
typedef void   (APIENTRY *PFNGLDELETESHADERPROC)(GLuint);
typedef GLuint (APIENTRY *PFNGLCREATEPROGRAMPROC)(void);
typedef void   (APIENTRY *PFNGLATTACHSHADERPROC)(GLuint, GLuint);
typedef void   (APIENTRY *PFNGLLINKPROGRAMPROC)(GLuint);
typedef void   (APIENTRY *PFNGLGETPROGRAMIVPROC)(GLuint, GLenum, GLint*);
typedef void   (APIENTRY *PFNGLGETPROGRAMINFOLOGPROC)(GLuint, GLsizei, GLsizei*, char*);
typedef void   (APIENTRY *PFNGLUSEPROGRAMPROC)(GLuint);
typedef GLint  (APIENTRY *PFNGLGETUNIFORMLOCATIONPROC)(GLuint, const char*);
typedef void   (APIENTRY *PFNGLUNIFORM1FPROC)(GLint, GLfloat);
typedef void   (APIENTRY *PFNGLUNIFORM1IPROC)(GLint, GLint);
typedef void   (APIENTRY *PFNGLUNIFORM2FPROC)(GLint, GLfloat, GLfloat);
typedef void   (APIENTRY *PFNGLUNIFORM2IPROC)(GLint, GLint, GLint);
typedef void   (APIENTRY *PFNGLUNIFORM3FVPROC)(GLint, GLsizei, const GLfloat*);
typedef void   (APIENTRY *PFNGLUNIFORMMATRIX3FVPROC)(GLint, GLsizei, GLboolean, const GLfloat*);
typedef void   (APIENTRY *PFNGLACTIVETEXTUREPROC)(GLenum);
typedef void   (APIENTRY *PFNGLGENFRAMEBUFFERSPROC)(GLsizei, GLuint*);
typedef void   (APIENTRY *PFNGLBINDFRAMEBUFFERPROC)(GLenum, GLuint);
typedef void   (APIENTRY *PFNGLFRAMEBUFFERTEXTURE2DPROC)(GLenum, GLenum, GLenum, GLuint, GLint);
typedef GLenum (APIENTRY *PFNGLCHECKFRAMEBUFFERSTATUSPROC)(GLenum);
typedef void   (APIENTRY *PFNGLDELETEFRAMEBUFFERSPROC)(GLsizei, const GLuint*);
typedef void   (APIENTRY *PFNGLGENVERTEXARRAYSPROC)(GLsizei, GLuint*);
typedef void   (APIENTRY *PFNGLBINDVERTEXARRAYPROC)(GLuint);
typedef void   (APIENTRY *PFNGLDISPATCHCOMPUTEPROC)(GLuint, GLuint, GLuint);
typedef void   (APIENTRY *PFNGLMEMORYBARRIERPROC)(GLbitfield);
typedef void   (APIENTRY *PFNGLBINDIMAGETEXTUREPROC)(GLuint, GLuint, GLint, GLboolean, GLint, GLenum, GLenum);
typedef void   (APIENTRY *PFNGLGENQUERIESPROC)(GLsizei, GLuint*);
typedef void   (APIENTRY *PFNGLBEGINQUERYPROC)(GLenum, GLuint);
typedef void   (APIENTRY *PFNGLENDQUERYPROC)(GLenum);
typedef void   (APIENTRY *PFNGLGETQUERYOBJECTIVPROC)(GLuint, GLenum, GLint*);
typedef void   (APIENTRY *PFNGLGETQUERYOBJECTUI64VPROC)(GLuint, GLenum, uint64_t*);

static PFNWGLCREATECONTEXTATTRIBSARBPROC wglCreateContextAttribsARB;
static PFNWGLSWAPINTERVALEXTPROC         wglSwapIntervalEXT;
static PFNGLCREATESHADERPROC             pglCreateShader;
static PFNGLSHADERSOURCEPROC             pglShaderSource;
static PFNGLCOMPILESHADERPROC            pglCompileShader;
static PFNGLGETSHADERIVPROC              pglGetShaderiv;
static PFNGLGETSHADERINFOLOGPROC         pglGetShaderInfoLog;
static PFNGLDELETESHADERPROC             pglDeleteShader;
static PFNGLCREATEPROGRAMPROC            pglCreateProgram;
static PFNGLATTACHSHADERPROC             pglAttachShader;
static PFNGLLINKPROGRAMPROC              pglLinkProgram;
static PFNGLGETPROGRAMIVPROC             pglGetProgramiv;
static PFNGLGETPROGRAMINFOLOGPROC        pglGetProgramInfoLog;
static PFNGLUSEPROGRAMPROC               pglUseProgram;
static PFNGLGETUNIFORMLOCATIONPROC       pglGetUniformLocation;
static PFNGLUNIFORM1FPROC                pglUniform1f;
static PFNGLUNIFORM1IPROC                pglUniform1i;
static PFNGLUNIFORM2FPROC                pglUniform2f;
static PFNGLUNIFORM2IPROC                pglUniform2i;
static PFNGLUNIFORM3FVPROC               pglUniform3fv;
static PFNGLUNIFORMMATRIX3FVPROC         pglUniformMatrix3fv;
static PFNGLACTIVETEXTUREPROC            pglActiveTexture;
static PFNGLGENFRAMEBUFFERSPROC          pglGenFramebuffers;
static PFNGLBINDFRAMEBUFFERPROC          pglBindFramebuffer;
static PFNGLFRAMEBUFFERTEXTURE2DPROC     pglFramebufferTexture2D;
static PFNGLCHECKFRAMEBUFFERSTATUSPROC   pglCheckFramebufferStatus;
static PFNGLDELETEFRAMEBUFFERSPROC       pglDeleteFramebuffers;
static PFNGLGENVERTEXARRAYSPROC          pglGenVertexArrays;
static PFNGLBINDVERTEXARRAYPROC          pglBindVertexArray;
static PFNGLDISPATCHCOMPUTEPROC          pglDispatchCompute;
static PFNGLMEMORYBARRIERPROC            pglMemoryBarrier;
static PFNGLBINDIMAGETEXTUREPROC         pglBindImageTexture;
static PFNGLGENQUERIESPROC               pglGenQueries;
static PFNGLBEGINQUERYPROC               pglBeginQuery;
static PFNGLENDQUERYPROC                 pglEndQuery;
static PFNGLGETQUERYOBJECTIVPROC         pglGetQueryObjectiv;
static PFNGLGETQUERYOBJECTUI64VPROC      pglGetQueryObjectui64v;

static void *gl_proc(const char *name) {
  void *p = (void *)wglGetProcAddress(name);
  if (!p || p == (void *)0x1 || p == (void *)0x2 || p == (void *)0x3 || p == (void *)-1) {
    HMODULE mod = GetModuleHandleA("opengl32.dll");
    if (mod) p = (void *)GetProcAddress(mod, name);
  }
  return p;
}

static int load_gl_functions(void) {
  wglSwapIntervalEXT        = (PFNWGLSWAPINTERVALEXTPROC)gl_proc("wglSwapIntervalEXT");
  pglCreateShader           = (PFNGLCREATESHADERPROC)gl_proc("glCreateShader");
  pglShaderSource           = (PFNGLSHADERSOURCEPROC)gl_proc("glShaderSource");
  pglCompileShader          = (PFNGLCOMPILESHADERPROC)gl_proc("glCompileShader");
  pglGetShaderiv            = (PFNGLGETSHADERIVPROC)gl_proc("glGetShaderiv");
  pglGetShaderInfoLog       = (PFNGLGETSHADERINFOLOGPROC)gl_proc("glGetShaderInfoLog");
  pglDeleteShader           = (PFNGLDELETESHADERPROC)gl_proc("glDeleteShader");
  pglCreateProgram          = (PFNGLCREATEPROGRAMPROC)gl_proc("glCreateProgram");
  pglAttachShader           = (PFNGLATTACHSHADERPROC)gl_proc("glAttachShader");
  pglLinkProgram            = (PFNGLLINKPROGRAMPROC)gl_proc("glLinkProgram");
  pglGetProgramiv           = (PFNGLGETPROGRAMIVPROC)gl_proc("glGetProgramiv");
  pglGetProgramInfoLog      = (PFNGLGETPROGRAMINFOLOGPROC)gl_proc("glGetProgramInfoLog");
  pglUseProgram             = (PFNGLUSEPROGRAMPROC)gl_proc("glUseProgram");
  pglGetUniformLocation     = (PFNGLGETUNIFORMLOCATIONPROC)gl_proc("glGetUniformLocation");
  pglUniform1f              = (PFNGLUNIFORM1FPROC)gl_proc("glUniform1f");
  pglUniform1i              = (PFNGLUNIFORM1IPROC)gl_proc("glUniform1i");
  pglUniform2f              = (PFNGLUNIFORM2FPROC)gl_proc("glUniform2f");
  pglUniform2i              = (PFNGLUNIFORM2IPROC)gl_proc("glUniform2i");
  pglUniform3fv             = (PFNGLUNIFORM3FVPROC)gl_proc("glUniform3fv");
  pglUniformMatrix3fv       = (PFNGLUNIFORMMATRIX3FVPROC)gl_proc("glUniformMatrix3fv");
  pglActiveTexture          = (PFNGLACTIVETEXTUREPROC)gl_proc("glActiveTexture");
  pglGenFramebuffers        = (PFNGLGENFRAMEBUFFERSPROC)gl_proc("glGenFramebuffers");
  pglBindFramebuffer        = (PFNGLBINDFRAMEBUFFERPROC)gl_proc("glBindFramebuffer");
  pglFramebufferTexture2D   = (PFNGLFRAMEBUFFERTEXTURE2DPROC)gl_proc("glFramebufferTexture2D");
  pglCheckFramebufferStatus = (PFNGLCHECKFRAMEBUFFERSTATUSPROC)gl_proc("glCheckFramebufferStatus");
  pglDeleteFramebuffers     = (PFNGLDELETEFRAMEBUFFERSPROC)gl_proc("glDeleteFramebuffers");
  pglGenVertexArrays        = (PFNGLGENVERTEXARRAYSPROC)gl_proc("glGenVertexArrays");
  pglBindVertexArray        = (PFNGLBINDVERTEXARRAYPROC)gl_proc("glBindVertexArray");
  pglDispatchCompute        = (PFNGLDISPATCHCOMPUTEPROC)gl_proc("glDispatchCompute");
  pglMemoryBarrier          = (PFNGLMEMORYBARRIERPROC)gl_proc("glMemoryBarrier");
  pglBindImageTexture       = (PFNGLBINDIMAGETEXTUREPROC)gl_proc("glBindImageTexture");
  pglGenQueries             = (PFNGLGENQUERIESPROC)gl_proc("glGenQueries");
  pglBeginQuery             = (PFNGLBEGINQUERYPROC)gl_proc("glBeginQuery");
  pglEndQuery               = (PFNGLENDQUERYPROC)gl_proc("glEndQuery");
  pglGetQueryObjectiv       = (PFNGLGETQUERYOBJECTIVPROC)gl_proc("glGetQueryObjectiv");
  pglGetQueryObjectui64v    = (PFNGLGETQUERYOBJECTUI64VPROC)gl_proc("glGetQueryObjectui64v");

  return (pglCreateShader && pglGenFramebuffers && pglGenVertexArrays &&
          pglDispatchCompute && pglBindImageTexture && pglMemoryBarrier) ? 1 : 0;
}

// ============================================================================
// MATH, VECTOR HELPERS & HALTON(2,3) TAA SEQUENCE
// ============================================================================
#define PI_F 3.14159265359f

static float clampf(float x, float lo, float hi) { return x < lo ? lo : (x > hi ? hi : x); }
static float lerpf(float a, float b, float t) { return a + (b - a) * t; }

static void v3_sub(float out[3], const float a[3], const float b[3]) {
  out[0] = a[0] - b[0]; out[1] = a[1] - b[1]; out[2] = a[2] - b[2];
}
static void v3_add(float out[3], const float a[3], const float b[3]) {
  out[0] = a[0] + b[0]; out[1] = a[1] + b[1]; out[2] = a[2] + b[2];
}
static void v3_scale(float out[3], const float a[3], float s) {
  out[0] = a[0] * s; out[1] = a[1] * s; out[2] = a[2] * s;
}
static float v3_dot(const float a[3], const float b[3]) {
  return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
}
static void v3_cross(float out[3], const float a[3], const float b[3]) {
  float x = a[1] * b[2] - a[2] * b[1];
  float y = a[2] * b[0] - a[0] * b[2];
  float z = a[0] * b[1] - a[1] * b[0];
  out[0] = x; out[1] = y; out[2] = z;
}
static float v3_len(const float a[3]) {
  return sqrtf(a[0] * a[0] + a[1] * a[1] + a[2] * a[2]);
}
static void v3_norm(float out[3], const float a[3]) {
  float l = v3_len(a);
  if (l < 1e-6f) l = 1.0f;
  out[0] = a[0] / l; out[1] = a[1] / l; out[2] = a[2] / l;
}

static void build_camera_basis(float m[9], const float pos[3], const float target[3], float rollRad) {
  float fwd[3], tmp[3], right[3], up[3];
  v3_sub(tmp, target, pos);
  v3_norm(fwd, tmp);
  float worldUp[3] = { 0.0f, 1.0f, 0.0f };
  if (fabsf(v3_dot(fwd, worldUp)) > 0.995f) {
    worldUp[0] = 0.0f; worldUp[1] = 0.0f; worldUp[2] = 1.0f;
  }
  v3_cross(tmp, worldUp, fwd);
  v3_norm(right, tmp);
  v3_cross(up, fwd, right);

  if (fabsf(rollRad) > 1e-5f) {
    float c = cosf(rollRad), s = sinf(rollRad);
    float r2[3], u2[3];
    for (int i = 0; i < 3; i++) {
      r2[i] = right[i] * c + up[i] * s;
      u2[i] = -right[i] * s + up[i] * c;
    }
    memcpy(right, r2, sizeof(r2));
    memcpy(up, u2, sizeof(u2));
  }
  m[0] = right[0]; m[1] = right[1]; m[2] = right[2];
  m[3] = up[0];    m[4] = up[1];    m[5] = up[2];
  m[6] = fwd[0];   m[7] = fwd[1];   m[8] = fwd[2];
}

static float halton_seq(int index, int base) {
  float f = 1.0f, r = 0.0f;
  int i = index;
  while (i > 0) {
    f /= (float)base;
    r += f * (float)(i % base);
    i /= base;
  }
  return r;
}

static float g_halton[16][2];
static void init_halton(void) {
  for (int i = 0; i < 16; i++) {
    g_halton[i][0] = halton_seq(i + 1, 2) - 0.5f;
    g_halton[i][1] = halton_seq(i + 1, 3) - 0.5f;
  }
}

// ============================================================================
// SCENE PRESETS & ENGINE STATE
// ============================================================================
typedef struct {
  const char *name;
  float camPos[3];
  float target[3];
  float sunElev;
  float waterClarity;
  float volumetric;
  float exposure;
} ScenePreset;

static const ScenePreset SCENES[4] = {
  { "01 TIDAL MONOLITH", { 0.0f, 2.35f,  9.8f }, { 0.0f,  1.05f,  0.0f }, 0.34f, 1.05f, 0.85f,  0.00f },
  { "02 FLOODED VAULT",  { 0.0f, 1.55f,  8.6f }, { 0.0f,  1.25f, -2.5f }, 0.62f, 0.85f, 1.35f,  0.10f },
  { "03 EVENT HORIZON",  { 0.0f, 2.15f, 11.5f }, { 0.0f,  0.00f,  0.0f }, 0.25f, 1.00f, 0.70f,  0.05f },
  { "04 CAUSTIC BASIN",  { 5.4f, 3.05f,  6.2f }, { 0.0f, -0.25f,  0.0f }, 0.44f, 1.45f, 0.65f, -0.05f }
};

static const char *FILTER_NAMES[4] = { "CINEMA HDR", "BODYCAM UE5", "ANAMORPHIC", "RAW STUDIO" };
static const char *TM_NAMES[4]     = { "AgX", "ACES", "PBR-N", "HABLE" };
static const char *DBG_NAMES[4]    = { "BEAUTY", "NORMAL", "DEPTH", "WATER" };
static const char *VSYNC_NAMES[3]  = { "UNLIM", "ADAPT-NV", "VSYNC" };

typedef struct {
  int   scene;
  int   filter;
  int   toneMap;
  int   debug;
  int   autoExp;
  int   taa;
  int   split;
  int   cinema;
  int   vsyncMode; // 0 = off, 1 = Adaptive-NV (-1), 2 = On (1)
  float splitPos;
  float renderScale;
  float exposure;
  float sunElev;
  float waterClarity;
  float volumetric;
  float bloom;
  float sharp;
  float chroma;
  float grain;
} EngineState;

static EngineState g_state = {
  0, 0, 0, 0,
  1, 1, 0, 1, 1,
  0.50f, 1.00f,
  0.00f, 0.34f, 1.05f, 0.85f,
  0.55f, 0.48f, 0.65f, 0.35f
};

typedef struct {
  float pos[3], target[3], goalPos[3], goalTarget[3], prevPos[3], prevMat[9];
  float fov, yaw, pitch, dist;
  int   dragging, dragMode, lastX, lastY;
} CameraState;

static CameraState g_cam;

static HWND  g_hwnd = NULL;
static HDC   g_hdc  = NULL;
static HGLRC g_hrc  = NULL;
static int   g_running = 1;
static int   g_keys[256] = {0};
static int   g_winW = 1280, g_winH = 720;
static int   g_renderW = 1280, g_renderH = 720;
static int   g_fullscreen = 0;
static WINDOWPLACEMENT g_wpPrev = { sizeof(WINDOWPLACEMENT) };

static GLuint g_emptyVAO = 0;
static GLuint g_timerQuery[2] = {0, 0};
static int    g_queryIdx = 0;
static int    g_queryReady = 0;
static float  g_gpuMs = 0.0f;
static int    g_hasNvMemInfo = 0;

typedef struct {
  GLuint fbo;
  GLuint tex;
  int w, h;
} RenderTarget;

static RenderTarget g_fboMain     = {0};
static RenderTarget g_fboVol      = {0}; // Half-res RGBA16F Compute Volumetric buffer
static RenderTarget g_fboTAA[2]   = {{0}, {0}};
static RenderTarget g_fboLum[2]   = {{0}, {0}};
static RenderTarget g_fboBloom[2] = {{0}, {0}}; // Packed R11F_G11F_B10F (50% less VRAM bandwidth)
static RenderTarget g_fboStreak[2]= {{0}, {0}};
static int g_taaIdx = 0;
static int g_lumIdx = 0;
static int g_resetHistory = 1;
static int g_resetAdapt = 1;
static int g_needResize = 0;

static void destroy_target(RenderTarget *t) {
  if (t->tex) { glDeleteTextures(1, &t->tex); t->tex = 0; }
  if (t->fbo) { pglDeleteFramebuffers(1, &t->fbo); t->fbo = 0; }
  t->w = t->h = 0;
}

static int create_target(RenderTarget *t, int w, int h, GLenum internalFmt, GLenum fmt, GLenum type, int needFbo) {
  destroy_target(t);
  t->w = w; t->h = h;
  glGenTextures(1, &t->tex);
  glBindTexture(GL_TEXTURE_2D, t->tex);
  glTexImage2D(GL_TEXTURE_2D, 0, internalFmt, w, h, 0, fmt, type, NULL);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_WRAP_T, GL_CLAMP_TO_EDGE);
  if (!needFbo) return 1;

  pglGenFramebuffers(1, &t->fbo);
  pglBindFramebuffer(GL_FRAMEBUFFER, t->fbo);
  pglFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, t->tex, 0);
  GLenum status = pglCheckFramebufferStatus(GL_FRAMEBUFFER);
  pglBindFramebuffer(GL_FRAMEBUFFER, 0);
  return (status == GL_FRAMEBUFFER_COMPLETE) ? 1 : 0;
}

static void rebuild_targets(void) {
  if (g_winW < 1) g_winW = 1;
  if (g_winH < 1) g_winH = 1;

  g_renderW = (int)(g_winW * g_state.renderScale + 0.5f);
  g_renderH = (int)(g_winH * g_state.renderScale + 0.5f);
  if (g_renderW < 160) g_renderW = 160;
  if (g_renderH < 90)  g_renderH = 90;

  int halfW = g_renderW >> 1; if (halfW < 80) halfW = 80;
  int halfH = g_renderH >> 1; if (halfH < 45) halfH = 45;
  int qtrW  = g_renderW >> 2; if (qtrW  < 40) qtrW  = 40;
  int qtrH  = g_renderH >> 2; if (qtrH  < 24) qtrH  = 24;

  create_target(&g_fboMain,   g_renderW, g_renderH, GL_RGBA16F, GL_RGBA, GL_HALF_FLOAT, 1);
  create_target(&g_fboVol,    halfW,     halfH,     GL_RGBA16F, GL_RGBA, GL_HALF_FLOAT, 0);
  create_target(&g_fboTAA[0], g_renderW, g_renderH, GL_RGBA16F, GL_RGBA, GL_HALF_FLOAT, 1);
  create_target(&g_fboTAA[1], g_renderW, g_renderH, GL_RGBA16F, GL_RGBA, GL_HALF_FLOAT, 1);

  // Packed 32-bit R11F_G11F_B10F HDR targets for Bloom & Streaks (halves GDDR6X bandwidth)
  if (!create_target(&g_fboBloom[0], halfW, halfH, GL_R11F_G11F_B10F, GL_RGB, GL_FLOAT, 1)) {
    create_target(&g_fboBloom[0], halfW, halfH, GL_RGBA16F, GL_RGBA, GL_HALF_FLOAT, 1);
    create_target(&g_fboBloom[1], halfW, halfH, GL_RGBA16F, GL_RGBA, GL_HALF_FLOAT, 1);
    create_target(&g_fboStreak[0], qtrW, qtrH, GL_RGBA16F, GL_RGBA, GL_HALF_FLOAT, 1);
    create_target(&g_fboStreak[1], qtrW, qtrH, GL_RGBA16F, GL_RGBA, GL_HALF_FLOAT, 1);
  } else {
    create_target(&g_fboBloom[1],  halfW, halfH, GL_R11F_G11F_B10F, GL_RGB, GL_FLOAT, 1);
    create_target(&g_fboStreak[0], qtrW,  qtrH,  GL_R11F_G11F_B10F, GL_RGB, GL_FLOAT, 1);
    create_target(&g_fboStreak[1], qtrW,  qtrH,  GL_R11F_G11F_B10F, GL_RGB, GL_FLOAT, 1);
  }

  if (!g_fboLum[0].tex) {
    create_target(&g_fboLum[0], 1, 1, GL_RGBA16F, GL_RGBA, GL_HALF_FLOAT, 0);
    create_target(&g_fboLum[1], 1, 1, GL_RGBA16F, GL_RGBA, GL_HALF_FLOAT, 0);
  }
  g_resetHistory = 1;
}
// ============================================================================
// SHADER SOURCES (GLSL 430 CORE — MODULAR CHUNKS FOR MSVC C2026 & MINGW)
// ============================================================================
static const char *VS_QUAD_SRC =
"#version 430 core\n"
"out vec2 vUv;\n"
"void main() {\n"
"  vec2 p = vec2((gl_VertexID << 1) & 2, gl_VertexID & 2);\n"
"  vUv = p;\n"
"  gl_Position = vec4(p * 2.0 - 1.0, 0.0, 1.0);\n"
"}\n";

// --- SHARED MATH, ATMOSPHERE & NOISE-FREE ANALYTICAL SHADOW SDF ---
// Shared by both Pass 1 (Main Raymarcher) and Pass 2 (Volumetric Compute Shader)
static const char *GLSL_COMMON_MATH_SRC =
"const float PI = 3.14159265359;\n"
"const float TAU = 6.28318530718;\n"
"const float MAX_DIST = 110.0;\n"
"\n"
"float ign(vec2 p, int frame) {\n"
"  vec2 q = p + float(frame & 63) * vec2(5.588238, 7.129413);\n"
"  return fract(52.9829189 * fract(dot(q, vec2(0.06711056, 0.00583715))));\n"
"}\n"
"float hash12(vec2 p) {\n"
"  vec3 p3 = fract(vec3(p.xyx) * 0.1031);\n"
"  p3 += dot(p3, p3.yzx + 33.33);\n"
"  return fract((p3.x + p3.y) * p3.z);\n"
"}\n"
"float hash13(vec3 p3) {\n"
"  p3 = fract(p3 * 0.1031);\n"
"  p3 += dot(p3, p3.zyx + 31.32);\n"
"  return fract((p3.x + p3.y) * p3.z);\n"
"}\n"
"vec3 hash33(vec3 p3) {\n"
"  p3 = fract(p3 * vec3(0.1031, 0.1030, 0.0973));\n"
"  p3 += dot(p3, p3.yxz + 33.33);\n"
"  return fract((p3.xxy + p3.yxx) * p3.zyx);\n"
"}\n"
"float vnoise2(vec2 p) {\n"
"  vec2 i = floor(p), f = fract(p);\n"
"  vec2 u = f * f * (3.0 - 2.0 * f);\n"
"  return mix(\n"
"    mix(hash12(i + vec2(0.0, 0.0)), hash12(i + vec2(1.0, 0.0)), u.x),\n"
"    mix(hash12(i + vec2(0.0, 1.0)), hash12(i + vec2(1.0, 1.0)), u.x),\n"
"    u.y\n"
"  );\n"
"}\n"
"float vnoise3(vec3 p) {\n"
"  vec3 i = floor(p), f = fract(p);\n"
"  vec3 u = f * f * (3.0 - 2.0 * f);\n"
"  float n000 = hash13(i + vec3(0,0,0)), n100 = hash13(i + vec3(1,0,0));\n"
"  float n010 = hash13(i + vec3(0,1,0)), n110 = hash13(i + vec3(1,1,0));\n"
"  float n001 = hash13(i + vec3(0,0,1)), n101 = hash13(i + vec3(1,0,1));\n"
"  float n011 = hash13(i + vec3(0,1,1)), n111 = hash13(i + vec3(1,1,1));\n"
"  return mix(\n"
"    mix(mix(n000, n100, u.x), mix(n010, n110, u.x), u.y),\n"
"    mix(mix(n001, n101, u.x), mix(n011, n111, u.x), u.y),\n"
"    u.z\n"
"  );\n"
"}\n"
"float fbm2(vec2 p) {\n"
"  float v = 0.0, a = 0.5;\n"
"  mat2 m = mat2(0.80, 0.60, -0.60, 0.80);\n"
"  for (int i = 0; i < 4; i++) {\n"
"    v += a * vnoise2(p);\n"
"    p = m * p * 2.03 + vec2(17.1, 31.7);\n"
"    a *= 0.5;\n"
"  }\n"
"  return v;\n"
"}\n"
"float fbm3(vec3 p) {\n"
"  float v = 0.0, a = 0.5;\n"
"  for (int i = 0; i < 4; i++) {\n"
"    v += a * vnoise3(p);\n"
"    p = p * 2.02 + vec3(13.7, 29.3, 7.1);\n"
"    a *= 0.5;\n"
"  }\n"
"  return v;\n"
"}\n"
"float triplanarNoise(vec3 p, vec3 n, float scale) {\n"
"  vec3 w = pow(abs(n), vec3(4.0));\n"
"  w /= max(w.x + w.y + w.z, 1e-4);\n"
"  return fbm2(p.yz * scale) * w.x + fbm2(p.xz * scale) * w.y + fbm2(p.xy * scale) * w.z;\n"
"}\n"
"mat2 rot2(float a) { float c = cos(a), s = sin(a); return mat2(c, -s, s, c); }\n"
"\n"
"float sdSphere(vec3 p, float r) { return length(p) - r; }\n"
"float sdBox(vec3 p, vec3 b) {\n"
"  vec3 q = abs(p) - b;\n"
"  return length(max(q, 0.0)) + min(max(q.x, max(q.y, q.z)), 0.0);\n"
"}\n"
"float sdRoundBox(vec3 p, vec3 b, float r) {\n"
"  vec3 q = abs(p) - b;\n"
"  return length(max(q, 0.0)) + min(max(q.x, max(q.y, q.z)), 0.0) - r;\n"
"}\n"
"float sdCylinder(vec3 p, float r, float h) {\n"
"  vec2 d = abs(vec2(length(p.xz), p.y)) - vec2(r, h);\n"
"  return min(max(d.x, d.y), 0.0) + length(max(d, 0.0));\n"
"}\n"
"float smin(float a, float b, float k) {\n"
"  float h = clamp(0.5 + 0.5 * (b - a) / k, 0.0, 1.0);\n"
"  return mix(b, a, h) - k * h * (1.0 - h);\n"
"}\n"
"vec2 opU(vec2 a, vec2 b) { return (a.x < b.x) ? a : b; }\n"
"\n"
"vec3 getSunDir() {\n"
"  float elev = clamp(uSunElev, 0.05, 1.35);\n"
"  float az = (uScene == 1) ? 0.42 : (uScene == 3 ? -0.68 : -0.45);\n"
"  return normalize(vec3(sin(az) * cos(elev), sin(elev), -cos(az) * cos(elev)));\n"
"}\n"
"vec3 getSunRadiance(vec3 sunDir) {\n"
"  float mu = clamp(sunDir.y, 0.02, 1.0);\n"
"  float airmass = 1.0 / (mu + 0.15 * pow(max(mu * 90.0 + 3.885, 0.1), -1.253));\n"
"  vec3 ext = exp(-vec3(0.085, 0.19, 0.44) * airmass * 0.65);\n"
"  return vec3(13.5, 12.2, 10.6) * ext;\n"
"}\n"
"float hgPhase(float cosTheta, float g) {\n"
"  float g2 = g * g;\n"
"  float denom = max(1.0 + g2 - 2.0 * g * cosTheta, 1e-3);\n"
"  return (1.0 - g2) / (4.0 * PI * denom * sqrt(denom));\n"
"}\n"
"\n"
"// Fast Analytical Shadow SDF (zero 3D noise cost -> ~2.5x faster shadows & god rays)\n"
"float mapWorld0Shadow(vec3 p) {\n"
"  float r = length(p.xz);\n"
"  float d = p.y - (-1.35 + 0.55 * exp(-r * 0.18));\n"
"  if (r < 4.5 && p.y < 0.2) {\n"
"    d = min(d, min(sdCylinder(p - vec3(0.0, -0.78, 0.0), 3.6, 0.34) - 0.05,\n"
"                   sdCylinder(p - vec3(0.0, -0.42, 0.0), 2.35, 0.22) - 0.04));\n"
"  }\n"
"  if (abs(r - 4.2) < 2.2 && p.y < 1.2) {\n"
"    for (int i = 0; i < 6; i++) {\n"
"      float ang = float(i) * (TAU / 6.0) + 0.35;\n"
"      float rad = 4.2 + 0.9 * sin(float(i) * 2.1);\n"
"      vec3 q = p - vec3(cos(ang) * rad, -0.95, sin(ang) * rad);\n"
"      q.xz = rot2(ang) * q.xz;\n"
"      d = min(d, sdRoundBox(q, vec3(0.55, (i % 2 == 0) ? 0.62 : 1.15, 0.55), 0.08));\n"
"    }\n"
"  }\n"
"  vec3 pm = p - vec3(0.0, 1.35, 0.0);\n"
"  vec3 monoSize = vec3(0.95 - pm.y * 0.045, 2.75, 0.58 - pm.y * 0.025);\n"
"  float dMono = max(sdRoundBox(pm, max(monoSize, vec3(0.25)), 0.05),\n"
"                    -sdBox(pm - vec3(0.0, 0.35, 0.0), vec3(0.11, 1.85, 0.85)));\n"
"  d = min(d, dMono);\n"
"  vec3 pp = vec3(abs(p.x) - 2.95, p.y, p.z + 0.65);\n"
"  float dPylon = max(sdRoundBox(pp - vec3(0.0, 0.65, 0.0), vec3(0.36, 1.85, 0.42), 0.04),\n"
"                     -sdBox(pp - vec3(0.0, 1.1, 0.0), vec3(0.5, 0.22, 0.18)));\n"
"  return min(d, dPylon);\n"
"}\n"
"\n"
"float mapWorld1Shadow(vec3 p) {\n"
"  float dCavity = sdBox(p - vec3(0.0, 2.44, -0.5), vec3(5.0, 2.76, 13.5));\n"
"  float dArch = length(vec2(p.x, p.y - 3.6)) - 5.1;\n"
"  float dWalls = -max(dCavity, min(p.y - 3.6, dArch));\n"
"  float zRep = mod(p.z + 3.0, 6.0) - 3.0;\n"
"  if (abs(p.z + 1.0) < 10.5) {\n"
"    dWalls = max(dWalls, -sdBox(vec3(p.x, p.y - 5.8, zRep), vec3(1.55, 1.8, 1.15)));\n"
"  }\n"
"  vec3 pr = vec3(abs(p.x) - 3.65, p.y, zRep);\n"
"  float dPillar = sdRoundBox(pr - vec3(0.0, 2.2, 0.0), vec3(0.52, 2.9, 0.48), 0.04);\n"
"  float dBeam   = sdBox(vec3(p.x, p.y - 4.55, zRep), vec3(5.2, 0.38, 0.42));\n"
"  float dBack   = sdRoundBox(p - vec3(0.0, 1.9, -12.8), vec3(2.8, 2.5, 0.9), 0.06);\n"
"  return min(dWalls, min(dPillar, min(dBeam, dBack)));\n"
"}\n"
"\n"
"float mapWorld3Shadow(vec3 p) {\n"
"  float dBasin = max(p.y - 0.52, -min(sdBox(p - vec3(0.0, 0.05, 0.0), vec3(5.2, 1.40, 5.2)),\n"
"                                      sdBox(p - vec3(0.0, -0.35, 0.0), vec3(4.35, 0.98, 4.35))));\n"
"  float wallRing = max(sdBox(p - vec3(0.0, 2.1, 0.0), vec3(8.2, 2.6, 8.2)),\n"
"                      -sdBox(p - vec3(0.0, 2.2, 0.0), vec3(6.8, 3.0, 6.8)));\n"
"  vec3 aw = vec3(mod(p.x + 1.5, 3.0) - 1.5, p.y - 2.35, mod(p.z + 1.5, 3.0) - 1.5);\n"
"  wallRing = max(wallRing, -min(sdRoundBox(vec3(p.x, aw.y, aw.z), vec3(9.0, 0.95, 0.72), 0.35),\n"
"                                sdRoundBox(vec3(aw.x, aw.y, p.z), vec3(0.72, 0.95, 9.0), 0.35)));\n"
"  vec3 cp = vec3(abs(p.x) - 3.6, p.y, abs(p.z) - 3.6);\n"
"  float dPier = sdRoundBox(cp - vec3(0.0, -0.15, 0.0), vec3(0.55, 1.35, 0.55), 0.05);\n"
"  float dOrb  = sdSphere(p - vec3(0.0, 0.08 + sin(uTime * 0.8) * 0.06, 0.0), 0.82);\n"
"  return min(min(dBasin, wallRing), min(dPier, dOrb));\n"
"}\n"
"\n"
"float mapSolidShadow(vec3 p) {\n"
"  if (uScene == 0) return mapWorld0Shadow(p);\n"
"  if (uScene == 1) return mapWorld1Shadow(p);\n"
"  return mapWorld3Shadow(p);\n"
"}\n"
"\n"
"float calcFastShadow(vec3 ro, vec3 rd, float tMax) {\n"
"  float t = 0.08;\n"
"  for (int i = 0; i < 24; i++) {\n"
"    float h = mapSolidShadow(ro + rd * t);\n"
"    if (h < 0.012) return 0.0;\n"
"    t += max(h * 0.88, 0.11);\n"
"    if (t > tMax) break;\n"
"  }\n"
"  return 1.0;\n"
"}\n";

// --- PASS 1 HEADER ---
static const char *FS_MAIN_HEADER_SRC =
"#version 430 core\n"
"in vec2 vUv;\n"
"layout(location = 0) out vec4 outColor;\n"
"uniform vec2  uResolution;\n"
"uniform float uTime;\n"
"uniform int   uFrame;\n"
"uniform int   uScene;\n"
"uniform int   uDebug;\n"
"uniform vec3  uCamPos;\n"
"uniform mat3  uCamMat;\n"
"uniform vec2  uJitter;\n"
"uniform float uFov;\n"
"uniform float uSunElev;\n"
"uniform float uWaterClarity;\n"
"uniform float uVolumetric;\n"
"uniform float uAudioBass;\n"
"uniform float uAudioMid;\n"
"uniform float uAudioHigh;\n";

// --- PASS 1B: SKY, GGX PBR, WATER OPTICS, BOUNDING-ACCELERATED WORLDS & MATERIALS ---
static const char *FS_MAIN_WORLDS_SRC =
"vec3 evalSkyHDR(vec3 rd, vec3 sunDir, bool includeDisk) {\n"
"  float y = max(rd.y, 0.001);\n"
"  float sunMu = dot(rd, sunDir);\n"
"  float sunY = max(sunDir.y, 0.03);\n"
"  float zenithDepth = 1.0 / (y + 0.14);\n"
"  float sunDepth = 1.0 / (sunY + 0.14);\n"
"  vec3 betaR = vec3(5.8e-3, 13.5e-3, 33.1e-3) * 14.0;\n"
"  vec3 betaM = vec3(0.028);\n"
"  vec3 sunTrans = exp(-(betaR * sunDepth * 0.25 + betaM * sunDepth * 0.35));\n"
"  float rayleighPhase = 0.75 * (1.0 + sunMu * sunMu);\n"
"  float miePhase = hgPhase(sunMu, 0.78) * 0.85 + hgPhase(sunMu, 0.35) * 0.25;\n"
"  vec3 inScatterR = betaR * rayleighPhase * (1.0 - exp(-zenithDepth * 0.45));\n"
"  vec3 inScatterM = betaM * miePhase * (1.0 - exp(-zenithDepth * 0.65)) * 12.0;\n"
"  vec3 sky = (inScatterR * 1.45 + inScatterM) * sunTrans * 3.8;\n"
"  vec3 horizonCol = mix(vec3(0.45, 0.56, 0.72), vec3(0.95, 0.55, 0.32), pow(1.0 - sunY, 3.0));\n"
"  sky = mix(horizonCol * (0.45 + 0.55 * sunY), sky, smoothstep(0.0, 0.26, y));\n"
"  if (rd.y > 0.015 && uScene != 2) {\n"
"    vec2 cloudUv = rd.xz / (rd.y + 0.16) * 0.85 + vec2(uTime * 0.012, -uTime * 0.007);\n"
"    float c1 = fbm2(cloudUv * 1.4);\n"
"    float c2 = fbm2(cloudUv * 3.2 + vec2(c1 * 1.3));\n"
"    float cloud = smoothstep(0.47, 0.78, c1 * 0.65 + c2 * 0.35) * smoothstep(0.015, 0.22, rd.y);\n"
"    float forwardLit = 0.45 + 1.65 * pow(max(sunMu, 0.0), 5.0);\n"
"    vec3 cloudCol = mix(vec3(0.28, 0.34, 0.44), getSunRadiance(sunDir) * 0.24 * forwardLit, 0.78);\n"
"    sky = mix(sky, cloudCol, cloud * 0.55);\n"
"  }\n"
"  if (includeDisk) {\n"
"    float disk = smoothstep(0.99945, 0.99985, sunMu);\n"
"    float corona = pow(max(sunMu, 0.0), 64.0) * 1.35 + pow(max(sunMu, 0.0), 512.0) * 6.5;\n"
"    sky += getSunRadiance(sunDir) * (disk * 14.0 + corona * 0.35) * smoothstep(-0.02, 0.05, rd.y);\n"
"  }\n"
"  if (rd.y < 0.0) {\n"
"    sky = mix(sky, horizonCol * 0.16 * (0.35 + 0.65 * sunY), smoothstep(0.0, -0.18, rd.y));\n"
"  }\n"
"  return max(sky, vec3(0.0));\n"
"}\n"
"\n"
"float D_GGX(float NoH, float a) {\n"
"  float a2 = a * a;\n"
"  float d = (NoH * NoH) * (a2 - 1.0) + 1.0;\n"
"  return a2 / (PI * d * d + 1e-6);\n"
"}\n"
"float V_SmithGGX(float NoV, float NoL, float a) {\n"
"  float a2 = a * a;\n"
"  float ggxV = NoL * sqrt(NoV * NoV * (1.0 - a2) + a2);\n"
"  float ggxL = NoV * sqrt(NoL * NoL * (1.0 - a2) + a2);\n"
"  return 0.5 / max(ggxV + ggxL, 1e-5);\n"
"}\n"
"vec3 F_Schlick(float VoH, vec3 F0) { return F0 + (1.0 - F0) * pow(1.0 - clamp(VoH, 0.0, 1.0), 5.0); }\n"
"vec3 F_SchlickRough(float NoV, vec3 F0, float rough) {\n"
"  return F0 + (max(vec3(1.0 - rough), F0) - F0) * pow(1.0 - clamp(NoV, 0.0, 1.0), 5.0);\n"
"}\n"
"vec3 evalDirectPBR(vec3 N, vec3 V, vec3 L, vec3 albedo, float rough, float metal, vec3 radiance) {\n"
"  float NoL = max(dot(N, L), 0.0);\n"
"  if (NoL <= 0.0) return vec3(0.0);\n"
"  float NoV = max(dot(N, V), 1e-4);\n"
"  vec3 H = normalize(V + L);\n"
"  float a = max(rough * rough, 0.0025);\n"
"  vec3 F0 = mix(vec3(0.04), albedo, metal);\n"
"  vec3 F = F_Schlick(max(dot(V, H), 0.0), F0);\n"
"  vec3 spec = D_GGX(max(dot(N, H), 0.0), a) * V_SmithGGX(NoV, NoL, a) * F * (1.0 + F0 * (rough * 0.42));\n"
"  return ((1.0 - F) * (1.0 - metal) * albedo / PI + spec) * radiance * NoL;\n"
"}\n"
"\n"
"bool sceneHasWater(int sceneId) { return (sceneId == 0 || sceneId == 1 || sceneId == 3); }\n"
"float getWaterBaseY(int sceneId) { return (sceneId == 0 || sceneId == 1 || sceneId == 3) ? 0.0 : -999.0; }\n"
"\n"
"float waterHeight(vec2 xz, float t, int sceneId) {\n"
"  if (sceneId == 1) {\n"
"    return sin(dot(xz, vec2(2.3, 1.7)) + t * 1.4) * 0.007\n"
"         + sin(dot(xz, vec2(-1.9, 3.1)) - t * 1.9) * 0.005\n"
"         + (vnoise2(xz * 2.8 + vec2(t * 0.35, -t * 0.25)) - 0.5) * 0.009;\n"
"  }\n"
"  if (sceneId == 3) {\n"
"    float r = length(xz);\n"
"    return sin(dot(xz, vec2(1.8, 1.2)) + t * 1.5) * 0.016\n"
"         + sin(dot(xz, vec2(-1.4, 2.4)) - t * 1.8) * 0.012\n"
"         + sin(r * 3.8 - t * 2.4) * exp(-r * 0.22) * (0.015 + 0.012 * uAudioBass)\n"
"         + (vnoise2(xz * 3.6 + vec2(t * 0.45, t * 0.3)) - 0.5) * 0.012;\n"
"  }\n"
"  vec2 p = xz;\n"
"  return sin(dot(p, vec2(0.75, 0.52)) + t * 1.35) * 0.068\n"
"       + sin(dot(p, vec2(-0.48, 0.96)) + t * 1.75) * 0.044\n"
"       + sin(dot(p, vec2(1.42, -1.18)) - t * 2.15) * 0.022\n"
"       + sin(dot(p, vec2(-2.15, -1.35)) + t * 2.65) * 0.011\n"
"       + (fbm2(p * 1.45 + vec2(t * 0.42, -t * 0.31)) - 0.5) * 0.036;\n"
"}\n"
"vec3 waterNormal(vec2 xz, float t, int sceneId, float dist) {\n"
"  float eps = mix(0.018, 0.09, clamp(dist / 55.0, 0.0, 1.0));\n"
"  float hC = waterHeight(xz, t, sceneId);\n"
"  float hX = waterHeight(xz + vec2(eps, 0.0), t, sceneId);\n"
"  float hZ = waterHeight(xz + vec2(0.0, eps), t, sceneId);\n"
"  float microFade = 1.0 - smoothstep(4.0, 26.0, dist);\n"
"  if (microFade > 0.01) {\n"
"    float mEps = 0.008, mScale = (sceneId == 1) ? 7.5 : 5.2, mAmp = (sceneId == 1) ? 0.0035 : 0.009;\n"
"    vec2 drift = vec2(t * 0.55, -t * 0.42);\n"
"    float mC = vnoise2(xz * mScale + drift);\n"
"    hX += (vnoise2((xz + vec2(mEps, 0.0)) * mScale + drift) - mC) * mAmp * microFade * (eps / mEps);\n"
"    hZ += (vnoise2((xz + vec2(0.0, mEps)) * mScale + drift) - mC) * mAmp * microFade * (eps / mEps);\n"
"  }\n"
"  return normalize(vec3(hC - hX, eps, hC - hZ));\n"
"}\n"
"float evalCaustics(vec3 subPos, vec3 sunDir, float t, int sceneId) {\n"
"  float depth = max(getWaterBaseY(sceneId) - subPos.y, 0.0);\n"
"  if (depth <= 0.002) return 0.0;\n"
"  vec3 refrSun = refract(-sunDir, vec3(0.0, 1.0, 0.0), 1.0 / 1.333);\n"
"  vec2 surfXZ = subPos.xz - refrSun.xz * (depth / max(-refrSun.y, 0.15));\n"
"  vec2 uv1 = surfXZ * (sceneId == 3 ? 1.55 : 0.95);\n"
"  vec2 p1 = uv1 + vec2(t * 0.28, -t * 0.21);\n"
"  vec2 p2 = uv1 * 1.48 - vec2(t * 0.22, t * 0.31);\n"
"  float e = 0.14;\n"
"  float h00 = waterHeight(p1, t, sceneId);\n"
"  float lap1 = abs((waterHeight(p1 + vec2(e, 0.0), t, sceneId) + waterHeight(p1 + vec2(0.0, e), t, sceneId) - 2.0 * h00) / (e * e));\n"
"  vec2 wA = sin(p1 * 2.4 + cos(p1.yx * 2.1 + t * 1.2));\n"
"  vec2 wB = sin(p2 * 2.7 - cos(p2.yx * 2.3 - t * 1.4));\n"
"  float caustic = pow(clamp(1.0 - abs(wA.x * wA.y), 0.0, 1.0), 6.0)\n"
"                + pow(clamp(1.0 - abs(wB.x * wB.y), 0.0, 1.0), 6.0) * 0.8;\n"
"  caustic = caustic * 0.85 + smoothstep(0.15, 1.4, lap1) * 0.45;\n"
"  return clamp(caustic * smoothstep(0.01, 0.18, depth) * exp(-depth * 0.26) * 1.75, 0.0, 3.2);\n"
"}\n"
"\n"
"vec2 mapWorld0(vec3 p) {\n"
"  float r = length(p.xz);\n"
"  float floorBase = -1.35 + 0.55 * exp(-r * 0.18);\n"
"  float reefUndul = (r < 34.0) ? ((fbm2(p.xz * 0.24) - 0.5) * 0.65 + (vnoise2(p.xz * 1.1) - 0.5) * 0.14) : 0.0;\n"
"  float dGround = p.y - (floorBase + reefUndul);\n"
"  if (r < 4.8 && p.y < 0.35) {\n"
"    float t1 = sdCylinder(p - vec3(0.0, -0.78, 0.0), 3.6, 0.34) - 0.05;\n"
"    float t2 = sdCylinder(p - vec3(0.0, -0.42, 0.0), 2.35, 0.22) - 0.04;\n"
"    dGround = smin(dGround, min(t1, t2), 0.16);\n"
"  }\n"
"  if (abs(r - 4.2) < 2.2 && p.y < 1.35) {\n"
"    float dRocks = 1e5;\n"
"    for (int i = 0; i < 6; i++) {\n"
"      float ang = float(i) * (TAU / 6.0) + 0.35;\n"
"      float rad = 4.2 + 0.9 * sin(float(i) * 2.1);\n"
"      vec3 q = p - vec3(cos(ang) * rad, -0.95, sin(ang) * rad);\n"
"      q.xz = rot2(ang) * q.xz;\n"
"      dRocks = min(dRocks, sdRoundBox(q, vec3(0.55, (i % 2 == 0) ? 0.62 : 1.15, 0.55), 0.08));\n"
"    }\n"
"    if (dRocks < 0.25) dRocks += (vnoise3(p * 2.2) - 0.5) * 0.06;\n"
"    dGround = smin(dGround, dRocks, 0.18);\n"
"  }\n"
"  vec2 res = vec2(dGround, 1.0);\n"
"  vec3 pm = p - vec3(0.0, 1.35, 0.0);\n"
"  vec3 monoSize = vec3(0.95 - pm.y * 0.045, 2.75, 0.58 - pm.y * 0.025);\n"
"  float dMono = sdRoundBox(pm, max(monoSize, vec3(0.25)), 0.05);\n"
"  dMono = max(dMono, -sdBox(pm - vec3(0.0, 0.35, 0.0), vec3(0.11, 1.85, 0.85))) + abs(sin(pm.y * 5.2)) * 0.015;\n"
"  res = opU(res, vec2(dMono, 2.0));\n"
"  res = opU(res, vec2(sdRoundBox(pm - vec3(0.0, 0.35, 0.0), vec3(0.055, 1.72, 0.22), 0.02), 3.0));\n"
"  vec3 pp = vec3(abs(p.x) - 2.95, p.y, p.z + 0.65);\n"
"  float dPylon = max(sdRoundBox(pp - vec3(0.0, 0.65, 0.0), vec3(0.36, 1.85, 0.42), 0.04),\n"
"                     -sdBox(pp - vec3(0.0, 1.1, 0.0), vec3(0.5, 0.22, 0.18)));\n"
"  return opU(res, vec2(dPylon, 1.0));\n"
"}\n"
"\n"
"vec2 mapWorld1(vec3 p) {\n"
"  float dCavity = sdBox(p - vec3(0.0, 2.44, -0.5), vec3(5.0, 2.76, 13.5));\n"
"  float dArch = length(vec2(p.x, p.y - 3.6)) - 5.1;\n"
"  float dWalls = -max(dCavity, min(p.y - 3.6, dArch));\n"
"  float zRep = mod(p.z + 3.0, 6.0) - 3.0;\n"
"  if (abs(p.z + 1.0) < 10.5) {\n"
"    dWalls = max(dWalls, -sdBox(vec3(p.x, p.y - 5.8, zRep), vec3(1.55, 1.8, 1.15)));\n"
"  }\n"
"  vec3 pr = vec3(abs(p.x) - 3.65, p.y, zRep);\n"
"  float dPillar = sdRoundBox(pr - vec3(0.0, 2.2, 0.0), vec3(0.52, 2.9, 0.48), 0.04);\n"
"  float dPlinth = sdRoundBox(pr - vec3(0.0, -0.05, 0.0), vec3(0.72, 0.34, 0.68), 0.03);\n"
"  float dBeam   = sdBox(vec3(p.x, p.y - 4.55, zRep), vec3(5.2, 0.38, 0.42));\n"
"  float dBackWall = max(sdRoundBox(p - vec3(0.0, 1.9, -12.8), vec3(2.8, 2.5, 0.9), 0.06),\n"
"                        -sdBox(p - vec3(0.0, 1.4, -12.0), vec3(1.35, 1.85, 0.55)));\n"
"  float dConcrete = min(dWalls, min(min(dPillar, dPlinth), min(dBeam, dBackWall)));\n"
"  if (dConcrete < 0.12) dConcrete += (vnoise3(p * 3.5) - 0.5) * 0.008;\n"
"  vec2 res = vec2(dConcrete, 4.0);\n"
"  float dWalkway = sdBox(p - vec3(0.0, -0.22, -0.5), vec3(1.45, 0.08, 12.2));\n"
"  if (dWalkway < 0.1) dWalkway += smoothstep(0.2, 0.6, sin(p.z * 14.0) * sin(p.x * 14.0)) * 0.014;\n"
"  res = opU(res, vec2(dWalkway, 5.0));\n"
"  vec3 pipeP = vec3(abs(p.x) - 4.65, p.y - 2.65, p.z);\n"
"  res = opU(res, vec2(length(pipeP.xy) - 0.11, 5.0));\n"
"  vec3 lampP = vec3(abs(p.x) - 3.12, p.y - 2.15, zRep);\n"
"  return opU(res, vec2(sdRoundBox(lampP, vec3(0.06, 0.24, 0.11), 0.02), 3.0));\n"
"}\n"
"\n"
"vec2 mapWorld2(vec3 p) { return vec2(length(p) - 1.5, 2.0); }\n"
"\n"
"vec2 mapWorld3(vec3 p) {\n"
"  float dBasin = max(p.y - 0.52, -min(sdBox(p - vec3(0.0, 0.05, 0.0), vec3(5.2, 1.40, 5.2)),\n"
"                                      sdBox(p - vec3(0.0, -0.35, 0.0), vec3(4.35, 0.98, 4.35))));\n"
"  float wallRing = max(sdBox(p - vec3(0.0, 2.1, 0.0), vec3(8.2, 2.6, 8.2)),\n"
"                      -sdBox(p - vec3(0.0, 2.2, 0.0), vec3(6.8, 3.0, 6.8)));\n"
"  vec3 aw = vec3(mod(p.x + 1.5, 3.0) - 1.5, p.y - 2.35, mod(p.z + 1.5, 3.0) - 1.5);\n"
"  wallRing = max(wallRing, -min(sdRoundBox(vec3(p.x, aw.y, aw.z), vec3(9.0, 0.95, 0.72), 0.35),\n"
"                                sdRoundBox(vec3(aw.x, aw.y, p.z), vec3(0.72, 0.95, 9.0), 0.35)));\n"
"  float dSub = min(sdRoundBox(p - vec3(0.0, -1.05, 0.0), vec3(2.2, 0.32, 2.2), 0.06),\n"
"                   sdRoundBox(p - vec3(0.0, -1.22, 0.0), vec3(3.1, 0.18, 3.1), 0.05));\n"
"  vec3 cp = vec3(abs(p.x) - 3.6, p.y, abs(p.z) - 3.6);\n"
"  float dStone = min(min(dBasin, wallRing), min(dSub, sdRoundBox(cp - vec3(0.0, -0.15, 0.0), vec3(0.55, 1.35, 0.55), 0.05)));\n"
"  if (dStone < 0.12) dStone += (vnoise3(p * 2.8) - 0.5) * 0.008;\n"
"  vec2 res = vec2(dStone, 6.0);\n"
"  res = opU(res, vec2(sdSphere(p - vec3(0.0, 0.08 + sin(uTime * 0.8) * 0.06, 0.0), 0.82), 5.0));\n"
"  float dOrbs = min(min(sdSphere(p - vec3(-2.35, -0.82,  1.85), 0.48), sdSphere(p - vec3( 2.45, -0.88, -1.65), 0.42)),\n"
"                    min(sdSphere(p - vec3( 1.85, -0.78,  2.25), 0.36), sdSphere(p - vec3(-1.95, -0.76, -2.15), 0.40)));\n"
"  return opU(res, vec2(dOrbs, 7.0));\n"
"}\n"
"\n"
"vec2 mapSolid(vec3 p) {\n"
"  if (uScene == 0) return mapWorld0(p);\n"
"  if (uScene == 1) return mapWorld1(p);\n"
"  if (uScene == 2) return mapWorld2(p);\n"
"  return mapWorld3(p);\n"
"}\n"
"\n"
"vec3 calcNormal(vec3 p, float t) {\n"
"  float e = max(0.0012, 0.00055 * t);\n"
"  vec2 k = vec2(1.0, -1.0);\n"
"  return normalize(\n"
"    k.xyy * mapSolid(p + k.xyy * e).x + k.yyx * mapSolid(p + k.yyx * e).x +\n"
"    k.yxy * mapSolid(p + k.yxy * e).x + k.xxx * mapSolid(p + k.xxx * e).x\n"
"  );\n"
"}\n"
"\n"
"struct Material { vec3 albedo; float rough; float metal; vec3 emissive; vec3 normalMod; };\n"
"\n"
"Material evalMaterial(vec3 p, vec3 N, float matId) {\n"
"  Material m;\n"
"  m.albedo = vec3(0.45); m.rough = 0.65; m.metal = 0.0; m.emissive = vec3(0.0); m.normalMod = N;\n"
"  float nLow  = triplanarNoise(p, N, 0.65);\n"
"  float nMid  = triplanarNoise(p, N, 2.60);\n"
"  float nHigh = triplanarNoise(p, N, 9.50);\n"
"  if (matId < 1.5) {\n"
"    m.albedo = mix(vec3(0.065, 0.072, 0.082), vec3(0.14, 0.145, 0.15), nLow * 0.7 + nMid * 0.3);\n"
"    float moss = smoothstep(0.55, 0.88, N.y) * smoothstep(0.48, 0.72, nLow) * smoothstep(0.18, 0.75, p.y);\n"
"    m.albedo = mix(m.albedo, vec3(0.08, 0.12, 0.06), moss * 0.55);\n"
"    m.rough = clamp(0.58 + (nHigh - 0.5) * 0.35, 0.25, 0.92); m.metal = 0.02;\n"
"  } else if (matId < 2.5) {\n"
"    float striations = sin(p.y * 28.0 + nMid * 3.0) * 0.5 + 0.5;\n"
"    m.albedo = mix(vec3(0.03, 0.034, 0.042), vec3(0.075, 0.085, 0.105), striations * 0.4 + nHigh * 0.3);\n"
"    m.rough = clamp(0.16 + nHigh * 0.22, 0.08, 0.45); m.metal = 0.35;\n"
"  } else if (matId < 3.5) {\n"
"    float pulse = 1.0 + 0.18 * uAudioMid;\n"
"    m.albedo = vec3(0.95, 0.82, 0.65); m.rough = 0.2;\n"
"    m.emissive = (uScene == 1) ? vec3(15.5, 6.4, 1.8) * pulse : vec3(2.8, 9.5, 14.5) * pulse;\n"
"  } else if (matId < 4.5) {\n"
"    float stain = smoothstep(0.35, 0.8, fbm2(p.xz * 0.55 + vec2(p.y * 0.2)));\n"
"    float seam = smoothstep(0.96, 1.0, abs(sin(p.y * PI * 1.1))) * 0.18;\n"
"    m.albedo = mix(vec3(0.22, 0.225, 0.22), vec3(0.09, 0.095, 0.092), stain * 0.65 + seam) * (0.82 + 0.36 * nHigh);\n"
"    m.rough = clamp(0.68 + (nMid - 0.5) * 0.34 - seam * 0.2, 0.32, 0.95);\n"
"  } else if (matId < 5.5) {\n"
"    m.albedo = (uScene == 3) ? mix(vec3(0.72, 0.54, 0.34), vec3(0.84, 0.72, 0.52), nHigh)\n"
"                             : mix(vec3(0.16, 0.14, 0.12), vec3(0.34, 0.22, 0.14), nMid);\n"
"    m.rough = (uScene == 3) ? clamp(0.14 + nHigh * 0.16, 0.06, 0.35) : clamp(0.38 + nHigh * 0.35, 0.18, 0.82);\n"
"    m.metal = (uScene == 3) ? 0.92 : 0.78;\n"
"  } else if (matId < 6.5) {\n"
"    float strata = sin(p.y * 11.0 + nLow * 4.0) * 0.5 + 0.5;\n"
"    m.albedo = mix(vec3(0.46, 0.42, 0.35), vec3(0.62, 0.57, 0.48), strata * 0.55 + nMid * 0.35) * (0.85 + 0.25 * nHigh);\n"
"    m.rough = clamp(0.56 + (nHigh - 0.5) * 0.30, 0.28, 0.88);\n"
"  } else {\n"
"    float vein = smoothstep(0.62, 0.92, sin(p.x * 5.0 + p.z * 4.0 + nMid * 5.5) * 0.5 + 0.5);\n"
"    m.albedo = mix(vec3(0.68, 0.67, 0.64), vec3(0.26, 0.28, 0.31), vein * 0.55);\n"
"    m.rough = clamp(0.15 + nHigh * 0.12, 0.08, 0.32);\n"
"  }\n"
"  if (sceneHasWater(uScene) && matId != 3.0) {\n"
"    float wy = getWaterBaseY(uScene);\n"
"    float wetness = 1.0 - smoothstep(wy - 0.02, wy + 0.46, p.y - (nLow - 0.5) * 0.14);\n"
"    if (wetness > 0.001) {\n"
"      m.albedo *= mix(1.0, 0.44, wetness * (1.0 - m.metal * 0.8));\n"
"      m.rough = mix(m.rough, min(m.rough, 0.09), wetness * 0.92);\n"
"    }\n"
"  }\n"
"  if (matId != 3.0) {\n"
"    vec3 bump = vec3(\n"
"      vnoise3(p * 14.0 + vec3(0.1, 0.0, 0.0)) - vnoise3(p * 14.0 - vec3(0.1, 0.0, 0.0)),\n"
"      vnoise3(p * 14.0 + vec3(0.0, 0.1, 0.0)) - vnoise3(p * 14.0 - vec3(0.0, 0.1, 0.0)),\n"
"      vnoise3(p * 14.0 + vec3(0.0, 0.0, 0.1)) - vnoise3(p * 14.0 - vec3(0.0, 0.0, 0.1))\n"
"    );\n"
"    m.normalMod = normalize(N + bump * ((matId == 4.0 || matId == 1.0 || matId == 6.0) ? 0.14 : 0.04));\n"
"  }\n"
"  return m;\n"
"}\n";

// --- PASS 1C: 2-MEDIUM WATER, FRESNEL EARLY-OUT, POLISHED FOAM & EVENT HORIZON ---
static const char *FS_MAIN_INTEGRATOR_SRC =
"vec2 raymarchSolid(vec3 ro, vec3 rd, float tMin, float tMax, int maxSteps) {\n"
"  float t = tMin;\n"
"  float stepScale = (uScene == 1 || uScene == 3) ? 0.74 : 0.80;\n"
"  for (int i = 0; i < 128; i++) {\n"
"    if (i >= maxSteps) break;\n"
"    vec3 p = ro + rd * t;\n"
"    vec2 h = mapSolid(p);\n"
"    float eps = max(0.0012, 0.00055 * t);\n"
"    if (h.x < eps) return vec2(t, h.y);\n"
"    t += max(h.x * stepScale, eps * 0.75);\n"
"    if (t > tMax) break;\n"
"  }\n"
"  return vec2(-1.0, 0.0);\n"
"}\n"
"\n"
"float calcSoftShadow(vec3 ro, vec3 rd, float tMin, float tMax, float k) {\n"
"  float res = 1.0, t = tMin, ph = 1e10;\n"
"  for (int i = 0; i < 36; i++) {\n"
"    float h = mapSolidShadow(ro + rd * t);\n"
"    if (h < 0.0015) return 0.0;\n"
"    float y = (h * h) / (2.0 * ph);\n"
"    float d = sqrt(max(0.0, h * h - y * y));\n"
"    res = min(res, k * d / max(0.0, t - y));\n"
"    ph = h;\n"
"    t += clamp(h * 0.82, 0.03, 0.95);\n"
"    if (t > tMax || res < 0.005) break;\n"
"  }\n"
"  return clamp(res, 0.0, 1.0);\n"
"}\n"
"\n"
"float calcAO(vec3 p, vec3 n) {\n"
"  float occ = 0.0, sca = 1.0;\n"
"  for (int i = 0; i < 5; i++) {\n"
"    float h = 0.04 + 0.16 * float(i);\n"
"    occ += (h - mapSolidShadow(p + h * n)) * sca;\n"
"    sca *= 0.72;\n"
"  }\n"
"  return clamp(1.0 - 2.4 * occ, 0.04, 1.0);\n"
"}\n"
"\n"
"float intersectWater(vec3 ro, vec3 rd, float tMax) {\n"
"  if (!sceneHasWater(uScene)) return -1.0;\n"
"  float wy = getWaterBaseY(uScene);\n"
"  float maxAmp = (uScene == 0) ? 0.19 : 0.055;\n"
"  float yHi = wy + maxAmp, yLo = wy - maxAmp;\n"
"  if (ro.y > yHi && rd.y >= -1e-4) return -1.0;\n"
"  if (ro.y < yLo && rd.y <=  1e-4) return -1.0;\n"
"  float tStart = 0.02, tEnd = tMax;\n"
"  if (abs(rd.y) > 1e-4) {\n"
"    float t1 = (yHi - ro.y) / rd.y, t2 = (yLo - ro.y) / rd.y;\n"
"    tStart = max(tStart, min(t1, t2));\n"
"    tEnd   = min(tEnd,   max(t1, t2));\n"
"  }\n"
"  if (tStart > tEnd) return -1.0;\n"
"  vec3 p0 = ro + rd * tStart;\n"
"  float prevF = p0.y - (wy + waterHeight(p0.xz, uTime, uScene));\n"
"  float prevT = tStart;\n"
"  int steps = (uScene == 0) ? 28 : 16;\n"
"  float dt = (tEnd - tStart) / float(steps);\n"
"  for (int i = 1; i <= 28; i++) {\n"
"    if (i > steps) break;\n"
"    float t = tStart + dt * float(i);\n"
"    vec3 p = ro + rd * t;\n"
"    float f = p.y - (wy + waterHeight(p.xz, uTime, uScene));\n"
"    if (f * prevF <= 0.0) {\n"
"      float a = prevT, b = t, fa = prevF;\n"
"      for (int j = 0; j < 5; j++) {\n"
"        float m = 0.5 * (a + b);\n"
"        vec3 pm = ro + rd * m;\n"
"        float fm = pm.y - (wy + waterHeight(pm.xz, uTime, uScene));\n"
"        if (fm * fa <= 0.0) b = m; else { a = m; fa = fm; }\n"
"      }\n"
"      return 0.5 * (a + b);\n"
"    }\n"
"    prevT = t; prevF = f;\n"
"  }\n"
"  return -1.0;\n"
"}\n"
"\n"
"vec3 evalLocalLights(vec3 p, vec3 N, vec3 V, Material m, bool cheapShadow) {\n"
"  vec3 acc = vec3(0.0);\n"
"  if (uScene == 0) {\n"
"    vec3 toL = vec3(0.0, 1.65, 0.0) - p;\n"
"    float d2 = dot(toL, toL) + 0.65;\n"
"    vec3 col = vec3(2.8, 9.5, 14.5) * (1.0 + 0.18 * uAudioMid) * (2.4 / d2);\n"
"    acc += evalDirectPBR(N, V, normalize(toL), m.albedo, m.rough, m.metal, col);\n"
"  } else if (uScene == 1) {\n"
"    float lz = floor((p.z + 3.0) / 6.0) * 6.0;\n"
"    for (int s = -1; s <= 1; s += 2) {\n"
"      vec3 toL = vec3(float(s) * 2.95, 2.15, lz) - p;\n"
"      float d2 = dot(toL, toL) + 0.35;\n"
"      float d = sqrt(d2);\n"
"      vec3 L = toL / d;\n"
"      vec3 rad = vec3(17.5, 7.4, 2.2) * (1.0 + 0.12 * uAudioMid) / d2;\n"
"      float sh = 1.0;\n"
"      if (!cheapShadow && d < 8.5) {\n"
"        sh = calcSoftShadow(p + N * 0.025, L, 0.05, min(d - 0.12, 7.5), 10.0);\n"
"      }\n"
"      acc += evalDirectPBR(N, V, L, m.albedo, m.rough, m.metal, rad) * sh;\n"
"    }\n"
"  }\n"
"  return acc;\n"
"}\n"
"\n"
"vec3 shadeSolid(vec3 p, vec3 geomN, vec3 V, float matId, vec3 sunDir, vec3 sunCol, bool isUnderwater, bool doBounceRefl, bool cheapShadow) {\n"
"  Material m = evalMaterial(p, geomN, matId);\n"
"  vec3 N = m.normalMod;\n"
"  float ao = calcAO(p, geomN);\n"
"  float sh = cheapShadow ? calcFastShadow(p + geomN * 0.025, sunDir, 24.0)\n"
"                         : calcSoftShadow(p + geomN * 0.025, sunDir, 0.05, 32.0, 14.0);\n"
"  vec3 directSun = sunCol;\n"
"  if (isUnderwater) {\n"
"    float subDepth = max(getWaterBaseY(uScene) - p.y, 0.0);\n"
"    directSun *= exp(-(vec3(0.42, 0.13, 0.07) / max(uWaterClarity, 0.2)) * subDepth);\n"
"    directSun *= (1.0 + evalCaustics(p, sunDir, uTime, uScene) * 2.6 * max(geomN.y, 0.08));\n"
"  }\n"
"  vec3 col = evalDirectPBR(N, V, sunDir, m.albedo, m.rough, m.metal, directSun) * sh;\n"
"  col += evalLocalLights(p, N, V, m, cheapShadow);\n"
"  vec3 skyUp = evalSkyHDR(normalize(vec3(0.0, 0.85, 0.15)), sunDir, false);\n"
"  vec3 skyHoriz = evalSkyHDR(normalize(vec3(N.x, 0.12, N.z)), sunDir, false);\n"
"  vec3 bounceCol = (uScene == 1) ? vec3(0.035, 0.032, 0.030) : (uScene == 3 ? vec3(0.26, 0.24, 0.19) : vec3(0.05, 0.09, 0.11));\n"
"  vec3 irr = mix(bounceCol, mix(skyHoriz, skyUp, 0.5), 0.5 + 0.5 * N.y);\n"
"  if (uScene == 1) irr *= mix(0.045, 0.34, smoothstep(-0.3, 4.8, p.y));\n"
"  if (isUnderwater) {\n"
"    float subDepth = max(getWaterBaseY(uScene) - p.y, 0.0);\n"
"    irr *= exp(-vec3(0.38, 0.12, 0.06) * subDepth / max(uWaterClarity, 0.2));\n"
"  }\n"
"  float NoV = max(dot(N, V), 1e-4);\n"
"  vec3 F0 = mix(vec3(0.04), m.albedo, m.metal);\n"
"  vec3 Fenv = F_SchlickRough(NoV, F0, m.rough);\n"
"  col += (1.0 - Fenv) * (1.0 - m.metal) * m.albedo * irr * ao * 0.48;\n"
"  vec3 R = reflect(-V, N);\n"
"  vec3 envRefl = evalSkyHDR(R, sunDir, false);\n"
"  if (uScene == 1) envRefl *= 0.18;\n"
"  if (doBounceRefl && m.rough < 0.38 && !isUnderwater) {\n"
"    vec2 rh = raymarchSolid(p + geomN * 0.03, R, 0.04, 18.0, 32);\n"
"    if (rh.x > 0.0) {\n"
"      vec3 rp = p + R * rh.x;\n"
"      vec3 rN = calcNormal(rp, rh.x);\n"
"      Material rm = evalMaterial(rp, rN, rh.y);\n"
"      float rSh = calcFastShadow(rp + rN * 0.03, sunDir, 18.0);\n"
"      envRefl = rm.emissive + evalDirectPBR(rN, -R, sunDir, rm.albedo, rm.rough, rm.metal, sunCol) * rSh + rm.albedo * irr * 0.25;\n"
"    }\n"
"  }\n"
"  return col + envRefl * Fenv * mix(1.0, 0.28, m.rough * m.rough) * mix(0.35, 1.0, ao) + m.emissive;\n"
"}\n"
"\n"
"vec3 evalStarfield(vec3 dir) {\n"
"  vec3 col = vec3(0.0);\n"
"  float band = exp(-pow(dot(dir, normalize(vec3(0.28, 0.88, -0.38))) * 3.2, 2.0));\n"
"  col += vec3(0.035, 0.055, 0.095) * band * fbm3(dir * 4.5) * 1.4;\n"
"  col += vec3(0.08, 0.045, 0.03) * band * pow(fbm3(dir * 7.5 + 3.1), 2.0) * 0.8;\n"
"  vec3 p = dir * 135.0;\n"
"  vec3 rnd = hash33(floor(p));\n"
"  float d = length((fract(p) - 0.5) - (rnd - 0.5) * 0.55);\n"
"  float star = smoothstep(0.11, 0.015, d) * step(0.935, rnd.z);\n"
"  vec3 starCol = mix(vec3(0.7, 0.85, 1.0), vec3(1.0, 0.82, 0.62), rnd.x);\n"
"  return col + starCol * star * (2.5 + 6.0 * pow(rnd.y, 4.0));\n"
"}\n"
"\n"
"vec4 renderEventHorizon(vec3 ro, vec3 rd) {\n"
"  const float RS = 1.38, R_INNER = 2.15, R_OUTER = 7.60;\n"
"  vec3 pos = ro, vel = normalize(rd);\n"
"  vec3 hVec = cross(pos, vel);\n"
"  float h2 = dot(hVec, hVec);\n"
"  vec3 accum = vec3(0.0);\n"
"  float trans = 1.0, minR = length(pos), hitDepth = 50.0;\n"
"  bool captured = false;\n"
"  for (int i = 0; i < 130; i++) {\n"
"    float r = length(pos);\n"
"    minR = min(minR, r);\n"
"    if (r <= RS * 1.015) { captured = true; hitDepth = min(hitDepth, length(pos - ro)); break; }\n"
"    if (r > 36.0 && dot(pos, vel) > 0.0) break;\n"
"    float dt = (r > 8.5) ? clamp(0.055 * r, 0.04, 1.05) : clamp(0.032 * r, 0.025, 0.42);\n"
"    float r2 = max(r * r, 0.01);\n"
"    vec3 nextVel = normalize(vel + (-1.5 * h2 * pos / (r2 * r2 * r)) * dt);\n"
"    vec3 nextPos = pos + nextVel * dt;\n"
"    vec3 mp = 0.5 * (pos + nextPos);\n"
"    float rMid = length(mp);\n"
"    float diskThick = 0.09 + 0.045 * (rMid - R_INNER);\n"
"    float yAbs = abs(mp.y);\n"
"    if (rMid > R_INNER * 0.92 && rMid < R_OUTER && yAbs < diskThick * 3.5) {\n"
"      float radT = clamp((rMid - R_INNER) / (R_OUTER - R_INNER), 0.0, 1.0);\n"
"      float omega = 1.65 / pow(max(rMid, 1.0), 1.35);\n"
"      float spiral = atan(mp.z, mp.x) + uTime * omega + 4.8 / sqrt(max(rMid, 0.8));\n"
"      vec3 swirlCoord = vec3(cos(spiral) * rMid * 0.65, mp.y * 5.0, sin(spiral) * rMid * 0.65);\n"
"      float turb = fbm3(swirlCoord * 1.35 + vec3(uTime * 0.15, 0.0, -uTime * 0.12));\n"
"      float filaments = smoothstep(0.28, 0.82, turb) * (0.65 + 0.55 * sin(rMid * 5.2 - uTime * 2.0 + turb * 5.0));\n"
"      float dens = filaments * exp(-pow(yAbs / max(diskThick, 0.04), 2.0)) * smoothstep(0.0, 0.08, radT) * pow(1.0 - radT, 1.85) * (1.0 + 0.25 * uAudioBass);\n"
"      if (dens > 0.002) {\n"
"        vec3 tanDir = normalize(vec3(-mp.z, 0.0, mp.x));\n"
"        float beta = sqrt(0.5 * RS / max(rMid, RS * 1.2));\n"
"        float doppler = 1.0 / max(1.0 - beta * dot(tanDir, -vel), 0.35);\n"
"        float beam = pow(clamp(doppler, 0.45, 2.4), 2.6);\n"
"        vec3 plasma = mix(vec3(1.15, 0.94, 0.82), vec3(1.10, 0.48, 0.14), smoothstep(0.0, 0.38, radT));\n"
"        plasma = mix(plasma, vec3(0.45, 0.09, 0.03), smoothstep(0.35, 0.95, radT));\n"
"        plasma = mix(plasma * vec3(1.25, 0.72, 0.48), plasma * vec3(0.85, 0.96, 1.30), smoothstep(0.75, 1.55, doppler));\n"
"        accum += trans * (plasma * beam * dens * 4.4) * dt * 2.4;\n"
"        trans *= exp(-dens * dt * 2.8);\n"
"        hitDepth = min(hitDepth, length(mp - ro));\n"
"        if (trans < 0.015) break;\n"
"      }\n"
"    }\n"
"    pos = nextPos; vel = nextVel;\n"
"  }\n"
"  if (!captured) {\n"
"    accum += trans * vec3(1.35, 0.82, 0.42) * exp(-pow((minR - RS * 1.48) / 0.14, 2.0)) * 1.15;\n"
"    accum += trans * evalStarfield(vel);\n"
"  }\n"
"  return vec4(max(accum, vec3(0.0)), hitDepth);\n"
"}\n"
"\n"
"void main() {\n"
"  vec2 pix = gl_FragCoord.xy + uJitter;\n"
"  vec2 ndc = (pix / uResolution) * 2.0 - 1.0;\n"
"  ndc.x *= uResolution.x / uResolution.y;\n"
"  vec3 ro = uCamPos;\n"
"  vec3 rd = normalize(uCamMat * vec3(ndc * tan(uFov * 0.5), 1.0));\n"
"  if (uScene == 2) {\n"
"    vec4 bh = renderEventHorizon(ro, rd);\n"
"    outColor = (uDebug == 2) ? vec4(vec3(exp(-bh.a * 0.08)), bh.a) : bh;\n"
"    return;\n"
"  }\n"
"  vec3 sunDir = getSunDir();\n"
"  vec3 sunCol = getSunRadiance(sunDir);\n"
"  vec2 solidHit = raymarchSolid(ro, rd, 0.02, MAX_DIST, 118);\n"
"  float tSolid = (solidHit.x > 0.0) ? solidHit.x : MAX_DIST;\n"
"  float tWater = intersectWater(ro, rd, tSolid);\n"
"  float wy = getWaterBaseY(uScene);\n"
"  bool camUnderwater = sceneHasWater(uScene) && (ro.y < wy + waterHeight(ro.xz, uTime, uScene));\n"
"  if (uDebug == 1) {\n"
"    if (tWater > 0.0 && tWater < tSolid) outColor = vec4(waterNormal((ro + rd * tWater).xz, uTime, uScene, tWater) * 0.5 + 0.5, tWater);\n"
"    else if (solidHit.x > 0.0)           outColor = vec4(calcNormal(ro + rd * tSolid, tSolid) * 0.5 + 0.5, tSolid);\n"
"    else                                 outColor = vec4(rd * 0.5 + 0.5, MAX_DIST);\n"
"    return;\n"
"  }\n"
"  if (uDebug == 2) {\n"
"    float tBest = (tWater > 0.0) ? min(tWater, tSolid) : tSolid;\n"
"    outColor = vec4(vec3(exp(-tBest * 0.065)), tBest);\n"
"    return;\n"
"  }\n"
"  vec3 color = vec3(0.0);\n"
"  float outDepth = tSolid;\n"
"  if (tWater > 0.0 && tWater < tSolid && !camUnderwater) {\n"
"    outDepth = tWater;\n"
"    vec3 pw = ro + rd * tWater;\n"
"    vec3 Nw = waterNormal(pw.xz, uTime, uScene, tWater);\n"
"    vec3 V = -rd;\n"
"    float NoV = max(dot(Nw, V), 0.001);\n"
"    float fresnel = 0.02 + 0.98 * pow(1.0 - NoV, 5.0);\n"
"    vec3 rdRefr = refract(rd, Nw, 1.0 / 1.333);\n"
"    rdRefr = normalize(length(rdRefr) < 0.01 ? rd : rdRefr);\n"
"    vec2 subHit = raymarchSolid(pw - vec3(0.0, 0.012, 0.0), rdRefr, 0.015, 28.0, 68);\n"
"    float subDist = (subHit.x > 0.0) ? subHit.x : 24.0;\n"
"    vec3 subCol = vec3(0.012, 0.045, 0.068);\n"
"    if (subHit.x > 0.0) {\n"
"      vec3 pSub = pw + rdRefr * subHit.x;\n"
"      vec3 nSub = calcNormal(pSub, tWater + subHit.x);\n"
"      subCol = shadeSolid(pSub, nSub, -rdRefr, subHit.y, sunDir, sunCol, true, false, true);\n"
"    }\n"
"    vec3 sigmaA = (uScene == 1) ? vec3(0.85, 0.55, 0.42)\n"
"                                : (uScene == 3 ? vec3(0.36, 0.11, 0.06) : vec3(0.46, 0.14, 0.08));\n"
"    vec3 transmittance = exp(-(sigmaA / max(uWaterClarity, 0.25)) * subDist);\n"
"    float sunLitWater = calcFastShadow(pw + vec3(0.0, 0.05, 0.0), sunDir, 24.0);\n"
"    vec3 scatterCol = (uScene == 1) ? vec3(0.018, 0.022, 0.024)\n"
"      : mix(vec3(0.012, 0.055, 0.075), vec3(0.04, 0.20, 0.24), sunLitWater * clamp(sunDir.y * 2.0, 0.1, 1.0));\n"
"    vec3 refractedTotal = subCol * transmittance + scatterCol * (1.0 - transmittance);\n"
"    vec3 rdRefl = reflect(rd, Nw);\n"
"    if (rdRefl.y < 0.02) rdRefl = normalize(vec3(rdRefl.x, 0.02, rdRefl.z));\n"
"    vec3 reflCol = evalSkyHDR(rdRefl, sunDir, true);\n"
"    // Early-out skip on steep downward angles where Fresnel reflection weight < 5.5%\n"
"    if (fresnel > 0.055 || uScene == 1) {\n"
"      vec2 reflHit = raymarchSolid(pw + Nw * 0.025, rdRefl, 0.03, 34.0, 48);\n"
"      if (reflHit.x > 0.0) {\n"
"        vec3 pr = pw + rdRefl * reflHit.x;\n"
"        vec3 nr = calcNormal(pr, reflHit.x);\n"
"        reflCol = shadeSolid(pr, nr, -rdRefl, reflHit.y, sunDir, sunCol, false, false, true);\n"
"        reflCol = mix(reflCol, evalSkyHDR(rdRefl, sunDir, false), (1.0 - exp(-reflHit.x * 0.018)) * (uScene == 1 ? 0.15 : 0.65));\n"
"      }\n"
"    }\n"
"    color = mix(refractedTotal, reflCol, fresnel);\n"
"    float waterSh = calcSoftShadow(pw + vec3(0.0, 0.03, 0.0), sunDir, 0.05, 32.0, 14.0);\n"
"    vec3 H = normalize(V + sunDir);\n"
"    float NoH = max(dot(Nw, H), 0.0), NoL = max(dot(Nw, sunDir), 0.0);\n"
"    float glints = D_GGX(NoH, 0.018) * V_SmithGGX(NoV, NoL, 0.018) * (0.02 + 0.98 * pow(1.0 - max(dot(V, H), 0.0), 5.0));\n"
"    color += sunCol * glints * NoL * waterSh * 1.15;\n"
"    // Tight shoreline-only contact foam (evaluated slightly above waterline so submerged flat terraces stay clean!)\n"
"    float emergeProx = mapSolidShadow(pw + vec3(0.0, 0.07, 0.0));\n"
"    float edgeBand = 1.0 - smoothstep(0.0, (uScene == 0) ? 0.22 : 0.11, emergeProx);\n"
"    if (edgeBand > 0.005 && uScene != 1) {\n"
"      float foamTex = fbm2(pw.xz * 7.8 + vec2(uTime * 0.35, -uTime * 0.25));\n"
"      float foamMask = smoothstep(0.36, 0.72, foamTex + edgeBand * 0.52) * edgeBand;\n"
"      vec3 foamLit = sunCol * 0.22 * waterSh + evalSkyHDR(vec3(0.0, 1.0, 0.0), sunDir, false) * 0.45;\n"
"      color = mix(color, foamLit * vec3(0.92, 0.96, 1.0), foamMask * 0.80);\n"
"    }\n"
"    if (uDebug == 3) {\n"
"      float cDbg = (subHit.x > 0.0) ? evalCaustics(pw + rdRefr * subHit.x, sunDir, uTime, uScene) : 0.0;\n"
"      outColor = vec4(fresnel, cDbg * 0.65, transmittance.r, tWater);\n"
"      return;\n"
"    }\n"
"    float airFog = (uScene == 1) ? (1.0 - exp(-tWater * 0.030)) : (1.0 - exp(-tWater * 0.011));\n"
"    color = mix(color, (uScene == 1) ? vec3(0.014, 0.017, 0.022) : evalSkyHDR(rd, sunDir, false), airFog * 0.72);\n"
"  } else if (solidHit.x > 0.0) {\n"
"    vec3 p = ro + rd * tSolid;\n"
"    vec3 N = calcNormal(p, tSolid);\n"
"    color = shadeSolid(p, N, -rd, solidHit.y, sunDir, sunCol, camUnderwater, true, false);\n"
"    if (camUnderwater) {\n"
"      vec3 tr = exp(-(vec3(0.45, 0.14, 0.08) / max(uWaterClarity, 0.25)) * tSolid);\n"
"      color = color * tr + vec3(0.018, 0.085, 0.115) * (1.0 - tr);\n"
"    } else {\n"
"      float airFog = (uScene == 1) ? (1.0 - exp(-tSolid * 0.034)) : (1.0 - exp(-tSolid * 0.012));\n"
"      color = mix(color, (uScene == 1) ? vec3(0.014, 0.017, 0.022) : evalSkyHDR(rd, sunDir, false), airFog * 0.72);\n"
"    }\n"
"    if (uDebug == 3) {\n"
"      float cDbg = camUnderwater ? evalCaustics(p, sunDir, uTime, uScene) : 0.0;\n"
"      outColor = vec4(0.0, cDbg * 0.7, camUnderwater ? 0.8 : 0.05, tSolid);\n"
"      return;\n"
"    }\n"
"  } else {\n"
"    outDepth = MAX_DIST;\n"
"    color = evalSkyHDR(rd, sunDir, true);\n"
"    if (camUnderwater) color = mix(color * vec3(0.25, 0.65, 0.78), vec3(0.015, 0.075, 0.105), 0.75);\n"
"  }\n"
"  if (any(isnan(color)) || any(isinf(color))) color = vec3(0.0);\n"
"  outColor = vec4(clamp(color, 0.0, 50.0), outDepth);\n"
"}\n";

// --- PASS 2: HALF-RES NVIDIA 32-THREAD WARP VOLUMETRIC GOD-RAY COMPUTE SHADER ---
static const char *CS_VOL_HEADER_SRC =
"#version 430 core\n"
"layout(local_size_x = 8, local_size_y = 4, local_size_z = 1) in;\n"
"layout(rgba16f, binding = 0) writeonly uniform image2D uVolOut;\n"
"uniform sampler2D uMainTex;\n"
"uniform ivec2 uMainSize;\n"
"uniform ivec2 uVolSize;\n"
"uniform float uTime;\n"
"uniform int   uFrame;\n"
"uniform int   uScene;\n"
"uniform vec3  uCamPos;\n"
"uniform mat3  uCamMat;\n"
"uniform float uFov;\n"
"uniform float uSunElev;\n"
"uniform float uVolumetric;\n";

static const char *CS_VOL_MAIN_SRC =
"void main() {\n"
"  ivec2 gid = ivec2(gl_GlobalInvocationID.xy);\n"
"  if (gid.x >= uVolSize.x || gid.y >= uVolSize.y) return;\n"
"  ivec2 fullPix = min(gid * 2, uMainSize - 1);\n"
"  float tLimit = texelFetch(uMainTex, fullPix, 0).a;\n"
"  bool underwater = ((uScene == 0 || uScene == 1 || uScene == 3) && uCamPos.y < -0.02);\n"
"  if (uScene == 2 || uVolumetric <= 0.005 || underwater) {\n"
"    imageStore(uVolOut, gid, vec4(0.0, 0.0, 0.0, tLimit));\n"
"    return;\n"
"  }\n"
"  vec2 ndc = ((vec2(fullPix) + 0.5) / vec2(uMainSize)) * 2.0 - 1.0;\n"
"  ndc.x *= float(uMainSize.x) / float(uMainSize.y);\n"
"  vec3 rd = normalize(uCamMat * vec3(ndc * tan(uFov * 0.5), 1.0));\n"
"  vec3 sunDir = getSunDir();\n"
"  vec3 sunCol = getSunRadiance(sunDir);\n"
"  float marchDist = min(tLimit, (uScene == 1) ? 24.0 : 34.0);\n"
"  if (marchDist < 0.15) {\n"
"    imageStore(uVolOut, gid, vec4(0.0, 0.0, 0.0, tLimit));\n"
"    return;\n"
"  }\n"
"  const int STEPS = 20;\n"
"  float stepLen = marchDist / float(STEPS);\n"
"  float dither = ign(vec2(gid), uFrame);\n"
"  float cosTheta = dot(rd, sunDir);\n"
"  float phase = hgPhase(cosTheta, 0.72) * 0.85 + hgPhase(cosTheta, 0.15) * 0.25;\n"
"  vec3 scatter = vec3(0.0);\n"
"  float sigmaBase = ((uScene == 1) ? 0.044 : (uScene == 3 ? 0.011 : 0.013)) * uVolumetric;\n"
"  for (int i = 0; i < STEPS; i++) {\n"
"    float t = (float(i) + dither) * stepLen;\n"
"    vec3 p = uCamPos + rd * t;\n"
"    float hDens = (uScene == 1)\n"
"      ? (0.65 + 0.55 * vnoise3(p * 0.45 + vec3(0.0, uTime * 0.08, uTime * 0.05)))\n"
"      : exp(-max(p.y + 0.3, 0.0) * 0.26) * (0.7 + 0.4 * vnoise3(p * 0.3 + vec3(uTime * 0.05, 0.0, 0.0)));\n"
"    float sh = calcFastShadow(p, sunDir, 26.0);\n"
"    vec3 inLit = sunCol * phase * sh * 0.46;\n"
"    if (uScene == 1) {\n"
"      float lz = floor((p.z + 3.0) / 6.0) * 6.0;\n"
"      float g1 = 1.0 / (dot(p - vec3( 2.95, 2.15, lz), p - vec3( 2.95, 2.15, lz)) + 0.85);\n"
"      float g2 = 1.0 / (dot(p - vec3(-2.95, 2.15, lz), p - vec3(-2.95, 2.15, lz)) + 0.85);\n"
"      inLit += vec3(3.6, 1.45, 0.42) * (g1 + g2) * 0.18;\n"
"    }\n"
"    scatter += inLit * hDens * sigmaBase * stepLen;\n"
"  }\n"
"  imageStore(uVolOut, gid, vec4(clamp(scatter, 0.0, 12.0), tLimit));\n"
"}\n";

// --- PASS 3: BILATERAL VOLUMETRIC UPSAMPLE + TEMPORAL ANTI-ALIASING ---
static const char *FS_TAA_SRC =
"#version 430 core\n"
"in vec2 vUv;\n"
"out vec4 outColor;\n"
"uniform sampler2D uCurrTex;\n"
"uniform sampler2D uVolTex;\n"
"uniform sampler2D uHistTex;\n"
"uniform vec2  uResolution;\n"
"uniform int   uEnableTAA;\n"
"uniform int   uUseVol;\n"
"uniform float uBlendFactor;\n"
"uniform vec3  uCamPos;\n"
"uniform mat3  uCamMat;\n"
"uniform vec3  uPrevCamPos;\n"
"uniform mat3  uPrevCamMat;\n"
"uniform float uFov;\n"
"vec3 rgb2ycocg(vec3 c) {\n"
"  return vec3(0.25*c.r + 0.5*c.g + 0.25*c.b, 0.5*c.r - 0.5*c.b, -0.25*c.r + 0.5*c.g - 0.25*c.b);\n"
"}\n"
"vec3 ycocg2rgb(vec3 c) {\n"
"  return vec3(c.x + c.y - c.z, c.x + c.z, c.x - c.y - c.z);\n"
"}\n"
"vec3 sampleVolBilateral(vec2 uv, float centerDepth) {\n"
"  ivec2 volSize = textureSize(uVolTex, 0);\n"
"  vec2 fCoord = uv * vec2(volSize) - 0.5;\n"
"  ivec2 base = ivec2(floor(fCoord));\n"
"  vec2 f = clamp(fCoord - vec2(base), 0.0, 1.0);\n"
"  vec3 sum = vec3(0.0);\n"
"  float wSum = 0.0;\n"
"  float depthScale = max(centerDepth * 0.14, 0.35);\n"
"  for (int dy = 0; dy <= 1; dy++) {\n"
"    for (int dx = 0; dx <= 1; dx++) {\n"
"      ivec2 tc = clamp(base + ivec2(dx, dy), ivec2(0), volSize - 1);\n"
"      vec4 tap = texelFetch(uVolTex, tc, 0);\n"
"      float bw = ((dx == 0) ? (1.0 - f.x) : f.x) * ((dy == 0) ? (1.0 - f.y) : f.y);\n"
"      float dw = exp(-abs(centerDepth - tap.a) / depthScale);\n"
"      float w = bw * (dw + 1e-4);\n"
"      sum += tap.rgb * w;\n"
"      wSum += w;\n"
"    }\n"
"  }\n"
"  return sum / max(wSum, 1e-4);\n"
"}\n"
"void main() {\n"
"  vec4 curr = texture(uCurrTex, vUv);\n"
"  vec3 vol = (uUseVol == 1) ? sampleVolBilateral(vUv, curr.a) : vec3(0.0);\n"
"  vec3 currRgb = curr.rgb + vol;\n"
"  if (uEnableTAA == 0 || uBlendFactor <= 0.001) { outColor = vec4(currRgb, curr.a); return; }\n"
"  float aspect = uResolution.x / uResolution.y;\n"
"  float tanHalf = tan(uFov * 0.5);\n"
"  vec2 ndc = vUv * 2.0 - 1.0;\n"
"  vec3 rdCurr = normalize(uCamMat * vec3(ndc.x * aspect * tanHalf, ndc.y * tanHalf, 1.0));\n"
"  vec3 worldPos = uCamPos + rdCurr * min(curr.a, 100.0);\n"
"  vec3 prevRel = transpose(uPrevCamMat) * (worldPos - uPrevCamPos);\n"
"  vec2 prevUv = vUv;\n"
"  bool valid = false;\n"
"  if (prevRel.z > 0.05) {\n"
"    vec2 prevNdc = prevRel.xy / (prevRel.z * tanHalf);\n"
"    prevNdc.x /= aspect;\n"
"    prevUv = prevNdc * 0.5 + 0.5;\n"
"    valid = (prevUv.x > 0.002 && prevUv.x < 0.998 && prevUv.y > 0.002 && prevUv.y < 0.998);\n"
"  }\n"
"  if (!valid) { outColor = vec4(currRgb, curr.a); return; }\n"
"  vec2 texel = 1.0 / uResolution;\n"
"  vec3 m1 = vec3(0.0), m2 = vec3(0.0);\n"
"  for (int y = -1; y <= 1; y++) {\n"
"    for (int x = -1; x <= 1; x++) {\n"
"      vec3 ycc = rgb2ycocg(texture(uCurrTex, vUv + vec2(float(x), float(y)) * texel).rgb);\n"
"      m1 += ycc; m2 += ycc * ycc;\n"
"    }\n"
"  }\n"
"  vec3 baseMu = m1 / 9.0;\n"
"  vec3 mu = baseMu + rgb2ycocg(vol);\n"
"  vec3 sigma = sqrt(max(m2 / 9.0 - baseMu * baseMu, vec3(0.0))) + vec3(0.015, 0.008, 0.008);\n"
"  vec3 histClamped = ycocg2rgb(clamp(rgb2ycocg(texture(uHistTex, prevUv).rgb), mu - 1.25 * sigma, mu + 1.25 * sigma));\n"
"  float wCurr = 1.0 / (1.0 + dot(currRgb, vec3(0.2126, 0.7152, 0.0722)));\n"
"  float wHist = 1.0 / (1.0 + dot(histClamped, vec3(0.2126, 0.7152, 0.0722)));\n"
"  float alpha = clamp(uBlendFactor, 0.0, 0.92);\n"
"  vec3 blended = (currRgb * (1.0 - alpha) * wCurr + histClamped * alpha * wHist)\n"
"               / max((1.0 - alpha) * wCurr + alpha * wHist, 1e-4);\n"
"  outColor = vec4(max(blended, vec3(0.0)), curr.a);\n"
"}\n";

// --- PASS 4: 8x8 SHARED-MEMORY PARALLEL REDUCTION AUTO-EXPOSURE COMPUTE ---
static const char *CS_ADAPT_SRC =
"#version 430 core\n"
"layout(local_size_x = 8, local_size_y = 8, local_size_z = 1) in;\n"
"layout(rgba16f, binding = 0) writeonly uniform image2D uLumOut;\n"
"uniform sampler2D uHdrTex;\n"
"uniform sampler2D uPrevLumTex;\n"
"uniform float uDt;\n"
"uniform int uReset;\n"
"shared float sLog[64];\n"
"shared float sWeight[64];\n"
"void main() {\n"
"  uint idx = gl_LocalInvocationIndex;\n"
"  vec2 uv = (vec2(gl_LocalInvocationID.xy) + 0.5) / 8.0;\n"
"  float lum = dot(texture(uHdrTex, uv).rgb, vec3(0.2126, 0.7152, 0.0722));\n"
"  float d = length(uv - 0.5);\n"
"  float w = exp(-d * d * 3.5);\n"
"  sLog[idx] = log2(clamp(lum, 0.008, 32.0)) * w;\n"
"  sWeight[idx] = w;\n"
"  barrier();\n"
"  for (uint stride = 32u; stride > 0u; stride >>= 1u) {\n"
"    if (idx < stride) {\n"
"      sLog[idx] += sLog[idx + stride];\n"
"      sWeight[idx] += sWeight[idx + stride];\n"
"    }\n"
"    barrier();\n"
"  }\n"
"  if (idx == 0u) {\n"
"    float avgLum = exp2(sLog[0] / max(sWeight[0], 1e-4));\n"
"    float prevLum = texelFetch(uPrevLumTex, ivec2(0, 0), 0).r;\n"
"    float adapted;\n"
"    if (uReset == 1 || isnan(prevLum) || prevLum <= 0.001) {\n"
"      adapted = avgLum;\n"
"    } else {\n"
"      float speed = (avgLum > prevLum) ? 3.2 : 1.6;\n"
"      adapted = prevLum + (avgLum - prevLum) * (1.0 - exp(-uDt * speed));\n"
"    }\n"
"    imageStore(uLumOut, ivec2(0, 0), vec4(clamp(adapted, 0.04, 16.0), 0.0, 0.0, 1.0));\n"
"  }\n"
"}\n";

// --- PASS 5 & 6: KARIS BRIGHT-PASS & SEPARABLE GAUSSIAN BLUR ---
static const char *FS_BRIGHT_SRC =
"#version 430 core\n"
"in vec2 vUv;\n"
"out vec4 outColor;\n"
"uniform sampler2D uHdrTex;\n"
"uniform vec2 uTexelSize;\n"
"uniform float uThreshold;\n"
"float luma(vec3 c) { return dot(c, vec3(0.2126, 0.7152, 0.0722)); }\n"
"vec3 karisSample(vec2 uv) { vec3 c = texture(uHdrTex, uv).rgb; return c / (1.0 + luma(c)); }\n"
"void main() {\n"
"  vec3 avg = 0.25 * (\n"
"    karisSample(vUv + vec2(-0.5, -0.5) * uTexelSize) +\n"
"    karisSample(vUv + vec2( 0.5, -0.5) * uTexelSize) +\n"
"    karisSample(vUv + vec2(-0.5,  0.5) * uTexelSize) +\n"
"    karisSample(vUv + vec2( 0.5,  0.5) * uTexelSize)\n"
"  );\n"
"  avg = avg / max(1.0 - luma(avg), 0.04);\n"
"  float br = max(avg.r, max(avg.g, avg.b));\n"
"  float knee = uThreshold * 0.55;\n"
"  float soft = clamp(br - uThreshold + knee, 0.0, 2.0 * knee);\n"
"  soft = (soft * soft) / max(4.0 * knee, 1e-4);\n"
"  float contrib = max(soft, br - uThreshold) / max(br, 1e-4);\n"
"  outColor = vec4(max(avg * contrib, vec3(0.0)), 1.0);\n"
"}\n";

static const char *FS_BLUR_SRC =
"#version 430 core\n"
"in vec2 vUv;\n"
"out vec4 outColor;\n"
"uniform sampler2D uTex;\n"
"uniform vec2 uDir;\n"
"void main() {\n"
"  const float w[5] = float[](0.227027, 0.1945946, 0.1216216, 0.054054, 0.016216);\n"
"  vec3 sum = texture(uTex, vUv).rgb * w[0];\n"
"  for (int i = 1; i < 5; i++) {\n"
"    vec2 off = uDir * float(i) * 1.45;\n"
"    sum += texture(uTex, vUv + off).rgb * w[i];\n"
"    sum += texture(uTex, vUv - off).rgb * w[i];\n"
"  }\n"
"  outColor = vec4(sum, 1.0);\n"
"}\n";

// --- PASS 7: CINEMATIC COMPOSITOR + UE5 BODYCAM OPTICAL FILTERS + RCAS ---
static const char *FS_COMPOSITE_SRC =
"#version 430 core\n"
"in vec2 vUv;\n"
"out vec4 outColor;\n"
"uniform sampler2D uHdrTex;\n"
"uniform sampler2D uBloomTex;\n"
"uniform sampler2D uStreakTex;\n"
"uniform sampler2D uLumTex;\n"
"uniform vec2  uResolution;\n"
"uniform float uTime;\n"
"uniform int   uFilter;\n"
"uniform int   uToneMap;\n"
"uniform int   uAutoExp;\n"
"uniform float uExposureBias;\n"
"uniform float uBloomStrength;\n"
"uniform float uSharpness;\n"
"uniform float uChromaStrength;\n"
"uniform float uGrainStrength;\n"
"uniform int   uSplitEnabled;\n"
"uniform float uSplitPos;\n"
"uniform int   uDebug;\n"
"\n"
"vec3 agxDefaultContrastApprox(vec3 x) {\n"
"  vec3 x2 = x * x, x4 = x2 * x2;\n"
"  return + 15.5 * x4 * x2 - 40.14 * x4 * x + 31.96 * x4 - 6.868 * x2 * x + 0.4298 * x2 + 0.1191 * x - 0.00232;\n"
"}\n"
"vec3 toneMapAgX(vec3 val) {\n"
"  const mat3 agx_mat = mat3(\n"
"    0.842479062253094,  0.0423282422610123, 0.0423756549057051,\n"
"    0.0784335999999992, 0.878468636469772,  0.0784336,\n"
"    0.0792237451477643, 0.0791661274605434, 0.879142973793104\n"
"  );\n"
"  const mat3 agx_mat_inv = mat3(\n"
"     1.19687900512017,   -0.0528968517574562, -0.0529716355144438,\n"
"    -0.0980208811401368,  1.15190312990417,   -0.0980434501171241,\n"
"    -0.0990297440797205, -0.0989611768448433,  1.15107367264116\n"
"  );\n"
"  val = agx_mat * max(val, vec3(1e-6));\n"
"  val = (clamp(log2(val), -12.47393, 4.026069) + 12.47393) / (4.026069 + 12.47393);\n"
"  val = agx_mat_inv * agxDefaultContrastApprox(val);\n"
"  float luma = dot(val, vec3(0.2126, 0.7152, 0.0722));\n"
"  val = pow(max(val, vec3(0.0)), vec3(1.12));\n"
"  return clamp(mix(vec3(luma), val, 1.14), 0.0, 1.0);\n"
"}\n"
"vec3 toneMapACES(vec3 x) { return clamp((x * (2.51 * x + 0.03)) / (x * (2.43 * x + 0.59) + 0.14), 0.0, 1.0); }\n"
"vec3 toneMapPBRNeutral(vec3 color) {\n"
"  const float startCompression = 0.76, desaturation = 0.15;\n"
"  float x = min(color.r, min(color.g, color.b));\n"
"  color -= (x < 0.08) ? (x - 6.25 * x * x) : 0.04;\n"
"  float peak = max(color.r, max(color.g, color.b));\n"
"  if (peak < startCompression) return clamp(color, 0.0, 1.0);\n"
"  const float d = 1.0 - startCompression;\n"
"  float newPeak = 1.0 - d * d / (peak + d - startCompression);\n"
"  color *= newPeak / peak;\n"
"  float g = 1.0 - 1.0 / (desaturation * (peak - newPeak) + 1.0);\n"
"  return clamp(mix(color, vec3(newPeak), g), 0.0, 1.0);\n"
"}\n"
"vec3 hablePartial(vec3 x) {\n"
"  return ((x * (0.15 * x + 0.05) + 0.004) / (x * (0.15 * x + 0.50) + 0.06)) - 0.02 / 0.30;\n"
"}\n"
"vec3 toneMapHable(vec3 x) { return clamp(hablePartial(x * 2.0) / hablePartial(vec3(11.2)), 0.0, 1.0); }\n"
"vec3 applyToneMap(vec3 hdr) {\n"
"  if (uToneMap == 0) return toneMapAgX(hdr);\n"
"  if (uToneMap == 1) return toneMapACES(hdr);\n"
"  if (uToneMap == 2) return toneMapPBRNeutral(hdr);\n"
"  return toneMapHable(hdr);\n"
"}\n"
"vec2 distortUV(vec2 uv, float k1, float k2) {\n"
"  vec2 p = uv * 2.0 - 1.0;\n"
"  float aspect = uResolution.x / uResolution.y;\n"
"  p.x *= aspect;\n"
"  float r2 = dot(p, p);\n"
"  float norm = 1.0 / (1.0 + k1 * 1.15 + k2 * 1.32);\n"
"  p *= (1.0 + k1 * r2 + k2 * r2 * r2) * norm;\n"
"  p.x /= aspect;\n"
"  return p * 0.5 + 0.5;\n"
"}\n"
"float filmHash(vec2 p, float t) {\n"
"  vec3 p3 = fract(vec3(p.xyx) * 0.1031 + fract(t * 17.31));\n"
"  p3 += dot(p3, p3.yzx + 33.33);\n"
"  return fract((p3.x + p3.y) * p3.z);\n"
"}\n"
"vec3 sampleFilteredHDR(vec2 uv, float exposure, float sharpAmt, float caAmt) {\n"
"  vec2 texel = 1.0 / vec2(textureSize(uHdrTex, 0));\n"
"  vec2 toCenter = uv - 0.5;\n"
"  vec2 caOff = toCenter * dot(toCenter, toCenter) * 0.012 * caAmt;\n"
"  vec3 cCenter = vec3(\n"
"    texture(uHdrTex, clamp(uv + caOff, 0.001, 0.999)).r,\n"
"    texture(uHdrTex, uv).g,\n"
"    texture(uHdrTex, clamp(uv - caOff, 0.001, 0.999)).b\n"
"  );\n"
"  if (sharpAmt > 0.01) {\n"
"    vec3 n = texture(uHdrTex, uv + vec2(0.0,  texel.y)).rgb;\n"
"    vec3 s = texture(uHdrTex, uv + vec2(0.0, -texel.y)).rgb;\n"
"    vec3 e = texture(uHdrTex, uv + vec2( texel.x, 0.0)).rgb;\n"
"    vec3 w = texture(uHdrTex, uv + vec2(-texel.x, 0.0)).rgb;\n"
"    vec3 mn = min(cCenter, min(min(n, s), min(e, w)));\n"
"    vec3 mx = max(cCenter, max(max(n, s), max(e, w)));\n"
"    vec3 amp = clamp(min(mn, 2.0 - mx) / max(mx, vec3(1e-4)), 0.0, 1.0);\n"
"    vec3 weight = sqrt(amp) * (-1.0 / mix(8.0, 5.0, sharpAmt));\n"
"    cCenter = max((cCenter + (n + s + e + w) * weight) / (1.0 + 4.0 * weight), vec3(0.0));\n"
"  }\n"
"  return cCenter * exposure;\n"
"}\n"
"void main() {\n"
"  if (uDebug != 0) {\n"
"    outColor = vec4(pow(clamp(texture(uHdrTex, vUv).rgb, 0.0, 1.0), vec3(1.0 / 2.2)), 1.0);\n"
"    return;\n"
"  }\n"
"  float avgLum = texelFetch(uLumTex, ivec2(0, 0), 0).r;\n"
"  float autoScale = (uAutoExp == 1) ? clamp(0.22 / max(avgLum, 0.04), 0.25, 3.8) : 1.0;\n"
"  float exposure = autoScale * exp2(uExposureBias);\n"
"  if (uSplitEnabled == 1) {\n"
"    if (abs(vUv.x - uSplitPos) * uResolution.x < 1.5) { outColor = vec4(0.22, 0.74, 0.97, 1.0); return; }\n"
"    if (vUv.x < uSplitPos) {\n"
"      vec3 raw = texture(uHdrTex, vUv).rgb * exp2(uExposureBias) * 0.55;\n"
"      outColor = vec4(pow(clamp(raw, 0.0, 1.0), vec3(1.0 / 2.2)), 1.0);\n"
"      return;\n"
"    }\n"
"  }\n"
"  vec2 uv = vUv;\n"
"  float caMult = uChromaStrength, grainMult = uGrainStrength;\n"
"  float sharpMult = uSharpness, vigPow = 0.34, streakAmt = 0.14;\n"
"  if (uFilter == 1) {\n"
"    uv = distortUV(vUv, 0.16, 0.045);\n"
"    caMult *= 1.55; grainMult *= 1.85;\n"
"    sharpMult = clamp(sharpMult * 1.35 + 0.15, 0.0, 1.0);\n"
"    vigPow = 0.52; streakAmt = 0.10;\n"
"  } else if (uFilter == 2) {\n"
"    uv = distortUV(vUv, 0.04, 0.01);\n"
"    caMult *= 1.25; streakAmt = 0.65; vigPow = 0.42;\n"
"  } else if (uFilter == 3) {\n"
"    caMult *= 0.15; grainMult *= 0.15; vigPow = 0.12; streakAmt = 0.04;\n"
"  }\n"
"  if (uv.x < 0.0 || uv.x > 1.0 || uv.y < 0.0 || uv.y > 1.0) {\n"
"    outColor = vec4(0.0, 0.0, 0.0, 1.0); return;\n"
"  }\n"
"  vec3 hdr = sampleFilteredHDR(uv, exposure, sharpMult, caMult);\n"
"  vec3 bloom = texture(uBloomTex, uv).rgb * exposure;\n"
"  vec3 streak = texture(uStreakTex, uv).rgb * exposure;\n"
"  vec3 halation = bloom * vec3(1.18, 0.88, 0.72);\n"
"  vec3 streakTint = (uFilter == 2) ? vec3(0.42, 0.76, 1.35) : vec3(0.85, 0.92, 1.05);\n"
"  hdr += mix(bloom, halation, (uFilter == 1) ? 0.55 : 0.25) * (0.28 * uBloomStrength);\n"
"  hdr += streak * streakTint * (streakAmt * uBloomStrength);\n"
"  float r = length((uv - 0.5) * vec2(uResolution.x / uResolution.y, 1.0));\n"
"  float vig = pow(clamp(cos(min(r * 0.78, 1.35)), 0.0, 1.0), 4.0);\n"
"  hdr *= mix(1.0, vig, clamp(vigPow * (0.6 + 0.4 * uChromaStrength), 0.0, 0.95));\n"
"  vec3 ldr = applyToneMap(hdr);\n"
"  if (uFilter == 0) {\n"
"    ldr = smoothstep(vec3(-0.02), vec3(1.01), ldr);\n"
"  } else if (uFilter == 1) {\n"
"    float luma = dot(ldr, vec3(0.2126, 0.7152, 0.0722));\n"
"    ldr = mix(vec3(luma), ldr, 0.84);\n"
"    ldr *= mix(vec3(0.93, 0.98, 1.04), vec3(1.03, 1.01, 0.96), smoothstep(0.15, 0.82, luma));\n"
"    ldr = clamp((ldr - 0.5) * 1.12 + 0.5, 0.0, 1.0) * 0.97 + 0.012;\n"
"  } else if (uFilter == 2) {\n"
"    float luma = dot(ldr, vec3(0.2126, 0.7152, 0.0722));\n"
"    ldr *= mix(vec3(0.90, 0.99, 1.08), vec3(1.08, 1.00, 0.90), smoothstep(0.18, 0.85, luma));\n"
"  }\n"
"  if (grainMult > 0.005) {\n"
"    float g = (filmHash(gl_FragCoord.xy, uTime) + filmHash(gl_FragCoord.xy + vec2(37.0, 17.0), uTime * 1.13) - 1.0) * 0.042 * grainMult;\n"
"    float luma = dot(ldr, vec3(0.2126, 0.7152, 0.0722));\n"
"    ldr = clamp(ldr + g * ((1.0 - smoothstep(0.55, 1.0, luma)) * 0.85 + 0.15), 0.0, 1.0);\n"
"  }\n"
"  if (uFilter == 1) ldr *= (1.0 - 0.018 * sin(gl_FragCoord.y * 1.5));\n"
"  vec3 srgb = mix(ldr * 12.92, 1.055 * pow(max(ldr, vec3(0.0)), vec3(1.0 / 2.4)) - 0.055, step(vec3(0.0031308), ldr));\n"
"  outColor = vec4(clamp(srgb, 0.0, 1.0), 1.0);\n"
"}\n";
// ============================================================================
// SHADER COMPILER (GRAPHICS + COMPUTE) & UNIFORM LOCATIONS
// ============================================================================
static GLuint compile_shader_parts(GLenum type, const char **parts, int count, const char *label) {
  GLuint sh = pglCreateShader(type);
  pglShaderSource(sh, count, parts, NULL);
  pglCompileShader(sh);
  GLint ok = 0;
  pglGetShaderiv(sh, GL_COMPILE_STATUS, &ok);
  if (!ok) {
    char log[4096], title[128];
    log[0] = '\0';
    pglGetShaderInfoLog(sh, (GLsizei)sizeof(log), NULL, log);
    snprintf(title, sizeof(title), "AETHERION Shader Error: %s", label);
    MessageBoxA(g_hwnd, log, title, MB_OK | MB_ICONERROR);
    return 0;
  }
  return sh;
}

static GLuint link_program(GLuint prog, const char *label) {
  pglLinkProgram(prog);
  GLint ok = 0;
  pglGetProgramiv(prog, GL_LINK_STATUS, &ok);
  if (!ok) {
    char log[4096], title[128];
    log[0] = '\0';
    pglGetProgramInfoLog(prog, (GLsizei)sizeof(log), NULL, log);
    snprintf(title, sizeof(title), "AETHERION Link Error: %s", label);
    MessageBoxA(g_hwnd, log, title, MB_OK | MB_ICONERROR);
    return 0;
  }
  return prog;
}

static GLuint create_program_parts(const char *vsSrc, const char **fsParts, int fsCount, const char *label) {
  GLuint vs = compile_shader_parts(GL_VERTEX_SHADER, &vsSrc, 1, label);
  GLuint fs = compile_shader_parts(GL_FRAGMENT_SHADER, fsParts, fsCount, label);
  if (!vs || !fs) return 0;
  GLuint prog = pglCreateProgram();
  pglAttachShader(prog, vs);
  pglAttachShader(prog, fs);
  GLuint ok = link_program(prog, label);
  pglDeleteShader(vs);
  pglDeleteShader(fs);
  return ok;
}

static GLuint create_compute_parts(const char **csParts, int csCount, const char *label) {
  GLuint cs = compile_shader_parts(GL_COMPUTE_SHADER, csParts, csCount, label);
  if (!cs) return 0;
  GLuint prog = pglCreateProgram();
  pglAttachShader(prog, cs);
  GLuint ok = link_program(prog, label);
  pglDeleteShader(cs);
  return ok;
}

typedef struct {
  GLuint prog;
  GLint uResolution, uTime, uFrame, uScene, uDebug;
  GLint uCamPos, uCamMat, uJitter, uFov;
  GLint uSunElev, uWaterClarity, uVolumetric;
  GLint uAudioBass, uAudioMid, uAudioHigh;
} ProgMain;

typedef struct {
  GLuint prog;
  GLint uMainTex, uMainSize, uVolSize, uTime, uFrame, uScene;
  GLint uCamPos, uCamMat, uFov, uSunElev, uVolumetric;
} ProgVol;

typedef struct {
  GLuint prog;
  GLint uCurrTex, uVolTex, uHistTex, uResolution, uEnableTAA, uUseVol, uBlendFactor;
  GLint uCamPos, uCamMat, uPrevCamPos, uPrevCamMat, uFov;
} ProgTAA;

typedef struct {
  GLuint prog;
  GLint uHdrTex, uPrevLumTex, uDt, uReset;
} ProgAdapt;

typedef struct {
  GLuint prog;
  GLint uHdrTex, uTexelSize, uThreshold;
} ProgBright;

typedef struct {
  GLuint prog;
  GLint uTex, uDir;
} ProgBlur;

typedef struct {
  GLuint prog;
  GLint uHdrTex, uBloomTex, uStreakTex, uLumTex;
  GLint uResolution, uTime, uFilter, uToneMap;
  GLint uAutoExp, uExposureBias, uBloomStrength;
  GLint uSharpness, uChromaStrength, uGrainStrength;
  GLint uSplitEnabled, uSplitPos, uDebug;
} ProgComp;

static ProgMain   g_progMain;
static ProgVol    g_progVol;
static ProgTAA    g_progTAA;
static ProgAdapt  g_progAdapt;
static ProgBright g_progBright;
static ProgBlur   g_progBlur;
static ProgComp   g_progComp;

static int init_shaders(void) {
  const char *mainParts[4] = { FS_MAIN_HEADER_SRC, GLSL_COMMON_MATH_SRC, FS_MAIN_WORLDS_SRC, FS_MAIN_INTEGRATOR_SRC };
  g_progMain.prog = create_program_parts(VS_QUAD_SRC, mainParts, 4, "MAIN_RAYMARCH");
  if (!g_progMain.prog) return 0;
  g_progMain.uResolution   = pglGetUniformLocation(g_progMain.prog, "uResolution");
  g_progMain.uTime         = pglGetUniformLocation(g_progMain.prog, "uTime");
  g_progMain.uFrame        = pglGetUniformLocation(g_progMain.prog, "uFrame");
  g_progMain.uScene        = pglGetUniformLocation(g_progMain.prog, "uScene");
  g_progMain.uDebug        = pglGetUniformLocation(g_progMain.prog, "uDebug");
  g_progMain.uCamPos       = pglGetUniformLocation(g_progMain.prog, "uCamPos");
  g_progMain.uCamMat       = pglGetUniformLocation(g_progMain.prog, "uCamMat");
  g_progMain.uJitter       = pglGetUniformLocation(g_progMain.prog, "uJitter");
  g_progMain.uFov          = pglGetUniformLocation(g_progMain.prog, "uFov");
  g_progMain.uSunElev      = pglGetUniformLocation(g_progMain.prog, "uSunElev");
  g_progMain.uWaterClarity = pglGetUniformLocation(g_progMain.prog, "uWaterClarity");
  g_progMain.uVolumetric   = pglGetUniformLocation(g_progMain.prog, "uVolumetric");
  g_progMain.uAudioBass    = pglGetUniformLocation(g_progMain.prog, "uAudioBass");
  g_progMain.uAudioMid     = pglGetUniformLocation(g_progMain.prog, "uAudioMid");
  g_progMain.uAudioHigh    = pglGetUniformLocation(g_progMain.prog, "uAudioHigh");

  const char *volParts[3] = { CS_VOL_HEADER_SRC, GLSL_COMMON_MATH_SRC, CS_VOL_MAIN_SRC };
  g_progVol.prog = create_compute_parts(volParts, 3, "VOLUMETRIC_COMPUTE");
  if (!g_progVol.prog) return 0;
  g_progVol.uMainTex    = pglGetUniformLocation(g_progVol.prog, "uMainTex");
  g_progVol.uMainSize   = pglGetUniformLocation(g_progVol.prog, "uMainSize");
  g_progVol.uVolSize    = pglGetUniformLocation(g_progVol.prog, "uVolSize");
  g_progVol.uTime       = pglGetUniformLocation(g_progVol.prog, "uTime");
  g_progVol.uFrame      = pglGetUniformLocation(g_progVol.prog, "uFrame");
  g_progVol.uScene      = pglGetUniformLocation(g_progVol.prog, "uScene");
  g_progVol.uCamPos     = pglGetUniformLocation(g_progVol.prog, "uCamPos");
  g_progVol.uCamMat     = pglGetUniformLocation(g_progVol.prog, "uCamMat");
  g_progVol.uFov        = pglGetUniformLocation(g_progVol.prog, "uFov");
  g_progVol.uSunElev    = pglGetUniformLocation(g_progVol.prog, "uSunElev");
  g_progVol.uVolumetric = pglGetUniformLocation(g_progVol.prog, "uVolumetric");

  g_progTAA.prog = create_program_parts(VS_QUAD_SRC, &FS_TAA_SRC, 1, "TAA_BILATERAL");
  if (!g_progTAA.prog) return 0;
  g_progTAA.uCurrTex     = pglGetUniformLocation(g_progTAA.prog, "uCurrTex");
  g_progTAA.uVolTex      = pglGetUniformLocation(g_progTAA.prog, "uVolTex");
  g_progTAA.uHistTex     = pglGetUniformLocation(g_progTAA.prog, "uHistTex");
  g_progTAA.uResolution  = pglGetUniformLocation(g_progTAA.prog, "uResolution");
  g_progTAA.uEnableTAA   = pglGetUniformLocation(g_progTAA.prog, "uEnableTAA");
  g_progTAA.uUseVol      = pglGetUniformLocation(g_progTAA.prog, "uUseVol");
  g_progTAA.uBlendFactor = pglGetUniformLocation(g_progTAA.prog, "uBlendFactor");
  g_progTAA.uCamPos      = pglGetUniformLocation(g_progTAA.prog, "uCamPos");
  g_progTAA.uCamMat      = pglGetUniformLocation(g_progTAA.prog, "uCamMat");
  g_progTAA.uPrevCamPos  = pglGetUniformLocation(g_progTAA.prog, "uPrevCamPos");
  g_progTAA.uPrevCamMat  = pglGetUniformLocation(g_progTAA.prog, "uPrevCamMat");
  g_progTAA.uFov         = pglGetUniformLocation(g_progTAA.prog, "uFov");

  g_progAdapt.prog = create_compute_parts(&CS_ADAPT_SRC, 1, "ADAPT_COMPUTE");
  if (!g_progAdapt.prog) return 0;
  g_progAdapt.uHdrTex     = pglGetUniformLocation(g_progAdapt.prog, "uHdrTex");
  g_progAdapt.uPrevLumTex = pglGetUniformLocation(g_progAdapt.prog, "uPrevLumTex");
  g_progAdapt.uDt         = pglGetUniformLocation(g_progAdapt.prog, "uDt");
  g_progAdapt.uReset      = pglGetUniformLocation(g_progAdapt.prog, "uReset");

  g_progBright.prog = create_program_parts(VS_QUAD_SRC, &FS_BRIGHT_SRC, 1, "KARIS_BRIGHT");
  if (!g_progBright.prog) return 0;
  g_progBright.uHdrTex    = pglGetUniformLocation(g_progBright.prog, "uHdrTex");
  g_progBright.uTexelSize = pglGetUniformLocation(g_progBright.prog, "uTexelSize");
  g_progBright.uThreshold = pglGetUniformLocation(g_progBright.prog, "uThreshold");

  g_progBlur.prog = create_program_parts(VS_QUAD_SRC, &FS_BLUR_SRC, 1, "SEPARABLE_BLUR");
  if (!g_progBlur.prog) return 0;
  g_progBlur.uTex = pglGetUniformLocation(g_progBlur.prog, "uTex");
  g_progBlur.uDir = pglGetUniformLocation(g_progBlur.prog, "uDir");

  g_progComp.prog = create_program_parts(VS_QUAD_SRC, &FS_COMPOSITE_SRC, 1, "OPTICAL_COMPOSITE");
  if (!g_progComp.prog) return 0;
  g_progComp.uHdrTex         = pglGetUniformLocation(g_progComp.prog, "uHdrTex");
  g_progComp.uBloomTex       = pglGetUniformLocation(g_progComp.prog, "uBloomTex");
  g_progComp.uStreakTex      = pglGetUniformLocation(g_progComp.prog, "uStreakTex");
  g_progComp.uLumTex         = pglGetUniformLocation(g_progComp.prog, "uLumTex");
  g_progComp.uResolution     = pglGetUniformLocation(g_progComp.prog, "uResolution");
  g_progComp.uTime           = pglGetUniformLocation(g_progComp.prog, "uTime");
  g_progComp.uFilter         = pglGetUniformLocation(g_progComp.prog, "uFilter");
  g_progComp.uToneMap        = pglGetUniformLocation(g_progComp.prog, "uToneMap");
  g_progComp.uAutoExp        = pglGetUniformLocation(g_progComp.prog, "uAutoExp");
  g_progComp.uExposureBias   = pglGetUniformLocation(g_progComp.prog, "uExposureBias");
  g_progComp.uBloomStrength  = pglGetUniformLocation(g_progComp.prog, "uBloomStrength");
  g_progComp.uSharpness      = pglGetUniformLocation(g_progComp.prog, "uSharpness");
  g_progComp.uChromaStrength = pglGetUniformLocation(g_progComp.prog, "uChromaStrength");
  g_progComp.uGrainStrength  = pglGetUniformLocation(g_progComp.prog, "uGrainStrength");
  g_progComp.uSplitEnabled   = pglGetUniformLocation(g_progComp.prog, "uSplitEnabled");
  g_progComp.uSplitPos       = pglGetUniformLocation(g_progComp.prog, "uSplitPos");
  g_progComp.uDebug          = pglGetUniformLocation(g_progComp.prog, "uDebug");

  return 1;
}

// ============================================================================
// CAMERA, DIRECTOR CHOREOGRAPHY & FREE-FLY CONTROLS
// ============================================================================
static void sync_orbit_from_vectors(void) {
  float d[3];
  v3_sub(d, g_cam.goalPos, g_cam.goalTarget);
  g_cam.dist = v3_len(d);
  if (g_cam.dist < 1.8f) g_cam.dist = 1.8f;
  g_cam.yaw = atan2f(d[0], d[2]);
  g_cam.pitch = clampf(asinf(clampf(d[1] / g_cam.dist, -0.99f, 0.99f)), -1.18f, 1.38f);
}

static void update_goal_from_orbit(void) {
  float cp = cosf(g_cam.pitch);
  g_cam.goalPos[0] = g_cam.goalTarget[0] + g_cam.dist * cp * sinf(g_cam.yaw);
  g_cam.goalPos[1] = g_cam.goalTarget[1] + g_cam.dist * sinf(g_cam.pitch);
  g_cam.goalPos[2] = g_cam.goalTarget[2] + g_cam.dist * cp * cosf(g_cam.yaw);
}

static void reset_camera_to_scene(int snap) {
  const ScenePreset *s = &SCENES[g_state.scene];
  memcpy(g_cam.goalPos, s->camPos, sizeof(g_cam.goalPos));
  memcpy(g_cam.goalTarget, s->target, sizeof(g_cam.goalTarget));
  sync_orbit_from_vectors();
  if (snap) {
    memcpy(g_cam.pos, g_cam.goalPos, sizeof(g_cam.pos));
    memcpy(g_cam.target, g_cam.goalTarget, sizeof(g_cam.target));
    memcpy(g_cam.prevPos, g_cam.pos, sizeof(g_cam.prevPos));
    build_camera_basis(g_cam.prevMat, g_cam.pos, g_cam.target, 0.0f);
  }
}

static void apply_scene(int idx) {
  g_state.scene = idx & 3;
  const ScenePreset *s = &SCENES[g_state.scene];
  g_state.sunElev      = s->sunElev;
  g_state.waterClarity = s->waterClarity;
  g_state.volumetric   = s->volumetric;
  g_state.exposure     = s->exposure;
  reset_camera_to_scene(1);
  g_resetHistory = 1;
  g_resetAdapt = 1;
}

static void apply_vsync_mode(void) {
  if (!wglSwapIntervalEXT) return;
  if (g_state.vsyncMode == 0) {
    wglSwapIntervalEXT(0);
  } else if (g_state.vsyncMode == 1) {
    if (!wglSwapIntervalEXT(-1)) wglSwapIntervalEXT(1);
  } else {
    wglSwapIntervalEXT(1);
  }
}

static void update_director_camera(float t) {
  if (g_state.scene == 0) {
    float a = t * 0.16f;
    float rad = 8.4f + sinf(t * 0.24f) * 1.3f;
    g_cam.goalPos[0] = sinf(a) * rad;
    g_cam.goalPos[1] = 1.85f + sinf(t * 0.31f) * 0.72f;
    g_cam.goalPos[2] = cosf(a) * rad;
    g_cam.goalTarget[0] = 0.0f;
    g_cam.goalTarget[1] = 0.95f + sinf(t * 0.22f) * 0.25f;
    g_cam.goalTarget[2] = 0.0f;
  } else if (g_state.scene == 1) {
    float zSmooth = 3.2f + sinf(t * 0.22f) * 6.2f;
    g_cam.goalPos[0] = sinf(t * 0.37f) * 1.15f;
    g_cam.goalPos[1] = 1.38f + sinf(t * 0.55f) * 0.16f;
    g_cam.goalPos[2] = zSmooth;
    g_cam.goalTarget[0] = sinf(t * 0.29f) * 0.45f;
    g_cam.goalTarget[1] = 1.25f;
    g_cam.goalTarget[2] = zSmooth - 6.0f;
  } else if (g_state.scene == 2) {
    float a = t * 0.18f;
    g_cam.goalPos[0] = sinf(a) * 11.2f;
    g_cam.goalPos[1] = 2.05f + sinf(t * 0.27f) * 1.45f;
    g_cam.goalPos[2] = cosf(a) * 11.2f;
    g_cam.goalTarget[0] = 0.0f;
    g_cam.goalTarget[1] = 0.0f;
    g_cam.goalTarget[2] = 0.0f;
  } else {
    float a = t * 0.17f + 0.7f;
    float rad = 6.2f + sinf(t * 0.25f) * 0.7f;
    g_cam.goalPos[0] = sinf(a) * rad;
    g_cam.goalPos[1] = 2.35f + sinf(t * 0.32f) * 0.85f;
    g_cam.goalPos[2] = cosf(a) * rad;
    g_cam.goalTarget[0] = 0.0f;
    g_cam.goalTarget[1] = -0.35f;
    g_cam.goalTarget[2] = 0.0f;
  }
  sync_orbit_from_vectors();
}

static void update_free_fly(float dt) {
  int moving = g_keys['W'] || g_keys['S'] || g_keys['A'] || g_keys['D'] || g_keys['Q'] || g_keys['E'];
  if (!moving) return;

  g_state.cinema = 0;
  float basis[9];
  build_camera_basis(basis, g_cam.goalPos, g_cam.goalTarget, 0.0f);
  const float right[3] = { basis[0], basis[1], basis[2] };
  const float up[3]    = { basis[3], basis[4], basis[5] };
  const float fwd[3]   = { basis[6], basis[7], basis[8] };

  float move[3] = { 0.0f, 0.0f, 0.0f };
  if (g_keys['W']) v3_add(move, move, fwd);
  if (g_keys['S']) v3_sub(move, move, fwd);
  if (g_keys['D']) v3_add(move, move, right);
  if (g_keys['A']) v3_sub(move, move, right);
  if (g_keys['E']) v3_add(move, move, up);
  if (g_keys['Q']) v3_sub(move, move, up);

  if (v3_len(move) > 1e-4f) {
    float speed = g_keys[VK_SHIFT] ? 7.5f : 3.4f;
    float dir[3], delta[3];
    v3_norm(dir, move);
    v3_scale(delta, dir, speed * dt);
    v3_add(g_cam.goalPos, g_cam.goalPos, delta);
    v3_add(g_cam.goalTarget, g_cam.goalTarget, delta);
    if (g_state.scene == 1) {
      g_cam.goalPos[0] = clampf(g_cam.goalPos[0], -3.9f, 3.9f);
      g_cam.goalPos[1] = clampf(g_cam.goalPos[1],  0.25f, 4.1f);
      g_cam.goalPos[2] = clampf(g_cam.goalPos[2], -11.2f, 11.8f);
    }
    sync_orbit_from_vectors();
  }
}

static void update_continuous_keys(float dt) {
  if (g_keys[VK_UP])    g_state.sunElev      = clampf(g_state.sunElev + 0.45f * dt, 0.06f, 1.25f);
  if (g_keys[VK_DOWN])  g_state.sunElev      = clampf(g_state.sunElev - 0.45f * dt, 0.06f, 1.25f);
  if (g_keys[VK_RIGHT]) g_state.waterClarity = clampf(g_state.waterClarity + 0.70f * dt, 0.25f, 2.40f);
  if (g_keys[VK_LEFT])  g_state.waterClarity = clampf(g_state.waterClarity - 0.70f * dt, 0.25f, 2.40f);
  if (g_keys[0xDB])     g_state.splitPos     = clampf(g_state.splitPos - 0.45f * dt, 0.04f, 0.96f);
  if (g_keys[0xDD])     g_state.splitPos     = clampf(g_state.splitPos + 0.45f * dt, 0.04f, 0.96f);
}

// ============================================================================
// FULLSCREEN & WIN32 MESSAGE HANDLER
// ============================================================================
static void toggle_fullscreen(void) {
  DWORD style = (DWORD)GetWindowLongA(g_hwnd, GWL_STYLE);
  if (!g_fullscreen) {
    MONITORINFO mi = { sizeof(mi) };
    if (GetWindowPlacement(g_hwnd, &g_wpPrev) &&
        GetMonitorInfoA(MonitorFromWindow(g_hwnd, MONITOR_DEFAULTTOPRIMARY), &mi)) {
      SetWindowLongA(g_hwnd, GWL_STYLE, (LONG)(style & ~WS_OVERLAPPEDWINDOW));
      SetWindowPos(g_hwnd, HWND_TOP,
        mi.rcMonitor.left, mi.rcMonitor.top,
        mi.rcMonitor.right - mi.rcMonitor.left,
        mi.rcMonitor.bottom - mi.rcMonitor.top,
        SWP_NOOWNERZORDER | SWP_FRAMECHANGED);
      g_fullscreen = 1;
    }
  } else {
    SetWindowLongA(g_hwnd, GWL_STYLE, (LONG)(style | WS_OVERLAPPEDWINDOW));
    SetWindowPlacement(g_hwnd, &g_wpPrev);
    SetWindowPos(g_hwnd, NULL, 0, 0, 0, 0,
      SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER | SWP_NOOWNERZORDER | SWP_FRAMECHANGED);
    g_fullscreen = 0;
  }
  g_needResize = 1;
}

static LRESULT CALLBACK wnd_proc(HWND h, UINT msg, WPARAM w, LPARAM l) {
  switch (msg) {
    case WM_CLOSE:
    case WM_DESTROY:
      g_running = 0;
      PostQuitMessage(0);
      return 0;

    case WM_SIZE: {
      int nw = (int)LOWORD(l), nh = (int)HIWORD(l);
      if (nw > 0 && nh > 0) { g_winW = nw; g_winH = nh; g_needResize = 1; }
      return 0;
    }

    case WM_KEYDOWN: {
      int vk = (int)(w & 255);
      int firstPress = ((l & (1 << 30)) == 0);
      g_keys[vk] = 1;
      if (firstPress) {
        if      (vk == '1') apply_scene(0);
        else if (vk == '2') apply_scene(1);
        else if (vk == '3') apply_scene(2);
        else if (vk == '4') apply_scene(3);
        else if (vk == VK_SPACE) { g_state.cinema = !g_state.cinema; }
        else if (vk == 'F') { g_state.filter = (g_state.filter + 1) & 3; g_resetHistory = 1; }
        else if (vk == 'T') { g_state.toneMap = (g_state.toneMap + 1) & 3; }
        else if (vk == 'V') { g_state.debug = (g_state.debug + 1) & 3; g_resetHistory = 1; }
        else if (vk == 'B') { g_state.split = !g_state.split; }
        else if (vk == 'G') { g_state.taa = !g_state.taa; g_resetHistory = 1; }
        else if (vk == 'X') { g_state.autoExp = !g_state.autoExp; g_resetAdapt = 1; }
        else if (vk == 'R') { reset_camera_to_scene(0); g_resetHistory = 1; }
        else if (vk == 'U') { g_state.vsyncMode = (g_state.vsyncMode + 1) % 3; apply_vsync_mode(); }
        else if (vk == 0xBD) { g_state.exposure = clampf(g_state.exposure - 0.15f, -2.2f, 2.2f); }
        else if (vk == 0xBB) { g_state.exposure = clampf(g_state.exposure + 0.15f, -2.2f, 2.2f); }
        else if (vk == VK_F5) { g_state.renderScale = 0.50f; g_needResize = 1; }
        else if (vk == VK_F6) { g_state.renderScale = 0.75f; g_needResize = 1; }
        else if (vk == VK_F7) { g_state.renderScale = 1.00f; g_needResize = 1; }
        else if (vk == VK_F8) { g_state.renderScale = 1.25f; g_needResize = 1; }
        else if (vk == VK_F11) { toggle_fullscreen(); }
        else if (vk == VK_ESCAPE) { g_running = 0; PostQuitMessage(0); }
      }
      return 0;
    }

    case WM_KEYUP:
      g_keys[w & 255] = 0;
      return 0;

    case WM_LBUTTONDOWN:
    case WM_RBUTTONDOWN:
      g_cam.dragging = 1;
      g_cam.dragMode = (msg == WM_RBUTTONDOWN || g_keys[VK_SHIFT]) ? 1 : 0;
      g_cam.lastX = (int)(short)LOWORD(l);
      g_cam.lastY = (int)(short)HIWORD(l);
      g_state.cinema = 0;
      SetCapture(h);
      return 0;

    case WM_LBUTTONUP:
    case WM_RBUTTONUP:
      g_cam.dragging = 0;
      ReleaseCapture();
      return 0;

    case WM_MOUSEMOVE:
      if (g_cam.dragging) {
        int mx = (int)(short)LOWORD(l), my = (int)(short)HIWORD(l);
        int dx = mx - g_cam.lastX, dy = my - g_cam.lastY;
        g_cam.lastX = mx; g_cam.lastY = my;
        if (g_cam.dragMode == 0) {
          g_cam.yaw   -= (float)dx * 0.0052f;
          g_cam.pitch  = clampf(g_cam.pitch + (float)dy * 0.0046f, -1.15f, 1.38f);
          update_goal_from_orbit();
        } else {
          float basis[9], shiftR[3], shiftU[3], shift[3];
          build_camera_basis(basis, g_cam.goalPos, g_cam.goalTarget, 0.0f);
          const float right[3] = { basis[0], basis[1], basis[2] };
          const float up[3]    = { basis[3], basis[4], basis[5] };
          float panScale = g_cam.dist * 0.0014f;
          v3_scale(shiftR, right, -(float)dx * panScale);
          v3_scale(shiftU, up,     (float)dy * panScale);
          v3_add(shift, shiftR, shiftU);
          v3_add(g_cam.goalPos, g_cam.goalPos, shift);
          v3_add(g_cam.goalTarget, g_cam.goalTarget, shift);
        }
      }
      return 0;

    case WM_MOUSEWHEEL: {
      short delta = (short)HIWORD(w);
      g_state.cinema = 0;
      g_cam.dist = clampf(g_cam.dist * expf(-(float)delta * 0.0009f), 2.0f, 26.0f);
      update_goal_from_orbit();
      return 0;
    }
  }
  return DefWindowProcA(h, msg, w, l);
}

// ============================================================================
// OPENGL 4.6 CORE BOOTSTRAP (WITH AUTOMATIC FALLBACK DOWN TO 4.3 CORE)
// ============================================================================
static int init_gl_context(HWND hwnd) {
  g_hdc = GetDC(hwnd);
  PIXELFORMATDESCRIPTOR pfd;
  memset(&pfd, 0, sizeof(pfd));
  pfd.nSize        = sizeof(pfd);
  pfd.nVersion     = 1;
  pfd.dwFlags      = PFD_DRAW_TO_WINDOW | PFD_SUPPORT_OPENGL | PFD_DOUBLEBUFFER;
  pfd.iPixelType   = PFD_TYPE_RGBA;
  pfd.cColorBits   = 32;
  pfd.cDepthBits   = 24;
  pfd.cStencilBits = 8;
  pfd.iLayerType   = PFD_MAIN_PLANE;

  int pf = ChoosePixelFormat(g_hdc, &pfd);
  if (!pf || !SetPixelFormat(g_hdc, pf, &pfd)) return 0;

  HGLRC tempRC = wglCreateContext(g_hdc);
  if (!tempRC || !wglMakeCurrent(g_hdc, tempRC)) return 0;

  wglCreateContextAttribsARB = (PFNWGLCREATECONTEXTATTRIBSARBPROC)wglGetProcAddress("wglCreateContextAttribsARB");
  if (wglCreateContextAttribsARB) {
    const int versions[4][2] = { {4, 6}, {4, 5}, {4, 4}, {4, 3} };
    HGLRC coreRC = NULL;
    for (int i = 0; i < 4 && !coreRC; i++) {
      const int attribs[] = {
        WGL_CONTEXT_MAJOR_VERSION_ARB, versions[i][0],
        WGL_CONTEXT_MINOR_VERSION_ARB, versions[i][1],
        WGL_CONTEXT_PROFILE_MASK_ARB,  WGL_CONTEXT_CORE_PROFILE_BIT_ARB,
        0
      };
      coreRC = wglCreateContextAttribsARB(g_hdc, 0, attribs);
    }
    if (coreRC) {
      wglMakeCurrent(NULL, NULL);
      wglDeleteContext(tempRC);
      wglMakeCurrent(g_hdc, coreRC);
      g_hrc = coreRC;
    } else {
      g_hrc = tempRC;
    }
  } else {
    g_hrc = tempRC;
  }

  if (!load_gl_functions()) return 0;

  // Probe GL_NVX_gpu_memory_info safely in Core Profile
  while (glGetError() != GL_NO_ERROR) {}
  GLint totalKb = 0;
  glGetIntegerv(GL_GPU_MEMORY_INFO_DEDICATED_VIDMEM_NVX, &totalKb);
  if (glGetError() == GL_NO_ERROR && totalKb > 0) g_hasNvMemInfo = 1;

  return 1;
}

static void bind_tex(int unit, GLuint tex, GLint loc) {
  pglActiveTexture(GL_TEXTURE0 + (GLenum)unit);
  glBindTexture(GL_TEXTURE_2D, tex);
  pglUniform1i(loc, unit);
}

static void draw_fs(void) {
  glDrawArrays(GL_TRIANGLES, 0, 3);
}

// ============================================================================
// ENTRY POINT & 7-PASS NVIDIA COMPUTE + HDR REAL-TIME LOOP
// ============================================================================
int WINAPI WinMain(HINSTANCE hInst, HINSTANCE hPrev, LPSTR cmd, int show) {
  (void)hPrev; (void)cmd; (void)show;
  init_halton();
  nvml_try_init();

  WNDCLASSA wc;
  memset(&wc, 0, sizeof(wc));
  wc.style         = CS_OWNDC;
  wc.lpfnWndProc   = wnd_proc;
  wc.hInstance     = hInst;
  wc.lpszClassName = "AetherionV25NV";
  wc.hCursor       = LoadCursor(NULL, IDC_ARROW);
  RegisterClassA(&wc);

  RECT wr = { 0, 0, g_winW, g_winH };
  AdjustWindowRect(&wr, WS_OVERLAPPEDWINDOW, FALSE);
  g_hwnd = CreateWindowA(
    "AetherionV25NV",
    "AETHERION V2.5 // Initializing NVIDIA OpenGL 4.6 Compute + NVML...",
    WS_OVERLAPPEDWINDOW | WS_VISIBLE,
    CW_USEDEFAULT, CW_USEDEFAULT,
    wr.right - wr.left, wr.bottom - wr.top,
    NULL, NULL, hInst, NULL
  );

  if (!init_gl_context(g_hwnd)) {
    MessageBoxA(g_hwnd, "OpenGL 4.3+ Compute context creation failed.", "AETHERION V2.5", MB_OK | MB_ICONERROR);
    nvml_cleanup();
    return 1;
  }
  if (!init_shaders()) {
    nvml_cleanup();
    return 1;
  }

  pglGenVertexArrays(1, &g_emptyVAO);
  pglBindVertexArray(g_emptyVAO);
  if (pglGenQueries) pglGenQueries(2, g_timerQuery);
  glDisable(GL_DEPTH_TEST);
  glDisable(GL_BLEND);
  apply_vsync_mode();

  RECT rc;
  GetClientRect(g_hwnd, &rc);
  g_winW = rc.right - rc.left;
  g_winH = rc.bottom - rc.top;
  rebuild_targets();

  g_cam.fov = 54.0f * PI_F / 180.0f;
  apply_scene(0);

  LARGE_INTEGER freq, tStart, tLast, tNow;
  QueryPerformanceFrequency(&freq);
  QueryPerformanceCounter(&tStart);
  tLast = tStart;

  int   frameCount = 0;
  float fpsAccum = 0.0f;
  int   fpsFrames = 0;
  MSG   msg;

  while (g_running) {
    while (PeekMessageA(&msg, NULL, 0, 0, PM_REMOVE)) {
      if (msg.message == WM_QUIT) g_running = 0;
      TranslateMessage(&msg);
      DispatchMessageA(&msg);
    }
    if (!g_running) break;

    if (g_needResize) {
      rebuild_targets();
      g_needResize = 0;
    }

    QueryPerformanceCounter(&tNow);
    float dt = clampf((float)(tNow.QuadPart - tLast.QuadPart) / (float)freq.QuadPart, 0.001f, 0.1f);
    tLast = tNow;
    float elapsed = (float)(tNow.QuadPart - tStart.QuadPart) / (float)freq.QuadPart;

    // Live NVIDIA NVML + GPU Timer Telemetry (~3x/sec)
    fpsAccum += dt;
    fpsFrames++;
    if (fpsAccum >= 0.30f || frameCount < 2) {
      float fps = (float)fpsFrames / (fpsAccum > 1e-4f ? fpsAccum : 0.016f);
      nvml_poll();

      char nvBuf[128] = "";
      if (g_nvml.active) {
        snprintf(nvBuf, sizeof(nvBuf), " | %s %u%% %uMHz %uC %.0fW",
          g_nvml.name[0] ? g_nvml.name : "NV-GPU",
          g_nvml.gpuUtil, g_nvml.clkMHz, g_nvml.tempC, g_nvml.powerW);
      } else if (g_hasNvMemInfo) {
        GLint totalKb = 0, availKb = 0;
        glGetIntegerv(GL_GPU_MEMORY_INFO_DEDICATED_VIDMEM_NVX, &totalKb);
        glGetIntegerv(GL_GPU_MEMORY_INFO_CURRENT_AVAILABLE_VIDMEM_NVX, &availKb);
        snprintf(nvBuf, sizeof(nvBuf), " | VRAM %.1f/%.1fGB",
          (float)(totalKb - availKb) / 1048576.0f, (float)totalKb / 1048576.0f);
      }

      char title[320];
      snprintf(title, sizeof(title),
        "AETHERION V2.5 [%s] | %.0f FPS (GPU %.1fms) | %dx%d%s | %s · %s · %s | %s",
        SCENES[g_state.scene].name, fps, g_gpuMs, g_renderW, g_renderH, nvBuf,
        FILTER_NAMES[g_state.filter], TM_NAMES[g_state.toneMap], DBG_NAMES[g_state.debug],
        VSYNC_NAMES[g_state.vsyncMode]
      );
      SetWindowTextA(g_hwnd, title);
      fpsAccum = 0.0f;
      fpsFrames = 0;
    }

    // Update Camera & Continuous Hotkeys
    update_continuous_keys(dt);
    if (g_state.cinema) update_director_camera(elapsed);
    else                update_free_fly(dt);

    float smooth = 1.0f - expf(-dt * 7.5f);
    for (int i = 0; i < 3; i++) {
      g_cam.pos[i]    = lerpf(g_cam.pos[i],    g_cam.goalPos[i],    smooth);
      g_cam.target[i] = lerpf(g_cam.target[i], g_cam.goalTarget[i], smooth);
    }

    float renderPos[3]    = { g_cam.pos[0],    g_cam.pos[1],    g_cam.pos[2] };
    float renderTarget[3] = { g_cam.target[0], g_cam.target[1], g_cam.target[2] };
    float rollRad = 0.0f;
    float targetFov = (g_state.filter == 1 ? 72.0f : 54.0f) * PI_F / 180.0f;
    g_cam.fov = lerpf(g_cam.fov, targetFov, 1.0f - expf(-dt * 8.0f));

    if (g_state.filter == 1) {
      renderPos[0]    += sinf(elapsed * 1.9f) * 0.025f + sinf(elapsed * 4.7f) * 0.008f;
      renderPos[1]    += cosf(elapsed * 2.3f) * 0.028f + sinf(elapsed * 5.9f) * 0.009f;
      renderTarget[1] += sinf(elapsed * 1.4f) * 0.035f;
      rollRad          = sinf(elapsed * 1.25f) * 0.024f + cosf(elapsed * 3.1f) * 0.007f;
    }

    float camMat[9];
    build_camera_basis(camMat, renderPos, renderTarget, rollRad);

    float jx = (g_state.taa && g_state.debug == 0) ? g_halton[frameCount & 15][0] : 0.0f;
    float jy = (g_state.taa && g_state.debug == 0) ? g_halton[frameCount & 15][1] : 0.0f;

    // Non-blocking GPU Timer Start
    if (pglBeginQuery && g_timerQuery[0]) {
      if (g_queryReady) {
        GLint avail = 0;
        pglGetQueryObjectiv(g_timerQuery[1 - g_queryIdx], GL_QUERY_RESULT_AVAILABLE, &avail);
        if (avail) {
          uint64_t ns = 0;
          pglGetQueryObjectui64v(g_timerQuery[1 - g_queryIdx], GL_QUERY_RESULT, &ns);
          g_gpuMs = lerpf(g_gpuMs, (float)ns * 1e-6f, g_gpuMs < 0.01f ? 1.0f : 0.25f);
        }
      }
      pglBeginQuery(GL_TIME_ELAPSED, g_timerQuery[g_queryIdx]);
    }

    // ========================================================================
    // PASS 1: MAIN HDR RAYMARCHER (2-Medium Water + Fast Shadow SDF + BH)
    // ========================================================================
    pglBindFramebuffer(GL_FRAMEBUFFER, g_fboMain.fbo);
    glViewport(0, 0, g_renderW, g_renderH);
    pglUseProgram(g_progMain.prog);
    pglUniform2f(g_progMain.uResolution, (float)g_renderW, (float)g_renderH);
    pglUniform1f(g_progMain.uTime, elapsed);
    pglUniform1i(g_progMain.uFrame, frameCount);
    pglUniform1i(g_progMain.uScene, g_state.scene);
    pglUniform1i(g_progMain.uDebug, g_state.debug);
    pglUniform3fv(g_progMain.uCamPos, 1, renderPos);
    pglUniformMatrix3fv(g_progMain.uCamMat, 1, GL_FALSE, camMat);
    pglUniform2f(g_progMain.uJitter, jx, jy);
    pglUniform1f(g_progMain.uFov, g_cam.fov);
    pglUniform1f(g_progMain.uSunElev, g_state.sunElev);
    pglUniform1f(g_progMain.uWaterClarity, g_state.waterClarity);
    pglUniform1f(g_progMain.uVolumetric, g_state.volumetric);
    pglUniform1f(g_progMain.uAudioBass, 0.0f);
    pglUniform1f(g_progMain.uAudioMid, 0.0f);
    pglUniform1f(g_progMain.uAudioHigh, 0.0f);
    draw_fs();

    // ========================================================================
    // PASS 2: HALF-RES 8x4 WARP-ALIGNED VOLUMETRIC GOD-RAY COMPUTE SHADER
    // ========================================================================
    int useVol = (g_state.debug == 0 && g_state.scene != 2 && g_state.volumetric > 0.005f) ? 1 : 0;
    if (useVol) {
      pglBindFramebuffer(GL_FRAMEBUFFER, 0);
      pglUseProgram(g_progVol.prog);
      bind_tex(0, g_fboMain.tex, g_progVol.uMainTex);
      pglBindImageTexture(0, g_fboVol.tex, 0, GL_FALSE, 0, GL_WRITE_ONLY, GL_RGBA16F);
      pglUniform2i(g_progVol.uMainSize, g_renderW, g_renderH);
      pglUniform2i(g_progVol.uVolSize, g_fboVol.w, g_fboVol.h);
      pglUniform1f(g_progVol.uTime, elapsed);
      pglUniform1i(g_progVol.uFrame, frameCount);
      pglUniform1i(g_progVol.uScene, g_state.scene);
      pglUniform3fv(g_progVol.uCamPos, 1, renderPos);
      pglUniformMatrix3fv(g_progVol.uCamMat, 1, GL_FALSE, camMat);
      pglUniform1f(g_progVol.uFov, g_cam.fov);
      pglUniform1f(g_progVol.uSunElev, g_state.sunElev);
      pglUniform1f(g_progVol.uVolumetric, g_state.volumetric);
      pglDispatchCompute((GLuint)((g_fboVol.w + 7) / 8), (GLuint)((g_fboVol.h + 3) / 4), 1);
      pglMemoryBarrier(GL_TEXTURE_FETCH_BARRIER_BIT | GL_SHADER_IMAGE_ACCESS_BARRIER_BIT);
    }

    // ========================================================================
    // PASS 3: BILATERAL VOLUMETRIC UPSAMPLE + TEMPORAL ANTI-ALIASING
    // ========================================================================
    RenderTarget *taaRead  = &g_fboTAA[g_taaIdx];
    RenderTarget *taaWrite = &g_fboTAA[1 - g_taaIdx];
    pglBindFramebuffer(GL_FRAMEBUFFER, taaWrite->fbo);
    glViewport(0, 0, g_renderW, g_renderH);
    pglUseProgram(g_progTAA.prog);
    bind_tex(0, g_fboMain.tex, g_progTAA.uCurrTex);
    bind_tex(1, g_fboVol.tex,  g_progTAA.uVolTex);
    bind_tex(2, taaRead->tex,  g_progTAA.uHistTex);
    pglUniform2f(g_progTAA.uResolution, (float)g_renderW, (float)g_renderH);
    pglUniform1i(g_progTAA.uEnableTAA, (g_state.taa && g_state.debug == 0 && !g_resetHistory) ? 1 : 0);
    pglUniform1i(g_progTAA.uUseVol, useVol);
    pglUniform1f(g_progTAA.uBlendFactor, g_resetHistory ? 0.0f : 0.84f);
    pglUniform3fv(g_progTAA.uCamPos, 1, renderPos);
    pglUniformMatrix3fv(g_progTAA.uCamMat, 1, GL_FALSE, camMat);
    pglUniform3fv(g_progTAA.uPrevCamPos, 1, g_cam.prevPos);
    pglUniformMatrix3fv(g_progTAA.uPrevCamMat, 1, GL_FALSE, g_cam.prevMat);
    pglUniform1f(g_progTAA.uFov, g_cam.fov);
    draw_fs();
    g_taaIdx = 1 - g_taaIdx;
    RenderTarget *hdrResolved = &g_fboTAA[g_taaIdx];

    // ========================================================================
    // PASS 4: 8x8 SHARED-MEMORY PARALLEL REDUCTION EYE ADAPTATION COMPUTE
    // ========================================================================
    RenderTarget *lumRead  = &g_fboLum[g_lumIdx];
    RenderTarget *lumWrite = &g_fboLum[1 - g_lumIdx];
    pglBindFramebuffer(GL_FRAMEBUFFER, 0);
    pglUseProgram(g_progAdapt.prog);
    bind_tex(0, hdrResolved->tex, g_progAdapt.uHdrTex);
    bind_tex(1, lumRead->tex,     g_progAdapt.uPrevLumTex);
    pglBindImageTexture(0, lumWrite->tex, 0, GL_FALSE, 0, GL_WRITE_ONLY, GL_RGBA16F);
    pglUniform1f(g_progAdapt.uDt, dt);
    pglUniform1i(g_progAdapt.uReset, g_resetAdapt ? 1 : 0);
    pglDispatchCompute(1, 1, 1);
    pglMemoryBarrier(GL_TEXTURE_FETCH_BARRIER_BIT | GL_SHADER_IMAGE_ACCESS_BARRIER_BIT);
    g_lumIdx = 1 - g_lumIdx;
    RenderTarget *lumCurrent = &g_fboLum[g_lumIdx];

    // ========================================================================
    // PASS 5: KARIS BRIGHT-PASS & PACKED R11G11B10F SEPARABLE HDR BLOOM
    // ========================================================================
    int bW = g_fboBloom[0].w, bH = g_fboBloom[0].h;
    pglBindFramebuffer(GL_FRAMEBUFFER, g_fboBloom[0].fbo);
    glViewport(0, 0, bW, bH);
    pglUseProgram(g_progBright.prog);
    bind_tex(0, hdrResolved->tex, g_progBright.uHdrTex);
    pglUniform2f(g_progBright.uTexelSize, 1.0f / (float)g_renderW, 1.0f / (float)g_renderH);
    pglUniform1f(g_progBright.uThreshold, 1.05f);
    draw_fs();

    pglUseProgram(g_progBlur.prog);
    for (int p = 0; p < 2; p++) {
      pglBindFramebuffer(GL_FRAMEBUFFER, g_fboBloom[1].fbo);
      glViewport(0, 0, bW, bH);
      bind_tex(0, g_fboBloom[0].tex, g_progBlur.uTex);
      pglUniform2f(g_progBlur.uDir, (1.4f + (float)p * 0.9f) / (float)bW, 0.0f);
      draw_fs();

      pglBindFramebuffer(GL_FRAMEBUFFER, g_fboBloom[0].fbo);
      glViewport(0, 0, bW, bH);
      bind_tex(0, g_fboBloom[1].tex, g_progBlur.uTex);
      pglUniform2f(g_progBlur.uDir, 0.0f, (1.4f + (float)p * 0.9f) / (float)bH);
      draw_fs();
    }

    // ========================================================================
    // PASS 6: QUARTER-RES HORIZONTAL ANAMORPHIC LENS STREAKS
    // ========================================================================
    int sW = g_fboStreak[0].w, sH = g_fboStreak[0].h;
    pglBindFramebuffer(GL_FRAMEBUFFER, g_fboStreak[0].fbo);
    glViewport(0, 0, sW, sH);
    pglUseProgram(g_progBright.prog);
    bind_tex(0, hdrResolved->tex, g_progBright.uHdrTex);
    pglUniform2f(g_progBright.uTexelSize, 2.0f / (float)g_renderW, 2.0f / (float)g_renderH);
    pglUniform1f(g_progBright.uThreshold, 1.85f);
    draw_fs();

    pglUseProgram(g_progBlur.prog);
    for (int p = 0; p < 3; p++) {
      pglBindFramebuffer(GL_FRAMEBUFFER, g_fboStreak[1].fbo);
      glViewport(0, 0, sW, sH);
      bind_tex(0, g_fboStreak[0].tex, g_progBlur.uTex);
      pglUniform2f(g_progBlur.uDir, (2.6f + (float)p * 2.2f) / (float)sW, 0.0f);
      draw_fs();

      pglBindFramebuffer(GL_FRAMEBUFFER, g_fboStreak[0].fbo);
      glViewport(0, 0, sW, sH);
      bind_tex(0, g_fboStreak[1].tex, g_progBlur.uTex);
      pglUniform2f(g_progBlur.uDir, (3.2f + (float)p * 2.6f) / (float)sW, 0.0f);
      draw_fs();
    }

    // ========================================================================
    // PASS 7: FINAL CINEMATIC / UE5 BODYCAM OPTICAL FILTER & RCAS COMPOSITOR
    // ========================================================================
    pglBindFramebuffer(GL_FRAMEBUFFER, 0);
    glViewport(0, 0, g_winW, g_winH);
    pglUseProgram(g_progComp.prog);
    bind_tex(0, hdrResolved->tex,   g_progComp.uHdrTex);
    bind_tex(1, g_fboBloom[0].tex,  g_progComp.uBloomTex);
    bind_tex(2, g_fboStreak[0].tex, g_progComp.uStreakTex);
    bind_tex(3, lumCurrent->tex,    g_progComp.uLumTex);
    pglUniform2f(g_progComp.uResolution, (float)g_winW, (float)g_winH);
    pglUniform1f(g_progComp.uTime, elapsed);
    pglUniform1i(g_progComp.uFilter, g_state.filter);
    pglUniform1i(g_progComp.uToneMap, g_state.toneMap);
    pglUniform1i(g_progComp.uAutoExp, g_state.autoExp);
    pglUniform1f(g_progComp.uExposureBias, g_state.exposure);
    pglUniform1f(g_progComp.uBloomStrength, g_state.bloom);
    pglUniform1f(g_progComp.uSharpness, g_state.sharp);
    pglUniform1f(g_progComp.uChromaStrength, g_state.chroma);
    pglUniform1f(g_progComp.uGrainStrength, g_state.grain);
    pglUniform1i(g_progComp.uSplitEnabled, g_state.split);
    pglUniform1f(g_progComp.uSplitPos, g_state.splitPos);
    pglUniform1i(g_progComp.uDebug, g_state.debug);
    draw_fs();

    if (pglEndQuery && g_timerQuery[0]) {
      pglEndQuery(GL_TIME_ELAPSED);
      g_queryIdx = 1 - g_queryIdx;
      g_queryReady = 1;
    }

    SwapBuffers(g_hdc);

    memcpy(g_cam.prevPos, renderPos, sizeof(g_cam.prevPos));
    memcpy(g_cam.prevMat, camMat, sizeof(g_cam.prevMat));
    g_resetHistory = 0;
    g_resetAdapt = 0;
    frameCount++;
  }

  destroy_target(&g_fboMain);
  destroy_target(&g_fboVol);
  destroy_target(&g_fboTAA[0]);
  destroy_target(&g_fboTAA[1]);
  destroy_target(&g_fboLum[0]);
  destroy_target(&g_fboLum[1]);
  destroy_target(&g_fboBloom[0]);
  destroy_target(&g_fboBloom[1]);
  destroy_target(&g_fboStreak[0]);
  destroy_target(&g_fboStreak[1]);

  wglMakeCurrent(NULL, NULL);
  wglDeleteContext(g_hrc);
  ReleaseDC(g_hwnd, g_hdc);
  nvml_cleanup();
  return 0;
}
