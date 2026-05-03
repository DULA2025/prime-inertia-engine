#define GL_GLEXT_PROTOTYPES
#include <GL/glut.h>
#include <GL/gl.h>
#include <GL/glext.h>
#include <alsa/asoundlib.h>
#include <pthread.h>
#include <sys/time.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define CLAMP(x, low, high) (((x) > (high)) ? (high) : (((x) < (low)) ? (low) : (x)))
#define MAX(a, b) (((a) > (b)) ? (a) : (b))
#define MIN(a, b) (((a) < (b)) ? (a) : (b))

// --- State Variables ---
float currentDose = 4.0f;
float currentValence = 1.0f;
float currentLog = 0.0f;
float currentSpeed = 1.0f;
float currentF = 2.8f;
float currentB = 28.87f;
float camMode = 0.0f;
int isCameraMoving = 1;
int showHud = 1;
int audioEnabled = 1; 
float currentCamZ = 0.0f;
float accumulatedTime = 0.0f;

float currentMouseX = 0.0f;
float currentMouseY = 0.0f;
int rawMouseX = 0;
int rawMouseY = 0;

int special_keys[256] = {0};

// FPS Tracking
int frameCount = 0;
float fpsTimer = 0.0f;
int currentFPS = 0;
double lastTime = 0.0;

// GL Locations
GLint locTime, locCamZ, locRes, locMouse, locCamMode, locDose, locValence, locLogWarp, locF, locB;
GLuint shaderProgram;

// --- Audio Streaming Engine (ALSA) ---
#define SAMPLE_RATE 44100
#define BLOCK_SAMPLES 4410 

float globalAudioTime = 0.0f;
float b0 = 0, b1 = 0, b2 = 0, b3 = 0, b4 = 0, b5 = 0, b6 = 0; 
float noiseFilterState = 0.0f; 

void FillAudioBuffer(int16_t* buffer) {
    if (!audioEnabled) {
        memset(buffer, 0, BLOCK_SAMPLES * 2 * sizeof(int16_t));
        return;
    }

    for (int i = 0; i < BLOCK_SAMPLES; i++) {
        float t = globalAudioTime;
        globalAudioTime += 1.0f / SAMPLE_RATE;
        
        // 1. Generate Raw Pink Noise
        float white = ((float)rand() / RAND_MAX) * 2.0f - 1.0f;
        b0 = 0.99886f * b0 + white * 0.0555179f; b1 = 0.99332f * b1 + white * 0.0750759f;
        b2 = 0.96900f * b2 + white * 0.1538520f; b3 = 0.86650f * b3 + white * 0.3104856f;
        b4 = 0.55000f * b4 + white * 0.5329522f; b5 = -0.7616f * b5 - white * 0.0168980f;
        float noise = (b0 + b1 + b2 + b3 + b4 + b5 + b6 + white * 0.5362f) * 0.11f;
        b6 = white * 0.115926f;

        // 2. Modulate Deep Ocean IIR Low-Pass Filter
        float oceanLFO = sinf(2.0f * 3.14159f * 0.1f * t); 
        float cutoffFreq = 500.0f + 350.0f * oceanLFO;     
        float alpha = (2.0f * 3.14159f * cutoffFreq) / SAMPLE_RATE;
        noiseFilterState += alpha * (noise - noiseFilterState); 
        float finalOcean = noiseFilterState * (0.2f + 0.15f * oceanLFO) * 2.5f;

        // 3. Generate Heartbeat
        float beatT = fmodf(t, 60.0f / 54.0f);
        float heartbeat = 0.0f;
        if (beatT < 0.2f) {
            heartbeat = sinf(2.0f * 3.14159f * 45.0f * beatT) * expf(-25.0f * beatT);
        } else if (beatT > 0.3f && beatT < 0.5f) {
            float t_dub = beatT - 0.3f;
            heartbeat = sinf(2.0f * 3.14159f * 50.0f * t_dub) * expf(-25.0f * t_dub) * 0.8f;
        }

        // 4. Generate Binaural Sine Waves & Spatial Pan
        float pan8D = sinf(2.0f * 3.14159f * 0.0625f * t);
        float oscL = sinf(2.0f * 3.14159f * 137.036f * t);
        float oscR = sinf(2.0f * 3.14159f * 141.986f * t);

        // 5. Final Mixdown
        float mixL = oscL * 0.4f + finalOcean * (1.0f - pan8D) + heartbeat * 0.5f;
        float mixR = oscR * 0.4f + finalOcean * (1.0f + pan8D) + heartbeat * 0.5f;

        buffer[i * 2] = (int16_t)(MAX(-1.0f, MIN(1.0f, mixL)) * 32767.0f);
        buffer[i * 2 + 1] = (int16_t)(MAX(-1.0f, MIN(1.0f, mixR)) * 32767.0f);
    }
}

void* AudioThread(void* param) {
    snd_pcm_t *pcm_handle;
    if (snd_pcm_open(&pcm_handle, "default", SND_PCM_STREAM_PLAYBACK, 0) < 0) {
        printf("ERROR: ALSA failed to open audio device.\n");
        return NULL;
    }
    
    // Configure ALSA for Real-Time Low Latency
    snd_pcm_set_params(pcm_handle, SND_PCM_FORMAT_S16_LE, SND_PCM_ACCESS_RW_INTERLEAVED, 2, SAMPLE_RATE, 1, 50000);
    
    int16_t buffer[BLOCK_SAMPLES * 2];
    while (1) {
        FillAudioBuffer(buffer);
        snd_pcm_sframes_t frames = snd_pcm_writei(pcm_handle, buffer, BLOCK_SAMPLES);
        if (frames < 0) {
            snd_pcm_recover(pcm_handle, frames, 0); // Recover from buffer underruns
        }
    }
    return NULL;
}

// --- Shaders ---
const char* vertShaderSource = 
    "#version 130\n"
    "void main() { gl_Position = gl_Vertex; }\n"; 

const char* fragShaderSource = 
    "#version 330 core\n"
    "out vec4 FragColor;\n"
    "uniform float uTime; uniform float uCamZ; uniform vec2 uRes; uniform vec2 uMouse;\n"
    "uniform float uCamMode; uniform float uDose; uniform float uValence;\n"
    "uniform float uLogWarp; uniform float uF; uniform float uB;\n"
    "vec2 cMul(vec2 a, vec2 b) { return vec2(a.x*b.x - a.y*b.y, a.x*b.y + a.y*b.x); }\n"
    "vec2 cDiv(vec2 a, vec2 b) { float d = dot(b,b); return vec2(dot(a,b), a.y*b.x - a.x*b.y) / (d + 1e-6); }\n"
    "vec2 cConj(vec2 a) { return vec2(a.x, -a.y); }\n"
    "mat3 setCamera(in vec3 ro, in vec3 ta, float cr) {\n"
    "   vec3 cw = normalize(ta - ro); vec3 cp = vec3(sin(cr), cos(cr), 0.0);\n"
    "   vec3 cu = normalize(cross(cw, cp)); vec3 cv = normalize(cross(cu, cw)); return mat3(cu, cv, cw);\n"
    "}\n"
    "vec3 ACESFilm(vec3 x) { return clamp((x*(2.51*x+0.03))/(x*(2.43*x+0.59)+0.14), 0.0, 1.0); }\n"
    "mat2 rot(float a) { float s = sin(a), c = cos(a); return mat2(c, -s, s, c); }\n"
    "vec2 hexRep(vec2 p, vec2 size) { vec2 h = size * 0.5; vec2 a = mod(p, size) - h; vec2 b = mod(p - h, size) - h; return dot(a, a) < dot(b, b) ? a : b; }\n"
    "float de(vec3 p) {\n"
    "   vec3 p0 = p;\n"
    "   if (uLogWarp > 0.0) {\n"
    "       float r = length(p);\n"
    "       if (r > 0.001) {\n"
    "           float scale = mix(3.0, 0.5, uDose / 6.0);\n"
    "           float logrMod = mod(log(r) - uTime * 0.5, scale) - (scale * 0.5);\n"
    "           p = mix(p, (p / r) * exp(logrMod), uLogWarp);\n"
    "       }\n"
    "   }\n"
    "   p.xy = hexRep(p.xy, vec2(8.0, 8.0 * 1.73205081));\n"
    "   p.z = mod(p.z + 4.0, 8.0) - 4.0;\n"
    "   float dissonance = 1.0 - uValence;\n"
    "   if (dissonance > 0.0) { p.x += sin(p.y * 5.0 + uTime) * 0.15 * dissonance; p.y += cos(p.z * 4.0 - uTime) * 0.15 * dissonance; }\n"
    "   float lvl2 = smoothstep(1.0, 2.0, uDose); float lvl3 = smoothstep(2.0, 3.0, uDose);\n"
    "   float lvl4 = smoothstep(3.0, 4.0, uDose); float lvl5 = smoothstep(4.0, 5.0, uDose); float lvl6 = smoothstep(5.0, 6.0, uDose);\n"
    "   p.xy *= rot(p.z * 0.2 * lvl5 + uTime * 0.05 * lvl5);\n"
    "   vec3 offset = p;\n"
    "   float phaseSpeed = mix(0.01, 0.4, lvl6);\n"
    "   offset.xy *= rot(uTime * phaseSpeed * 3.0); offset.yz *= rot(uTime * phaseSpeed * 2.0); offset.zx *= rot(uTime * phaseSpeed);\n"
    "   float scale = mix(1.0, uF, lvl3); float dz = 1.0; float maxIters = mix(2.0, 11.0, (uDose - 1.0) / 5.0);\n"
    "   vec2 n1 = vec2(1.0, 0.0), n2 = vec2(0.5, 0.86602540378), n3 = vec2(-0.5, 0.86602540378);\n"
    "   for (int i = 0; i < 15; i++) {\n"
    "       if (float(i) > maxIters) break;\n"
    "       vec3 pHex = p; pHex.z = clamp(pHex.z, -1.0, 1.0) * 2.0 - pHex.z;\n"
    "       float d1 = dot(pHex.xy, n1); pHex.xy += (clamp(d1, -1.0, 1.0) - d1) * 2.0 * n1;\n"
    "       float d2 = dot(pHex.xy, n2); pHex.xy += (clamp(d2, -1.0, 1.0) - d2) * 2.0 * n2;\n"
    "       float d3 = dot(pHex.xy, n3); pHex.xy += (clamp(d3, -1.0, 1.0) - d3) * 2.0 * n3;\n"
    "       p = mix(p, pHex, lvl2);\n"
    "       float r2 = dot(p, p); float factor = 1.0;\n"
    "       if (r2 < 0.4) factor = mix(1.0, 4.2, lvl4); else if (r2 < 1.0) factor = mix(1.0, 1.0 / r2, lvl3);\n"
    "       p *= factor; dz *= factor; p = p * scale + offset; dz = dz * abs(scale) + 1.0;\n"
    "       if (lvl6 > 0.0 && i == 3) { float inv = mix(1.0, 1.5 / dot(p,p), lvl6 * 0.5); p *= inv; dz *= inv; }\n"
    "   }\n"
    "   float fracDist = length(p) / abs(dz) - mix(0.8, 0.0, lvl2);\n"
    "   float p0HexSafe = max(abs(p0.x), dot(abs(p0.xy), vec2(0.5, 0.86602540378)));\n"
    "   float safeZone = p0HexSafe - 0.5; float h = clamp(0.5 + 0.5 * (fracDist - (-safeZone)) / 0.5, 0.0, 1.0);\n"
    "   return mix(-safeZone, fracDist, h) + 0.5 * h * (1.0 - h);\n"
    "}\n"
    "vec3 calcNormal(vec3 p, float t) {\n"
    "   float eps = 0.001 * (1.0 + t * 0.5); vec2 e = vec2(1.0, -1.0) * eps;\n"
    "   vec3 n = normalize(e.xyy * de(p + e.xyy) + e.yyx * de(p + e.yyx) + e.yxy * de(p + e.yxy) + e.xxx * de(p + e.xxx));\n"
    "   return length(n) < 0.1 ? vec3(0.0, 1.0, 0.0) : n;\n"
    "}\n"
    "float calcAO(vec3 pos, vec3 nor) {\n"
    "   if (uDose < 2.5) return 1.0; float occ = 0.0; float sca = 1.0;\n"
    "   for(int i = 0; i < 5; i++) { float hr = 0.02 + 0.12 * float(i) / 4.0; float dd = de(pos + nor * hr); occ += -(dd - hr) * sca; sca *= 0.95; }\n"
    "   return clamp(1.0 - 2.5 * occ, 0.0, 1.0);\n"
    "}\n"
    "vec3 qriPalette(float t) {\n"
    "   vec3 aH = vec3(0.5), bH = vec3(0.5), cH = vec3(1.0), dH = vec3(0.0, 0.20, 0.45);\n"
    "   vec3 harmonic = aH + bH * cos(6.28318 * (cH * t + dH));\n"
    "   vec3 aD = vec3(0.6, 0.4, 0.4), bD = vec3(0.6, 0.6, 0.4), cD = vec3(2.0, 1.0, 1.0), dD = vec3(0.5, 0.0, 0.2);\n"
    "   vec3 dissonant = aD + bD * cos(6.28318 * (cD * t + dD));\n"
    "   return clamp(mix(dissonant, harmonic, uValence) * 1.15, 0.0, 1.0);\n"
    "}\n"
    "void main() {\n"
    "   vec2 uv = (gl_FragCoord.xy - 0.5 * uRes) / uRes.y;\n"
    "   float mobiusIntensity = smoothstep(3.5, 6.0, uDose);\n"
    "   if (mobiusIntensity > 0.0) {\n"
    "       vec2 a = vec2(sin(uTime * 0.41), cos(uTime * 0.27)) * 0.8 * mobiusIntensity;\n"
    "       vec2 mobiusUV = cMul(vec2(cos(uTime*0.2*mobiusIntensity), sin(uTime*0.2*mobiusIntensity)), cDiv(uv - a, vec2(1.0, 0.0) - cMul(cConj(a), uv)));\n"
    "       uv = mix(uv, mobiusUV, mobiusIntensity);\n"
    "   }\n"
    "   float vertigoIntensity = smoothstep(3.0, 6.0, uDose); float vertigoPhase = sin(uTime * uB * 0.05);\n"
    "   uv *= 1.0 + vertigoPhase * 0.6 * vertigoIntensity;\n"
    "   vec3 ro = vec3(0.0, 0.0, mod(uCamZ, 8.0));\n"
    "   vec3 ta = ro + vec3(0.0, 0.0, 1.0);\n"
    "   if (uCamMode > 0.5) { float yaw = -uMouse.x * 3.14; float pitch = uMouse.y * 1.5; ta = ro + vec3(sin(yaw)*cos(pitch), sin(pitch), cos(yaw)*cos(pitch)); }\n"
    "   else { float sway = mix(0.2, 1.2, smoothstep(4.0, 6.0, uDose)); ta.x += sin(uCamZ * 0.33) * sway; ta.y += cos(uCamZ * 0.2) * sway; }\n"
    "   mat3 cam = setCamera(ro, ta, sin(uCamZ*0.13)*0.3); vec3 rd = cam * normalize(vec3(uv, 1.0));\n"
    "   float t = 0.0; float glow = 0.0; float d;\n"
    "   for (int i = 0; i < 180; i++) { vec3 p = ro + rd * t; d = de(p); if (d < 0.001 || t > 18.0) break; t += d * 0.5; glow += 0.005 / (1.0 + d * 40.0); }\n"
    "   vec3 bgCol = vec3(0.002, 0.002, 0.005); vec3 col = bgCol;\n"
    "   if (t < 18.0) {\n"
    "       vec3 p = ro + rd * t; vec3 n = calcNormal(p, t); float ao = calcAO(p, n);\n"
    "       vec3 l = normalize(ro + vec3(sin(uTime)*3.0, 2.0, cos(uTime)*3.0 + 1.0) - p); vec3 ref = reflect(rd, n);\n"
    "       float dif = max(dot(n, l), 0.0); float spe = pow(max(dot(ref, l), 0.0), mix(8.0, 128.0, smoothstep(2.0, 4.0, uDose)));\n"
    "       float hexDistXY = max(abs(p.x), dot(abs(p.xy), vec2(0.5, 0.86602540378)));\n"
    "       float spatialDensity = mix(length(p)*0.5 + hexDistXY*0.5, max(hexDistXY, abs(p.z)), smoothstep(1.0, 4.0, uDose)) * 1.5 + p.z * 0.08 - uTime * 0.15;\n"
    "       vec3 albedo = qriPalette((spatialDensity - 0.05 * sin(spatialDensity * 30.0)) + (dot(n, -rd) * 0.2));\n"
    "       col = albedo * dif * ao * 0.8 + albedo * spe * mix(0.5, 3.0, smoothstep(2.0, 4.0, uDose)) * ao + qriPalette((spatialDensity - 0.05 * sin(spatialDensity * 30.0)) + (dot(n, -rd) * 0.2) + 0.2) * pow(1.0 - max(dot(n, -rd), 0.0), 5.0) * 1.5 * ao;\n"
    "       col = mix(col, bgCol, smoothstep(12.0, 18.0, t));\n"
    "   }\n"
    "   col += glow * qriPalette(t * 0.1 - uTime * 0.1) * 0.15;\n"
    "   col *= 1.0 + 0.1 * sin(uTime * 28.87 * 6.2831);\n"
    "   FragColor = vec4(pow(ACESFilm(col * 1.2), vec3(0.85)), 1.0);\n"
    "}\n";

// --- System Functions ---
double GetTime() {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return tv.tv_sec + tv.tv_usec * 1e-6;
}

void PrintText(float x, float y, const char* str) {
    glRasterPos2f(x, y);
    for(int i=0; str[i]; i++) {
        glutBitmapCharacter(GLUT_BITMAP_9_BY_15, str[i]); // Native FreeGLUT Font
    }
}

// --- GLUT Callbacks ---
void KeyboardDown(unsigned char key, int x, int y) {
    if (key == 27) exit(0); // ESC
    if (key == 9) showHud = !showHud; // TAB
    if (key == 'l' || key == 'L') currentLog = (currentLog == 0.0f) ? 1.0f : 0.0f;
    if (key == 'c' || key == 'C') camMode = (camMode == 0.0f) ? 1.0f : 0.0f;
    if (key == 'f' || key == 'F') isCameraMoving = !isCameraMoving;
    if (key == 'a' || key == 'A') audioEnabled = !audioEnabled;
}

void SpecialDown(int key, int x, int y) { special_keys[key] = 1; }
void SpecialUp(int key, int x, int y) { special_keys[key] = 0; }
void PassiveMotion(int x, int y) { rawMouseX = x; rawMouseY = y; }

void Display() {
    double currTime = GetTime();
    float dt = (float)(currTime - lastTime);
    lastTime = currTime;

    // Sliders
    if (special_keys[GLUT_KEY_UP]) currentDose = CLAMP(currentDose + 0.01f, 1.0f, 6.0f);
    if (special_keys[GLUT_KEY_DOWN]) currentDose = CLAMP(currentDose - 0.01f, 1.0f, 6.0f);
    if (special_keys[GLUT_KEY_RIGHT]) currentValence = CLAMP(currentValence + 0.01f, 0.0f, 1.0f);
    if (special_keys[GLUT_KEY_LEFT]) currentValence = CLAMP(currentValence - 0.01f, 0.0f, 1.0f);

    // FPS Calc
    frameCount++;
    fpsTimer += dt;
    if (fpsTimer >= 1.0f) {
        currentFPS = frameCount;
        frameCount = 0;
        fpsTimer -= 1.0f;
    }

    accumulatedTime += dt * currentSpeed;
    if (isCameraMoving) currentCamZ += dt * 0.3f * currentSpeed;

    int w = glutGet(GLUT_WINDOW_WIDTH);
    int h = glutGet(GLUT_WINDOW_HEIGHT);
    float targetMouseX = ((float)rawMouseX / w) * 2.0f - 1.0f;
    float targetMouseY = -((float)rawMouseY / h) * 2.0f + 1.0f;
    currentMouseX += (targetMouseX - currentMouseX) * 10.0f * dt;
    currentMouseY += (targetMouseY - currentMouseY) * 10.0f * dt;

    glUniform1f(locTime, accumulatedTime);
    glUniform1f(locCamZ, currentCamZ);
    glUniform2f(locRes, (float)w, (float)h);
    glUniform2f(locMouse, currentMouseX, currentMouseY);
    glUniform1f(locCamMode, camMode);
    glUniform1f(locDose, currentDose);
    glUniform1f(locValence, currentValence);
    glUniform1f(locLogWarp, currentLog);
    glUniform1f(locF, currentF);
    glUniform1f(locB, currentB);

    glRectf(-1.0f, -1.0f, 1.0f, 1.0f); 

    if (showHud) {
        glUseProgram(0); 
        glColor3f(0.0f, 1.0f, 1.0f); 
        char buf[128];
        sprintf(buf, "FPS:      %d", currentFPS); PrintText(-0.95f, 0.95f, buf);
        PrintText(-0.95f, 0.90f, "=== PIE QRI TOPOLOGY HUD ===");
        sprintf(buf, "[UP/DWN]  DOSE: %.2f", currentDose); PrintText(-0.95f, 0.85f, buf);
        sprintf(buf, "[LFT/RGT] VALENCE: %.2f", currentValence); PrintText(-0.95f, 0.80f, buf);
        sprintf(buf, "[L]       LOG WARP: %s", currentLog > 0.0f ? "ON" : "OFF"); PrintText(-0.95f, 0.75f, buf);
        sprintf(buf, "[C]       CAM MODE: %s", camMode > 0.0f ? "MANUAL" : "AUTO"); PrintText(-0.95f, 0.70f, buf);
        sprintf(buf, "[F]       CAMERA: %s", isCameraMoving ? "FLYING" : "FROZEN"); PrintText(-0.95f, 0.65f, buf);
        sprintf(buf, "[A]       AUDIO: %s", audioEnabled ? "ON" : "MUTED"); PrintText(-0.95f, 0.60f, buf);
        PrintText(-0.95f, 0.50f, "[TAB] TOGGLE MENU");
        PrintText(-0.95f, 0.45f, "[ESC] QUIT");
        glUseProgram(shaderProgram); 
    }

    glutSwapBuffers();
    glutPostRedisplay(); // Loop as fast as possible
}

int main(int argc, char** argv) {
    srand(time(NULL));
    
    // Init FreeGLUT Window
    glutInit(&argc, argv);
    glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGBA | GLUT_DEPTH);
    glutInitWindowSize(1920, 1080);
    glutCreateWindow("PIE: QRI 6-Level DMT Topology");
    glutFullScreen();
    glutSetCursor(GLUT_CURSOR_NONE);

    // Compile Shaders
    GLuint vs = glCreateShader(GL_VERTEX_SHADER);
    glShaderSource(vs, 1, &vertShaderSource, NULL);
    glCompileShader(vs);

    GLuint fs = glCreateShader(GL_FRAGMENT_SHADER);
    glShaderSource(fs, 1, &fragShaderSource, NULL);
    glCompileShader(fs);

    shaderProgram = glCreateProgram();
    glAttachShader(shaderProgram, vs); 
    glAttachShader(shaderProgram, fs);
    glLinkProgram(shaderProgram); 
    glUseProgram(shaderProgram);

    // Map Uniforms
    locTime = glGetUniformLocation(shaderProgram, "uTime");
    locCamZ = glGetUniformLocation(shaderProgram, "uCamZ");
    locRes  = glGetUniformLocation(shaderProgram, "uRes");
    locMouse = glGetUniformLocation(shaderProgram, "uMouse");
    locCamMode = glGetUniformLocation(shaderProgram, "uCamMode");
    locDose = glGetUniformLocation(shaderProgram, "uDose");
    locValence = glGetUniformLocation(shaderProgram, "uValence");
    locLogWarp = glGetUniformLocation(shaderProgram, "uLogWarp");
    locF = glGetUniformLocation(shaderProgram, "uF");
    locB = glGetUniformLocation(shaderProgram, "uB");

    // Init ALSA Audio Thread
    pthread_t audio_id;
    pthread_create(&audio_id, NULL, AudioThread, NULL);

    // Hook Callbacks and Start
    glutKeyboardFunc(KeyboardDown);
    glutSpecialFunc(SpecialDown);
    glutSpecialUpFunc(SpecialUp);
    glutPassiveMotionFunc(PassiveMotion);
    glutDisplayFunc(Display);
    
    lastTime = GetTime();
    glutMainLoop();
    
    return 0;
}
