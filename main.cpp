// ============================================================
//  ~celeste~ for M5Core2 + Adafruit Seesaw Gamepad
//  Translated from PICO-8 Lua by Matt Thorson & Noel Berry
//
//  New additions:
//    - Main screen with mountain + character select
//    - Pixel-art sprites for Madeline and Badeline
//    - Character-aware hair colour
//    - BLE multiplayer scaffolding (race mode)
//    - Opponent ghost rendering (same-room only)
//
//  Dependencies:
//    - M5Unified library
//    - Adafruit_seesaw library
//    - BLEDevice / BLEServer / BLEClient (ESP32 Arduino BLE)
//
//  Wiring: Seesaw gamepad on I2C (SDA=32, SCL=33 on Core2)
// ============================================================

#include <M5Unified.h>
#include <Adafruit_seesaw.h>
#include <math.h>
#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLEClient.h>
#include <BLEUtils.h>
#include <BLEScan.h>
#include <BLEAdvertisedDevice.h>
#include <BLE2902.h>

// #define BLE_ROLE_HOST  // comment out to make this device a BLE client instead of server

// -------------------------------------------------------
// Seesaw gamepad button masks
// -------------------------------------------------------
#define BUTTON_X         (1UL << 6)
#define BUTTON_Y         (1UL << 2)
#define BUTTON_A         (1UL << 5)
#define BUTTON_B         (1UL << 1)
#define BUTTON_SELECT    (1UL << 0)
#define BUTTON_START     (1UL << 16)

// Map PICO-8 button indices
#define K_LEFT   0
#define K_RIGHT  1
#define K_UP     2
#define K_DOWN   3
#define K_JUMP   4   // A button
#define K_DASH   5   // B button

// Raw button pressed-this-frame helpers (used in menus)
#define btn_just(k) (((btn_held >> (k)) & 1) && !((btn_prev >> (k)) & 1))
// Raw physical button just-pressed (not remapped)
static bool raw_just(uint32_t mask, uint32_t raw_cur, uint32_t raw_prev) {
  return (raw_cur & mask) && !(raw_prev & mask);
}

// -------------------------------------------------------
// Display constants
// -------------------------------------------------------
#define PICO_W   128
#define PICO_H   128
#define SCALE      2
#define OFFSET_X ((320 - PICO_W * SCALE) / 2)   //  32
#define OFFSET_Y ((240 - PICO_H * SCALE) / 2)   //  -8

// -------------------------------------------------------
// PICO-8 16-colour palette (RGB565)
// -------------------------------------------------------
static const uint16_t PICO_PAL[16] = {
  0x0000, // 0  black
  0x194A, // 1  dark blue
  0x792A, // 2  dark purple
  0x0480, // 3  dark green
  0xA945, // 4  brown
  0x5268, // 5  dark grey
  0xC5B8, // 6  light grey
  0xFFFF, // 7  white
  0xF809, // 8  red
  0xFF41, // 9  orange
  0xFF01, // 10 yellow
  0x07C0, // 11 green
  0x2B5F, // 12 blue
  0x83B3, // 13 indigo
  0xFBB5, // 14 pink
  0xFEF6, // 15 peach
};

// Helper: pack RGB888 → RGB565
static constexpr uint16_t rgb(uint8_t r, uint8_t g, uint8_t b) {
  return ((r >> 3) << 11) | ((g >> 2) << 5) | (b >> 3);
}

// -------------------------------------------------------
// Character selection
// -------------------------------------------------------
enum CharSelect { CHAR_MADELINE = 0, CHAR_BADELINE = 1 };
static CharSelect selectedChar = CHAR_MADELINE;

// -------------------------------------------------------
// End screen state
// -------------------------------------------------------
enum EndResult { END_WIN, END_LOSE, END_SOLO };
static EndResult endResult = END_SOLO;
static int end_frames = 0;  // own frame counter for end screen animation

// -------------------------------------------------------
// Game-mode state machine
// -------------------------------------------------------
enum GameMode {
  MODE_MAIN_SCREEN,   // mountain + character select
  MODE_BLE_CONNECT,   // waiting for BLE peer
  MODE_SOLO,          // single-player game
  MODE_RACE,          // two-player BLE race
  MODE_END            // end screen (win / lose / solo complete)
};
static GameMode gameMode = MODE_MAIN_SCREEN;

// -------------------------------------------------------
// BLE configuration
// -------------------------------------------------------
#define BLE_SERVICE_UUID    "4fafc201-1fb5-459e-8fcc-c5c9c331914b"
#define BLE_CHAR_UUID       "beb5483e-36e1-4688-b7f5-ea07361b26a8"
#define BLE_DEVICE_NAME     "CelesteM5"

// Peer state packet (sent each frame over BLE)
struct PeerPacket {
  int16_t x;
  int16_t y;
  uint8_t room_x;
  uint8_t room_y;
  uint8_t djump;
  uint8_t flip_x;
  uint8_t char_id;   // 0=Madeline, 1=Badeline
  uint8_t finished;  // 1 = peer completed all rooms
};

static bool        ble_connected   = false;
static bool        ble_scanning    = false;
static bool        ble_is_host     = false;  // true = advertising, false = scanning
static PeerPacket  peer_state      = {};
static bool        peer_valid      = false;
static bool peer_finished_first = false;
static bool local_finished = false;

static BLEServer        *ble_server    = nullptr;
static BLECharacteristic*ble_char      = nullptr;
static BLEClient        *ble_client    = nullptr;
static BLERemoteCharacteristic *ble_remote_char = nullptr;

// -------------------------------------------------------
// Pixel-art sprite data  (8×8, index into per-char palette)
// -------------------------------------------------------
// Colour indices:
//  0 = transparent
//  1 = dark outline
//  2 = skin
//  3 = skin shadow
//  5 = dark (eyes/pupil)
//  6 = shirt main
//  7 = shirt shadow
//  8 = boots/pants
//  9 = hair (overridden by draw_hair; shown here for layout)
static const uint8_t PLAYER_SPR[8][8] = {
  {1, 9, 9, 9, 9, 9, 1, 0},
  {9, 9, 2, 2, 2, 2, 9, 1},
  {1, 2, 5, 2, 2, 5, 2, 1},
  {0, 1, 2, 2, 2, 2, 1, 0},
  {0, 1, 6, 6, 6, 6, 1, 0},
  {0, 6, 6, 7, 7, 6, 6, 0},
  {0, 8, 6, 8, 8, 6, 8, 0},
  {0, 8, 8, 0, 0, 8, 8, 0},
};

// RGB565 colour tables — one per character, indexed by sprite index above
static const uint16_t MADELINE_PAL[10] = {
  0x0000,            // 0  transparent (unused — skip draw)
  rgb(26,26,46),     // 1  outline
  rgb(245,197,163),  // 2  skin
  rgb(212,149,106),  // 3  skin shadow
  0x0000,            // 4  (unused)
  rgb(26,26,46),     // 5  eyes
  rgb(58,181,164),   // 6  teal shirt
  rgb(42,138,124),   // 7  shirt shadow
  rgb(44,44,84),     // 8  boots
  rgb(255,68,68),    // 9  hair (normal)
};
static const uint16_t BADELINE_PAL[10] = {
  0x0000,
  rgb(26,26,46),
  rgb(200,168,216),  // 2  purple-tinted skin
  rgb(160,112,144),  // 3  skin shadow
  0x0000,
  rgb(26,26,46),     // 5  eyes
  rgb(74,35,90),     // 6  dark purple shirt
  rgb(45,18,53),     // 7  shirt shadow
  rgb(26,10,46),     // 8  boots
  rgb(155,89,182)   // 9  hair (normal)
};

// Hair colours
static const uint16_t MADELINE_HAIR_NORMAL = rgb(255,68,68);
static const uint16_t MADELINE_HAIR_DASH   = rgb(91,141,217);
static const uint16_t BADELINE_HAIR_NORMAL = rgb(155,89,182);
static const uint16_t BADELINE_HAIR_DASH   = rgb(204, 128, 186);

// Each sprite is 8×8, colour index 0=transparent

#define TILE_SPR_SIZE 8

// Tile: solid  (id=1)
static const uint8_t SPR_SOLID[8][8] = {
  {7,7,7,7,7,7,7,7},
  {7,7,12,7,12,12,7,7},
  {7,12,12,12,12,12,12,7},
  {12,12,12,7,12,12,7,12},
  {12,7,12,12,12,12,12,12},
  {12,12,12,12,7,12,12,12},
  {12,12,12,12,12,12,12,12},
  {12,12,12,12,12,12,12,12},
};

// Tile: spike_d  (id=17) — attaches to floor, tip points UP
static const uint8_t SPR_SPIKE_D[8][8] = {
  {0,0,0,5,5,0,0,0},
  {0,0,0,5,5,0,0,0},
  {0,0,5,6,6,5,0,0},
  {0,0,5,6,6,5,0,0},
  {0,5,6,6,6,6,5,0},
  {0,5,6,6,6,6,5,0},
  {5,6,6,6,6,6,6,5},
  {5,6,6,6,6,6,6,5},
};

// Tile: spike_u  (id=27) — attaches to ceiling, tip points DOWN
static const uint8_t SPR_SPIKE_U[8][8] = {
  {5,6,6,6,6,6,6,5},
  {5,6,6,6,6,6,6,5},
  {0,5,6,6,6,6,5,0},
  {0,5,6,6,6,6,5,0},
  {0,0,5,6,6,5,0,0},
  {0,0,5,6,6,5,0,0},
  {0,0,0,5,5,0,0,0},
  {0,0,0,5,5,0,0,0},
};

// Tile: spike_l  (id=43) — attaches to left wall, tip points RIGHT
static const uint8_t SPR_SPIKE_L[8][8] = {
  {5,5,0,0,0,0,0,0},
  {6,6,5,5,0,0,0,0},
  {6,6,6,6,5,5,0,0},
  {6,6,6,6,6,6,5,5},
  {6,6,6,6,6,6,5,5},
  {6,6,6,6,5,5,0,0},
  {6,6,5,5,0,0,0,0},
  {5,5,0,0,0,0,0,0},
};

// Tile: spike_r  (id=59) — attaches to right wall, tip points LEFT
static const uint8_t SPR_SPIKE_R[8][8] = {
  {0,0,0,0,0,0,5,5},
  {0,0,0,0,5,5,6,6},
  {0,0,5,5,6,6,6,6},
  {5,5,6,6,6,6,6,6},
  {5,5,6,6,6,6,6,6},
  {0,0,5,5,6,6,6,6},
  {0,0,0,0,5,5,6,6},
  {0,0,0,0,0,0,5,5},
};

// Tile: platform  (id=11)
static const uint8_t SPR_PLATFORM[8][8] = {
  {7,7,7,7,7,7,7,7},
  {12,12,12,12,12,12,12,12},
  {0,0,0,0,0,0,0,0},
  {0,0,0,0,0,0,0,0},
  {0,0,0,0,0,0,0,0},
  {0,0,0,0,0,0,0,0},
  {0,0,0,0,0,0,0,0},
  {0,0,0,0,0,0,0,0},
};

// Tile: spring  (id=18)
static const uint8_t SPR_SPRING[8][8] = {
  {0,0,0,0,0,0,0,0},
  {0,0,0,0,0,0,0,0},
  {0,0,0,0,0,0,0,0},
  {0,0,0,0,0,0,0,0},
  {0,0,0,0,0,0,0,0},
  {0,0,0,0,0,0,0,0},
  {0,5,5,5,5,5,5,0},
  {0,5,5,5,5,5,5,0},
};

static uint8_t tile_flags[256] = {};


// Tile flags  (bit 0=solid, bit 1=ice, bit 2=hazard, ...)
static void init_tile_flags_custom() {
  tile_flags[1] = 0x01;  // solid
  tile_flags[17] = 0x04;  // spike_d
  tile_flags[27] = 0x04;  // spike_u
  tile_flags[43] = 0x04;  // spike_l
  tile_flags[59] = 0x04;  // spike_r
}



// -------------------------------------------------------
// Globals
// -------------------------------------------------------
Adafruit_seesaw gamepad;
#define tft M5.Display
static M5Canvas canvas(&M5.Display);
#undef tft
#define tft canvas

static uint32_t btn_held  = 0;
static uint32_t btn_prev  = 0;
static uint32_t raw_held  = 0;   // physical button bits (for menu use)
static uint32_t raw_prev  = 0;

// PICO-8 globals
static int   frames        = 0;
static int   deaths        = 0;
static int   seconds       = 0;
static int   minutes       = 0;
static int   freeze        = 0;
static int   shake         = 0;
static bool  will_restart  = false;
static int   delay_restart = 0;
static bool  has_dashed    = false;
static int   sfx_timer     = 0;
static bool  has_key       = false;
static bool  pause_player  = false;
static bool  flash_bg      = false;
static int   music_timer   = 0;
static int   max_djump     = 1;
static bool  start_game    = false;
static int   start_game_flash = 0;
static bool  new_bg        = false;
static bool  got_fruit[30] = {};
static int   level_index();

struct Vec2f { float x, y; };
struct Vec2i { int   x, y; };
struct Room  { int   x, y; } room = {0, 0};

// -------------------------------------------------------
// Math helpers
// -------------------------------------------------------
static float pico_rnd(float n)   { return (rand() / (float)RAND_MAX) * n; }
static float pico_sin(float t)   { return sinf(t * 2.0f * M_PI); }
static float pico_cos(float t)   { return cosf(t * 2.0f * M_PI); }
static int   pico_flr(float v)   { return (int)floorf(v); }
static float pico_abs(float v)   { return fabsf(v); }
static int   pico_sign(float v)  { return v > 0 ? 1 : (v < 0 ? -1 : 0); }
static float pico_max(float a, float b) { return a > b ? a : b; }
static float pico_min(float a, float b) { return a < b ? a : b; }
static float pico_clamp(float v, float lo, float hi) {
  return pico_max(lo, pico_min(hi, v));
}
static float pico_appr(float val, float target, float amount) {
  return val > target ? pico_max(val - amount, target)
                      : pico_min(val + amount, target);
}
static bool pico_maybe() { return pico_rnd(1.0f) < 0.5f; }

// -------------------------------------------------------
// Tile / room helpers
// -------------------------------------------------------
static int level_index() { return room.x % 8 + room.y * 8; }
static bool is_title()   { return level_index() == 31; }

// -------------------------------------------------------
// Input helpers
// -------------------------------------------------------
static bool btn(int k)  { return (btn_held >> k) & 1; }

// -------------------------------------------------------
// Tilemap
// -------------------------------------------------------
#define MAP_W  16
#define MAP_H  16

#define TILE_EMPTY   0
#define TILE_SOLID   1
#define TILE_SPIKE_D 17
#define TILE_SPIKE_U 27
#define TILE_SPIKE_L 43
#define TILE_SPIKE_R 59


static const uint8_t ROOM_DATA[3][MAP_H][MAP_W] = {
  // Room 0
  {
   { 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,27,27,27,27,27, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0,17,17, 1},
   { 1, 0, 0, 0, 1, 1,17,17,17, 1, 1,17,17, 1, 1, 1},
   { 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}
  },
  // Room 1
  {
   { 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1},
   { 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1},
   { 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1},
   { 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1},
   { 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1},
   { 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1,27,27,27, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0,27,27,27,27,27,27,27, 0, 0, 0, 1, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1},
   { 1, 0, 0, 0, 0, 0, 0,17,17, 0, 0, 0, 0, 0, 1, 1},
   { 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1},
   { 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1},
   { 1, 0, 0, 0,17,17,17, 1, 1, 1,17,17, 1, 1, 1, 1},
   { 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}
  },
  // Room 2
  {
   { 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,43, 0, 0, 1, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,43, 0, 0,59, 1},
   { 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1,43, 0, 0,59, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,59, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1},
   { 1,17,17,17,17,17, 1, 1,17,17, 1, 1, 0, 0, 0, 1},
   { 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1},
   { 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1},
   { 1, 0, 0, 0,17,17,17,17,17,17,17,17,17,17,17, 1},
   { 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1}
  }
};



// static void init_tile_flags() {
//   tile_flags[TILE_SOLID]   = (1 << 0);
//   tile_flags[TILE_SPIKE_D] = 0;
//   tile_flags[TILE_SPIKE_U] = 0;
//   tile_flags[TILE_SPIKE_L] = 0;
//   tile_flags[TILE_SPIKE_R] = 0;
// }



static uint8_t mget(int tx, int ty) {
  if (tx < 0 || ty < 0 || tx >= MAP_W || ty >= MAP_H) return TILE_EMPTY;
  int idx = level_index();
  if (idx < 0 || idx >= 3) return TILE_EMPTY;
  return ROOM_DATA[idx][ty][tx];
}

static bool fget(uint8_t tile, uint8_t flag) {
  return (tile_flags[tile] >> flag) & 1;
}

// -------------------------------------------------------
// Drawing primitives
// -------------------------------------------------------
static void rectfill(int x0, int y0, int x1, int y1, int col) {
  tft.fillRect(OFFSET_X + x0 * SCALE,
               OFFSET_Y + y0 * SCALE,
               (x1 - x0 + 1) * SCALE,
               (y1 - y0 + 1) * SCALE,
               PICO_PAL[col & 15]);
}
static void circfill(float cx, float cy, float r, int col) {
  tft.fillCircle(OFFSET_X + (int)cx * SCALE,
                 OFFSET_Y + (int)cy * SCALE,
                 (int)(r * SCALE),
                 PICO_PAL[col & 15]);
}
static void circfill_rgb(float cx, float cy, float r, uint16_t color565) {
  tft.fillCircle(OFFSET_X + (int)cx * SCALE,
                 OFFSET_Y + (int)cy * SCALE,
                 (int)(r * SCALE),
                 color565);
}
static void pico_print(const char *s, int x, int y, int col) {
  tft.setTextColor(PICO_PAL[col & 15]);
  tft.drawString(s, OFFSET_X + x * SCALE, OFFSET_Y + y * SCALE);
}
static void pico_line(int x0, int y0, int x1, int y1, int col) {
  tft.drawLine(OFFSET_X + x0 * SCALE, OFFSET_Y + y0 * SCALE,
               OFFSET_X + x1 * SCALE, OFFSET_Y + y1 * SCALE,
               PICO_PAL[col & 15]);
}

// -------------------------------------------------------
// Pixel-art sprite renderer
// -------------------------------------------------------
// Draws the 8×8 player sprite using per-character palette.
// flip_x mirrors horizontally. ghost=true renders at ~50% brightness.
static void draw_player_sprite(float px, float py, bool flip_x,
                               CharSelect ch, bool ghost = false) {
  const uint16_t *pal = (ch == CHAR_MADELINE) ? MADELINE_PAL : BADELINE_PAL;
  int sx = OFFSET_X + (int)px * SCALE;
  int sy = OFFSET_Y + (int)py * SCALE;
  for (int row = 0; row < 8; row++) {
    for (int col = 0; col < 8; col++) {
      int c = flip_x ? PLAYER_SPR[row][7 - col] : PLAYER_SPR[row][col];
      if (c == 0 || c == 9) continue;  // transparent or hair (drawn separately)
      uint16_t color = pal[c];
      if (ghost) {
        // Dim each channel by ~50% for ghost effect
        uint8_t r = ((color >> 11) & 0x1F) >> 1;
        uint8_t g = ((color >>  5) & 0x3F) >> 1;
        uint8_t b = ( color        & 0x1F) >> 1;
        color = (r << 11) | (g << 5) | b;
      }
      tft.fillRect(sx + col * SCALE, sy + row * SCALE, SCALE, SCALE, color);
    }
  }
}

// -------------------------------------------------------
// Box-based non-player sprite renderer (unchanged)
// -------------------------------------------------------
static int spr_color(int id) {
  if (id ==  1 || id ==  2 || id ==  3 ||
      id ==  4 || id ==  5 || id ==  6 || id == 7)  return 12;
  if (id == 11 || id == 12)                          return  5;
  if (id == 18 || id == 19)                          return  9;
  if (id == 22)                                      return 12;
  if (id == 23 || id == 24 || id == 25)              return  4;
  if (id == 26)                                      return 10;
  if (id == 28)                                      return 10;
  if (id == 29 || id == 30 || id == 31)              return  6;
  if (id ==  8 || id ==  9 || id == 10)              return  9;
  if (id == 20)                                      return  9;
  if (id == 64 || id == 65 ||
      id == 80 || id == 81)                          return  5;
  if (id == 96 || id == 97 ||
      id == 112 || id == 113)                        return  7;
  if (id == 102)                                     return  7;
  if (id == 118 || id == 119 || id == 120)           return 11;
  return 7;
}

static void spr(int id, float x, float y,
                bool flip_x = false, bool flip_y = false) {
  (void)flip_x; (void)flip_y;
  int col = spr_color(id);
  tft.fillRect(OFFSET_X + (int)x * SCALE,
               OFFSET_Y + (int)y * SCALE,
               8 * SCALE, 8 * SCALE,
               PICO_PAL[col & 15]);
  tft.drawRect(OFFSET_X + (int)x * SCALE,
               OFFSET_Y + (int)y * SCALE,
               8 * SCALE, 8 * SCALE,
               PICO_PAL[0]);
}

static void draw_tile_sprite(int tx, int ty, uint8_t tile_id) {
  const uint8_t *spr = nullptr;
  switch(tile_id) {
    case  1: spr = &SPR_SOLID[0][0];    break;
    case 17: spr = &SPR_SPIKE_D[0][0];  break;
    case 27: spr = &SPR_SPIKE_U[0][0];  break;
    case 43: spr = &SPR_SPIKE_L[0][0];  break;
    case 59: spr = &SPR_SPIKE_R[0][0];  break;
    case 11: spr = &SPR_PLATFORM[0][0]; break;
    case 18: spr = &SPR_SPRING[0][0];   break;
    default: return;
  }
  for (int r = 0; r < TILE_SPR_SIZE; r++) {
    for (int c = 0; c < TILE_SPR_SIZE; c++) {
      uint8_t ci = spr[r * TILE_SPR_SIZE + c];
      if (ci == 0) continue;
      tft.fillRect(OFFSET_X + (tx * 8 + c) * SCALE,
                   OFFSET_Y + (ty * 8 + r) * SCALE,
                   SCALE, SCALE, PICO_PAL[ci & 15]);
    }
  }
}

static void map_draw_sprites() {
  for (int ty = 0; ty < MAP_H; ty++)
    for (int tx = 0; tx < MAP_W; tx++) {
      uint8_t t = mget(tx, ty);
      if (t != TILE_EMPTY) draw_tile_sprite(tx, ty, t);
    }
}

// -------------------------------------------------------
// Audio stubs
// -------------------------------------------------------
static void psfx(int) {}
static void pico_sfx(int) {}
static void pico_music(int, int = 0, int = 7) {}

// -------------------------------------------------------
// Object / entity system
// -------------------------------------------------------
struct HitBox { float x, y, w, h; };
struct Object;

struct ObjectType {
  int   tile         = 0;
  bool  if_not_fruit = false;
  void (*init_fn)  (Object *) = nullptr;
  void (*update_fn)(Object *) = nullptr;
  void (*draw_fn)  (Object *) = nullptr;
};

static ObjectType T_player;
static ObjectType T_player_spawn;
static ObjectType T_spring;
static ObjectType T_balloon;
static ObjectType T_fall_floor;
static ObjectType T_smoke;
static ObjectType T_fruit;
static ObjectType T_fly_fruit;
static ObjectType T_lifeup;
static ObjectType T_fake_wall;
static ObjectType T_key;
static ObjectType T_platform;
static ObjectType T_message;
static ObjectType T_orb;
static ObjectType T_flag;
static ObjectType T_room_title;

#define MAX_OBJECTS 64

struct Object {
  ObjectType *type    = nullptr;
  bool  alive         = false;
  bool  collideable   = true;
  bool  solids        = true;
  int   spr_id        = 0;
  bool  flip_x        = false;
  bool  flip_y        = false;
  float x             = 0, y = 0;
  HitBox hitbox       = {0, 0, 8, 8};
  Vec2f spd           = {0, 0};
  Vec2f rem           = {0, 0};
  bool  p_jump        = false;
  bool  p_dash        = false;
  int   grace         = 0;
  int   jbuffer       = 0;
  int   djump         = 1;
  int   dash_time     = 0;
  int   dash_effect_time = 0;
  Vec2f dash_target   = {0, 0};
  Vec2f dash_accel    = {0, 0};
  float spr_off       = 0;
  bool  was_on_ground = false;
  Vec2f target        = {0, 0};
  int   state         = 0;
  int   delay         = 0;
  int   hide_in       = 0;
  int   hide_for      = 0;
  int   timer         = 0;
  float offset        = 0;
  float start         = 0;
  float last          = 0;
  int   dir           = 0;
  int   duration      = 0;
  float flash         = 0;
  struct HairNode { float x, y; int size; } hair[5];
  bool  hair_init     = false;
  int   score         = 0;
  bool  show          = false;
  int   sfx_delay     = 0;
  bool  fly           = false;
  float step          = 0;
  struct BCP { float x, y, h, spd; } bcp[60];
  int   bcp_count     = 0;
};

static Object objects[MAX_OBJECTS];

static Object *init_object(ObjectType *type, float x, float y);
static void    destroy_object(Object *obj);
static bool    obj_is_solid(Object *obj, float ox, float oy);
static bool    obj_is_ice(Object *obj, float ox, float oy);

static Object *obj_collide(Object *obj, ObjectType *type, float ox, float oy) {
  for (int i = 0; i < MAX_OBJECTS; i++) {
    Object *other = &objects[i];
    if (!other->alive || other->type != type || other == obj || !other->collideable) continue;
    if (other->x + other->hitbox.x + other->hitbox.w > obj->x + obj->hitbox.x + ox &&
        other->y + other->hitbox.y + other->hitbox.h > obj->y + obj->hitbox.y + oy &&
        other->x + other->hitbox.x < obj->x + obj->hitbox.x + obj->hitbox.w + ox &&
        other->y + other->hitbox.y < obj->y + obj->hitbox.y + obj->hitbox.h + oy)
      return other;
  }
  return nullptr;
}
static bool obj_check(Object *obj, ObjectType *type, float ox, float oy) {
  return obj_collide(obj, type, ox, oy) != nullptr;
}

static bool tile_flag_at(float x, float y, float w, float h, int flag) {
  for (int i = pico_flr(pico_max(0, x / 8)); i <= (int)pico_min(15, (x+w-1)/8); i++)
    for (int j = pico_flr(pico_max(0, y / 8)); j <= (int)pico_min(15, (y+h-1)/8); j++)
      if (fget(mget(i, j), flag)) return true;
  return false;
}
static bool solid_at(float x, float y, float w, float h) { return tile_flag_at(x,y,w,h,0); }
static bool ice_at  (float x, float y, float w, float h) { return tile_flag_at(x,y,w,h,4); }

static bool obj_is_solid(Object *obj, float ox, float oy) {
  if (oy > 0 && !obj_check(obj, &T_platform, ox, 0) && obj_check(obj, &T_platform, ox, oy)) return true;
  return solid_at(obj->x+obj->hitbox.x+ox, obj->y+obj->hitbox.y+oy, obj->hitbox.w, obj->hitbox.h)
      || obj_check(obj, &T_fall_floor, ox, oy)
      || obj_check(obj, &T_fake_wall,  ox, oy);
}
static bool obj_is_ice(Object *obj, float ox, float oy) {
  return ice_at(obj->x+obj->hitbox.x+ox, obj->y+obj->hitbox.y+oy, obj->hitbox.w, obj->hitbox.h);
}

static bool spikes_at(float x, float y, float w, float h, float xspd, float yspd) {
  for (int i = pico_flr(pico_max(0,x/8)); i <= (int)pico_min(15,(x+w-1)/8); i++) {
    for (int j = pico_flr(pico_max(0,y/8)); j <= (int)pico_min(15,(y+h-1)/8); j++) {
      uint8_t t = mget(i,j);
      if (t==17 && ((int)(y+h-1)%8>=6 || y+h==j*8+8) && yspd>=0) return true;
      if (t==27 && (int)y%8<=2 && yspd<=0)                         return true;
      if (t==43 && (int)x%8<=2 && xspd<=0)                         return true;
      if (t==59 && ((int)(x+w-1)%8>=6 || x+w==i*8+8) && xspd>=0)  return true;
    }
  }
  return false;
}

static void obj_move_x(Object *obj, float amount, int start) {
  if (obj->solids) {
    int step = pico_sign(amount);
    for (int i = start; i <= (int)pico_abs(amount); i++) {
      if (!obj_is_solid(obj,(float)step,0)) obj->x += step;
      else { obj->spd.x = 0; obj->rem.x = 0; break; }
    }
  } else obj->x += amount;
}
static void obj_move_y(Object *obj, float amount) {
  if (obj->solids) {
    int step = pico_sign(amount);
    for (int i = 0; i <= (int)pico_abs(amount); i++) {
      if (!obj_is_solid(obj,0,(float)step)) obj->y += step;
      else { obj->spd.y = 0; obj->rem.y = 0; break; }
    }
  } else obj->y += amount;
}
static void obj_move(Object *obj, float ox, float oy) {
  obj->rem.x += ox; int ax = pico_flr(obj->rem.x + 0.5f); obj->rem.x -= ax; obj_move_x(obj,(float)ax,0);
  obj->rem.y += oy; int ay = pico_flr(obj->rem.y + 0.5f); obj->rem.y -= ay; obj_move_y(obj,(float)ay);
}

// -------------------------------------------------------
// Hair
// -------------------------------------------------------
static void create_hair(Object *obj) {
  for (int i = 0; i < 5; i++)
    obj->hair[i] = {obj->x, obj->y, (int)pico_max(1, pico_min(2,(float)(3-i)))};
  obj->hair_init = true;
}

// Draws hair with the correct colour for the chosen character and dash state.
// djump_count is the object's current djump value; ch is the character.
// ghost=true renders at half brightness.
static void draw_hair_for(Object *obj, int facing, CharSelect ch, int djump_count, bool ghost = false) {
  uint16_t hair_col;
  if (ch == CHAR_MADELINE)
    hair_col = (djump_count > 0) ? MADELINE_HAIR_NORMAL : MADELINE_HAIR_DASH;
  else
    hair_col = (djump_count > 0) ? BADELINE_HAIR_NORMAL : BADELINE_HAIR_DASH;

  if (ghost) {
    uint8_t r = ((hair_col >> 11) & 0x1F) >> 1;
    uint8_t g = ((hair_col >>  5) & 0x3F) >> 1;
    uint8_t b = ( hair_col        & 0x1F) >> 1;
    hair_col = (r << 11) | (g << 5) | b;
  }

  float lx = obj->x + 4 - facing * 2;
  float ly = obj->y + (btn(K_DOWN) ? 4.0f : 3.0f);
  for (int i = 0; i < 5; i++) {
    obj->hair[i].x += (lx - obj->hair[i].x) / 1.5f;
    obj->hair[i].y += (ly + 0.5f - obj->hair[i].y) / 1.5f;
    circfill_rgb(obj->hair[i].x, obj->hair[i].y, obj->hair[i].size, hair_col);
    lx = obj->hair[i].x;
    ly = obj->hair[i].y;
  }
}

// Legacy wrapper used by spawn draw (always local player's character)
static void draw_hair(Object *obj, int facing) {
  draw_hair_for(obj, facing, selectedChar, obj->djump);
}

// -------------------------------------------------------
// Particle systems
// -------------------------------------------------------
struct Cloud    { float x, y, spd, w; };
struct Particle { float x, y, s, spd, off; int c; };
struct DeadPart { float x, y, t; Vec2f spd; };

#define MAX_CLOUDS 17
#define MAX_PARTS  25
#define MAX_DEAD   16

static Cloud    clouds[MAX_CLOUDS];
static Particle particles[MAX_PARTS];
static DeadPart dead_particles[MAX_DEAD];
static int      dead_count = 0;

// Menu-screen snow (separate from game particles, persists its own state)
struct SnowFlake { float x, y, spd, off, s; };
#define MAX_SNOW 25
static SnowFlake snow[MAX_SNOW];
static bool snow_inited = false;

static void init_snow() {
  for (int i=0;i<MAX_SNOW;i++)
    snow[i] = {pico_rnd(128), pico_rnd(68),
               0.3f + pico_rnd(2.0f),   // horizontal speed (varied)
               pico_rnd(1.0f),            // sin phase for vertical drift
               (float)(1 + (i % 2))};    // size alternates 1 or 2
  snow_inited = true;
}

static void init_particles() {
  for (int i = 0; i < MAX_CLOUDS; i++)
    clouds[i] = {pico_rnd(128), pico_rnd(128), 1+pico_rnd(4), 32+pico_rnd(32)};
  for (int i = 0; i < MAX_PARTS; i++)
    particles[i] = {pico_rnd(128), pico_rnd(128),
                    (float)pico_flr(pico_rnd(5)/4), 0.25f+pico_rnd(5),
                    pico_rnd(1), 6+pico_flr(0.5f+pico_rnd(1))};
}

// -------------------------------------------------------
// Forward declarations
// -------------------------------------------------------
static void load_room(int x, int y);
static void next_room();
static void restart_room();
static void kill_player(Object *obj);
static void break_fall_floor(Object *obj);
static void break_spring(Object *obj);

// -------------------------------------------------------
// Player type
// -------------------------------------------------------
static void player_init(Object *t) {
  t->p_jump=false; t->p_dash=false; t->grace=0; t->jbuffer=0;
  t->djump=max_djump; t->dash_time=0; t->dash_effect_time=0;
  t->dash_target={0,0}; t->dash_accel={0,0};
  t->hitbox={1,3,6,5}; t->spr_off=0; t->was_on_ground=false;
  create_hair(t);
}

static void player_update(Object *t) {
  if (pause_player) return;
  float input = btn(K_RIGHT) ? 1.0f : (btn(K_LEFT) ? -1.0f : 0.0f);

  if (spikes_at(t->x+t->hitbox.x, t->y+t->hitbox.y, t->hitbox.w, t->hitbox.h, t->spd.x, t->spd.y))
    kill_player(t);
  if (t->y > 128) kill_player(t);

  bool on_ground = obj_is_solid(t, 0, 1);
  bool on_ice    = obj_is_ice(t, 0, 1);

  if (on_ground && !t->was_on_ground) init_object(&T_smoke, t->x, t->y+4);

  bool jump = btn(K_JUMP) && !t->p_jump;
  t->p_jump = btn(K_JUMP);
  if (jump) t->jbuffer=4; else if (t->jbuffer>0) t->jbuffer--;

  bool dash = btn(K_DASH) && !t->p_dash;
  t->p_dash = btn(K_DASH);

  if (on_ground) {
    t->grace=6;
    if (t->djump < max_djump) { psfx(54); t->djump=max_djump; }
  } else if (t->grace>0) t->grace--;

  t->dash_effect_time--;
  if (t->dash_time > 0) {
    init_object(&T_smoke, t->x, t->y);
    t->dash_time--;
    t->spd.x = pico_appr(t->spd.x, t->dash_target.x, t->dash_accel.x);
    t->spd.y = pico_appr(t->spd.y, t->dash_target.y, t->dash_accel.y);
  } else {
    float maxrun=1.0f, accel=0.6f, deccel=0.15f;
    if (!on_ground) accel=0.4f; else if (on_ice) accel=0.05f;
    if (pico_abs(t->spd.x)>maxrun)
      t->spd.x=pico_appr(t->spd.x, pico_sign(t->spd.x)*maxrun, deccel);
    else
      t->spd.x=pico_appr(t->spd.x, input*maxrun, accel);
    if (t->spd.x != 0) t->flip_x=(t->spd.x<0);
    float maxfall=2.0f, gravity=0.21f;
    if (pico_abs(t->spd.y)<=0.15f) gravity*=0.5f;
    if (input!=0 && obj_is_solid(t,(int)input,0) && !obj_is_ice(t,(int)input,0)) {
      maxfall=0.4f;
      if (pico_rnd(10)<2) init_object(&T_smoke, t->x+input*6, t->y);
    }
    if (!on_ground) t->spd.y=pico_appr(t->spd.y, maxfall, gravity);
    if (t->jbuffer>0) {
      if (t->grace>0) {
        psfx(1); t->jbuffer=0; t->grace=0; t->spd.y=-2;
        init_object(&T_smoke, t->x, t->y+4);
      } else {
        int wd=(obj_is_solid(t,-3,0)?-1:(obj_is_solid(t,3,0)?1:0));
        if (wd!=0) {
          psfx(2); t->jbuffer=0; t->spd.y=-2; t->spd.x=-wd*(maxrun+1);
          if (!obj_is_ice(t,wd*3,0)) init_object(&T_smoke, t->x+wd*6, t->y);
        }
      }
    }
    float d_full=5.0f, d_half=d_full*0.70710678118f;
    if (t->djump>0 && dash) {
      init_object(&T_smoke, t->x, t->y);
      t->djump--; t->dash_time=4; has_dashed=true; t->dash_effect_time=10;
      float v_input=btn(K_UP)?-1.0f:(btn(K_DOWN)?1.0f:0.0f);
      if (input!=0) {
        if (v_input!=0) { t->spd.x=input*d_half; t->spd.y=v_input*d_half; }
        else            { t->spd.x=input*d_full;  t->spd.y=0; }
      } else if (v_input!=0) { t->spd.x=0; t->spd.y=v_input*d_full; }
      else                   { t->spd.x=t->flip_x?-1.0f:1.0f; t->spd.y=0; }
      psfx(3); freeze=2; shake=6;
      t->dash_target={2.0f*pico_sign(t->spd.x), 2.0f*pico_sign(t->spd.y)};
      t->dash_accel={1.5f,1.5f};
      if (t->spd.y<0) t->dash_target.y*=0.75f;
      if (t->spd.y!=0) t->dash_accel.x*=0.70710678118f;
      if (t->spd.x!=0) t->dash_accel.y*=0.70710678118f;
    } else if (dash && t->djump<=0) {
      psfx(9); init_object(&T_smoke, t->x, t->y);
    }
  }

  t->spr_off += 0.25f;
  if (!on_ground) {
    t->spr_id = obj_is_solid(t,(int)input,0) ? 5 : 3;
  } else if (btn(K_DOWN)) { t->spr_id=6; }
  else if (btn(K_UP))     { t->spr_id=7; }
  else if (t->spd.x==0 || (!btn(K_LEFT)&&!btn(K_RIGHT))) { t->spr_id=1; }
  else                    { t->spr_id=1+(int)t->spr_off%4; }

  if (t->y < -4 && level_index() < 30) next_room();
  t->was_on_ground = on_ground;

  // Send BLE packet in race mode
  if (gameMode == MODE_RACE && ble_connected) {
    PeerPacket pkt;
    pkt.x       = (int16_t)t->x;
    pkt.y       = (int16_t)t->y;
    pkt.room_x  = (uint8_t)room.x;
    pkt.room_y  = (uint8_t)room.y;
    pkt.djump   = (uint8_t)t->djump;
    pkt.flip_x  = (uint8_t)(t->flip_x ? 1 : 0);
    pkt.char_id = (uint8_t)selectedChar;
    pkt.finished = (uint8_t)(local_finished ? 1 : 0);
    if (ble_is_host && ble_char) {
      // Host notifies client
      ble_char->setValue((uint8_t*)&pkt, sizeof(pkt));
      ble_char->notify();
    } else if (!ble_is_host && ble_remote_char) {
      // Client writes to host
      ble_remote_char->writeValue((uint8_t*)&pkt, sizeof(pkt), false);
    }
  }
}

static void player_draw(Object *t) {
  if (t->x < -1 || t->x > 121) { t->x=pico_clamp(t->x,-1,121); t->spd.x=0; }
  draw_hair_for(t, t->flip_x?-1:1, selectedChar, t->djump);
  draw_player_sprite(t->x, t->y, t->flip_x, selectedChar);
}

// -------------------------------------------------------
// Player spawn type
// -------------------------------------------------------
static void player_spawn_init(Object *t) {
  pico_sfx(4); t->spr_id=3; t->target={t->x,t->y};
  t->y=128; t->spd.y=-4; t->state=0; t->delay=0; t->solids=false;
  create_hair(t);
}
static void player_spawn_update(Object *t) {
  if (t->state==0) {
    if (t->y < t->target.y+16) { t->state=1; t->delay=3; }
  } else if (t->state==1) {
    t->spd.y+=0.5f;
    if (t->spd.y>0 && t->delay>0) { t->spd.y=0; t->delay--; }
    if (t->spd.y>0 && t->y>t->target.y) {
      t->y=t->target.y; t->spd={0,0}; t->state=2; t->delay=5;
      shake=5; init_object(&T_smoke,t->x,t->y+4); pico_sfx(5);
    }
  } else if (t->state==2) {
    t->delay--; t->spr_id=6;
    if (t->delay<0) { destroy_object(t); init_object(&T_player,t->x,t->y); }
  }
}
static void player_spawn_draw(Object *t) {
  draw_hair(t, 1);
  draw_player_sprite(t->x, t->y, t->flip_x, selectedChar);
}

// -------------------------------------------------------
// Spring type
// -------------------------------------------------------
static void spring_init(Object *t) { t->hide_in=0; t->hide_for=0; }
static void spring_update(Object *t) {
  if (t->hide_for>0) {
    t->hide_for--;
    if (t->hide_for<=0) { t->spr_id=18; t->delay=0; }
  } else if (t->spr_id==18) {
    Object *hit=obj_collide(t,&T_player,0,0);
    if (hit && hit->spd.y>=0) {
      t->spr_id=19; hit->y=t->y-4; hit->spd.x*=0.2f; hit->spd.y=-3;
      hit->djump=max_djump; t->delay=10; init_object(&T_smoke,t->x,t->y);
      Object *below=obj_collide(t,&T_fall_floor,0,1);
      if (below) break_fall_floor(below); psfx(8);
    }
  } else if (t->delay>0) { t->delay--; if (t->delay<=0) t->spr_id=18; }
  if (t->hide_in>0) { t->hide_in--; if (t->hide_in<=0) { t->hide_for=60; t->spr_id=0; } }
}
static void break_spring(Object *obj) { obj->hide_in=15; }

// -------------------------------------------------------
// Fall floor type
// -------------------------------------------------------
static void fall_floor_init(Object *t) { t->state=0; t->solids=true; }
static void fall_floor_update(Object *t) {
  if (t->state==0) {
    if (obj_check(t,&T_player,0,-1)||obj_check(t,&T_player,-1,0)||obj_check(t,&T_player,1,0))
      break_fall_floor(t);
  } else if (t->state==1) {
    t->delay--;
    if (t->delay<=0) { t->state=2; t->delay=60; t->collideable=false; }
  } else if (t->state==2) {
    t->delay--;
    if (t->delay<=0 && !obj_check(t,&T_player,0,0)) {
      psfx(7); t->state=0; t->collideable=true; init_object(&T_smoke,t->x,t->y);
    }
  }
}
static void fall_floor_draw(Object *t) {
  if (t->state!=2) spr(t->state!=1?23:23+(15-t->delay)/5, t->x, t->y);
}
static void break_fall_floor(Object *obj) {
  if (obj->state==0) {
    psfx(15); obj->state=1; obj->delay=15; init_object(&T_smoke,obj->x,obj->y);
    Object *hit=obj_collide(obj,&T_spring,0,-1); if (hit) break_spring(hit);
  }
}

// -------------------------------------------------------
// Smoke type
// -------------------------------------------------------
static void smoke_init(Object *t) {
  t->spr_id=29; t->spd.y=-0.1f; t->spd.x=0.3f+pico_rnd(0.2f);
  t->x+=-1+pico_rnd(2); t->y+=-1+pico_rnd(2);
  t->flip_x=pico_maybe(); t->flip_y=pico_maybe(); t->solids=false;
}
static void smoke_update(Object *t) {
  t->spr_off+=0.2f; if (t->spr_off>=3.0f) destroy_object(t);
  t->spr_id=29+(int)t->spr_off;
}

static void smoke_draw(Object *t) {
  float life = 1.0f - (t->spr_off / 3.0f);
  float r = 1.5f + (1.0f - life) * 3.0f;
  int col = (frames % 2 == 0 || t->spr_off > 1.5f) ? 6 : 7;
  circfill(t->x + 4 + (t->flip_x ? -1 : 1), t->y + 4, r, col);
}

// -------------------------------------------------------
// Fruit type
// -------------------------------------------------------
static void fruit_init(Object *t) { t->start=t->y; t->spr_off=0; }
static void fruit_update(Object *t) {
  Object *hit=obj_collide(t,&T_player,0,0);
  if (hit) {
    hit->djump=max_djump; sfx_timer=20; pico_sfx(13);
    got_fruit[level_index()]=true; init_object(&T_lifeup,t->x,t->y);
    destroy_object(t); return;
  }
  t->spr_off+=1; t->y=t->start+pico_sin(t->spr_off/40.0f)*2.5f;
}

// -------------------------------------------------------
// Lifeup type
// -------------------------------------------------------
static void lifeup_init(Object *t) {
  t->spd.y=-0.25f; t->duration=30; t->x-=2; t->y-=4; t->flash=0; t->solids=false;
}
static void lifeup_update(Object *t) { t->duration--; if (t->duration<=0) destroy_object(t); }
static void lifeup_draw(Object *t) {
  t->flash+=0.5f; pico_print("1000",(int)t->x-2,(int)t->y,7+(int)t->flash%2);
}

// -------------------------------------------------------
// Balloon type
// -------------------------------------------------------
static void balloon_init(Object *t) {
  t->offset=pico_rnd(1); t->start=t->y; t->timer=0; t->hitbox={-1,-1,10,10};
}
static void balloon_update(Object *t) {
  if (t->spr_id==22) {
    t->offset+=0.01f; t->y=t->start+pico_sin(t->offset)*2;
    Object *hit=obj_collide(t,&T_player,0,0);
    if (hit && hit->djump<max_djump) {
      psfx(6); init_object(&T_smoke,t->x,t->y);
      hit->djump=max_djump; t->spr_id=0; t->timer=60;
    }
  } else if (t->timer>0) { t->timer--; }
  else { psfx(7); init_object(&T_smoke,t->x,t->y); t->spr_id=22; }
}
static void balloon_draw(Object *t) {
  if (t->spr_id==22) { spr(13+(int)(t->offset*8)%3,t->x,t->y+6); spr(t->spr_id,t->x,t->y); }
}

// -------------------------------------------------------
// Fake wall type
// -------------------------------------------------------
static void fake_wall_update(Object *t) {
  t->hitbox={-1,-1,18,18};
  Object *hit=obj_collide(t,&T_player,0,0);
  if (hit && hit->dash_effect_time>0) {
    hit->spd.x=-pico_sign(hit->spd.x)*1.5f; hit->spd.y=-1.5f; hit->dash_time=-1;
    sfx_timer=20; pico_sfx(16); destroy_object(t);
    init_object(&T_smoke,t->x,t->y); init_object(&T_smoke,t->x+8,t->y);
    init_object(&T_smoke,t->x,t->y+8); init_object(&T_smoke,t->x+8,t->y+8);
    init_object(&T_fruit,t->x+4,t->y+4);
  }
  t->hitbox={0,0,16,16};
}
static void fake_wall_draw(Object *t) {
  spr(64,t->x,t->y); spr(65,t->x+8,t->y); spr(80,t->x,t->y+8); spr(81,t->x+8,t->y+8);
}

// -------------------------------------------------------
// Key type
// -------------------------------------------------------
static void key_update(Object *t) {
  int was=pico_flr(t->spr_off);
  t->spr_off=9+(pico_sin((float)frames/30.0f)+0.5f)*1.0f;
  int is=pico_flr(t->spr_off);
  if (is==10&&is!=was) t->flip_x=!t->flip_x;
  t->spr_id=(int)t->spr_off;
  if (obj_check(t,&T_player,0,0)) { pico_sfx(23); sfx_timer=10; destroy_object(t); has_key=true; }
}

// -------------------------------------------------------
// Chest type
// -------------------------------------------------------
static void chest_init(Object *t) { t->x-=4; t->start=t->x; t->timer=20; }
static void chest_update(Object *t) {
  if (has_key) {
    t->timer--; t->x=t->start-1+pico_rnd(3);
    if (t->timer<=0) { sfx_timer=20; pico_sfx(16); init_object(&T_fruit,t->x,t->y-4); destroy_object(t); }
  }
}

// -------------------------------------------------------
// Platform type
// -------------------------------------------------------
static void platform_init(Object *t) { t->x-=4; t->solids=false; t->hitbox.w=16; t->last=t->x; }
static void platform_update(Object *t) {
  t->spd.x=t->dir*0.65f;
  if (t->x<-16) t->x=128; else if (t->x>128) t->x=-16;
  if (!obj_check(t,&T_player,0,0)) {
    Object *hit=obj_collide(t,&T_player,0,-1); if (hit) obj_move_x(hit,t->x-t->last,1);
  }
  t->last=t->x;
}
static void platform_draw(Object *t) { spr(11,t->x,t->y-1); spr(12,t->x+8,t->y-1); }

// -------------------------------------------------------
// Flag type
// -------------------------------------------------------
static void flag_init(Object *t) {
  t->x+=5; t->score=0; t->show=false;
  for (int i=0;i<30;i++) if (got_fruit[i]) t->score++;
}
static void flag_draw(Object *t) {
  t->spr_id=118+(frames/5)%3; spr(t->spr_id,t->x,t->y);
  if (t->show) {
    rectfill(32,2,96,31,0); spr(26,55,6);
    char buf[16]; sprintf(buf,"x%d",t->score); pico_print(buf,64,9,7);
    char tbuf[16]; int h=minutes/60,m=minutes%60;
    sprintf(tbuf,"%02d:%02d:%02d",h,m,seconds);
    rectfill(49,16,49+32,16+6,0); pico_print(tbuf,50,17,7);
    char dbuf[24]; sprintf(dbuf,"deaths:%d",deaths); pico_print(dbuf,48,24,7);
  } else if (obj_check(t,&T_player,0,0)) {
    pico_sfx(55); sfx_timer=30; t->show=true;
  }
}

// -------------------------------------------------------
// Room title type
// -------------------------------------------------------
static void room_title_init(Object *t) { t->delay=5; }
static void room_title_draw(Object *t) {
  t->delay--; if (t->delay<-30) { destroy_object(t); return; }
  if (t->delay<0) {
    rectfill(24,58,104,70,0);
    if (room.x==3&&room.y==1)      pico_print("old site",48,62,7);
    else if (level_index()==30)     pico_print("summit",52,62,7);
    else {
      int level=(1+level_index())*100;
      char buf[12]; sprintf(buf,"%d m",level);
      pico_print(buf,52+(level<1000?2:0),62,7);
    }
    char tbuf[16]; int h=minutes/60,m2=minutes%60;
    sprintf(tbuf,"%02d:%02d:%02d",h,m2,seconds);
    rectfill(4,4,36,10,0); pico_print(tbuf,5,5,7);
  }
}

// -------------------------------------------------------
// Object type descriptors
// -------------------------------------------------------
static void set_type(ObjectType &t, int tile, bool if_not_fruit,
                     void(*init_fn)(Object*), void(*update_fn)(Object*), void(*draw_fn)(Object*)) {
  t.tile=tile; t.if_not_fruit=if_not_fruit;
  t.init_fn=init_fn; t.update_fn=update_fn; t.draw_fn=draw_fn;
}

static void init_types() {
  set_type(T_player,       0,   false, player_init,       player_update,       player_draw      );
  set_type(T_player_spawn, 255, false, player_spawn_init, player_spawn_update, player_spawn_draw);
  set_type(T_spring,       18,  false, spring_init,       spring_update,       nullptr          );
  set_type(T_balloon,      22,  false, balloon_init,      balloon_update,      balloon_draw     );
  set_type(T_fall_floor,   23,  false, fall_floor_init,   fall_floor_update,   fall_floor_draw  );
set_type(T_smoke, 0, false, smoke_init, smoke_update, smoke_draw);
  set_type(T_fruit,        26,  true,  fruit_init,        fruit_update,        nullptr          );
  set_type(T_lifeup,       0,   false, lifeup_init,       lifeup_update,       lifeup_draw      );
  set_type(T_fake_wall,    64,  true,  nullptr,           fake_wall_update,    fake_wall_draw   );
  set_type(T_key,          8,   true,  nullptr,           key_update,          nullptr          );
  set_type(T_platform,     11,  false, platform_init,     platform_update,     platform_draw    );
  set_type(T_room_title,   0,   false, room_title_init,   nullptr,             room_title_draw  );
  set_type(T_flag,         118, false, flag_init,         nullptr,             flag_draw        );
}

// -------------------------------------------------------
// Object pool management
// -------------------------------------------------------
static Object *init_object(ObjectType *type, float x, float y) {
  if (type->if_not_fruit && got_fruit[level_index()]) return nullptr;
  for (int i=0;i<MAX_OBJECTS;i++) {
    if (!objects[i].alive) {
      objects[i]={}; objects[i].alive=true; objects[i].type=type;
      objects[i].collideable=true; objects[i].solids=true;
      objects[i].spr_id=type->tile; objects[i].x=x; objects[i].y=y;
      objects[i].hitbox={0,0,8,8};
      if (type->init_fn) type->init_fn(&objects[i]);
      return &objects[i];
    }
  }
  return nullptr;
}
static void destroy_object(Object *obj) { if (obj) obj->alive=false; }

// -------------------------------------------------------
// Kill player
// -------------------------------------------------------
static void kill_player(Object *obj) {
  sfx_timer=12; pico_sfx(0); deaths++; shake=10; dead_count=0;
  for (int dir=0;dir<8;dir++) {
    if (dead_count>=MAX_DEAD) break;
    float angle=dir/8.0f;
    dead_particles[dead_count++]={obj->x+4,obj->y+4,10,{pico_sin(angle)*3,pico_cos(angle)*3}};
  }
  destroy_object(obj); restart_room();
}

// -------------------------------------------------------
// Room loading
// -------------------------------------------------------
static void restart_room() { will_restart=true; delay_restart=15; }

static void next_room() {
  int next = level_index() + 1;
  if (next >= 3) {
    local_finished = true;
    if (gameMode == MODE_RACE && ble_connected) {
      PeerPacket pkt = {};
      pkt.finished = 1;
      pkt.char_id  = (uint8_t)selectedChar;
      for (int i = 0; i < 5; i++) {
        if (ble_is_host && ble_char) {
          ble_char->setValue((uint8_t*)&pkt, sizeof(pkt));
          ble_char->notify();
        } else if (!ble_is_host && ble_remote_char) {
          ble_remote_char->writeValue((uint8_t*)&pkt, sizeof(pkt), false);
        }
        delay(20);
      }
    }
    if (gameMode == MODE_RACE) {
      endResult = peer_finished_first ? END_LOSE : END_WIN;
    } else {
      endResult = END_SOLO;
    }
    end_frames = 0;
    gameMode = MODE_END;
    return;
  }
  load_room(next%8, next/8);
}

static ObjectType *all_types[] = {
  &T_player_spawn,&T_spring,&T_balloon,&T_fall_floor,
  &T_fruit,&T_fake_wall,&T_key,&T_flag
};
static const int NUM_TYPES = sizeof(all_types)/sizeof(all_types[0]);

struct SpawnPoint { int x, y; };
static const SpawnPoint SPAWNS[] = {
  {16, 112},   // room 0
  {8, 104},  // left side, on the floor
  {8, 104},  // left side, on the floor
};


static void load_room(int x, int y) {
  has_dashed=false; has_key=false;
  for (int i=0;i<MAX_OBJECTS;i++) objects[i].alive=false;
  room.x=x; room.y=y;
  for (int tx=0;tx<16;tx++) {
    for (int ty=0;ty<16;ty++) {
      uint8_t tile=mget(tx,ty);
      if (tile==11)      { auto *p=init_object(&T_platform,tx*8,ty*8); if(p) p->dir=-1; }
      else if (tile==12) { auto *p=init_object(&T_platform,tx*8,ty*8); if(p) p->dir=1;  }
      else {
        for (int k=0;k<NUM_TYPES;k++)
          if (all_types[k]->tile==tile) init_object(all_types[k],tx*8,ty*8);
      }
    }
  }
  if (!is_title()) init_object(&T_room_title,0,0);
  // then in load_room():
  int idx = level_index();
  int spawnX = (idx < 3) ? SPAWNS[idx].x : 56;
  int spawnY = (idx < 3) ? SPAWNS[idx].y : 112;
  init_object(&T_player_spawn, spawnX, spawnY);
}

// -------------------------------------------------------
// Title / begin game
// -------------------------------------------------------
static void title_screen() {
  for (int i=0;i<30;i++) got_fruit[i]=false;
  frames=0; deaths=0; max_djump=1;
  start_game=false; start_game_flash=0;
  pico_music(40,0,7);
  load_room(7,3);
}
static void begin_game() {
  peer_finished_first = false;
  local_finished = false;
  frames=0; seconds=0; minutes=0; music_timer=0; start_game=false;
  pico_music(0,0,7);
  load_room(0,0);
}

// -------------------------------------------------------
// BLE callbacks
// -------------------------------------------------------
class BLEConnectionCB : public BLEServerCallbacks {
  void onConnect(BLEServer*)    override { ble_connected=true;  }
  void onDisconnect(BLEServer*) override { ble_connected=false; }
};

class BLEDataCB : public BLECharacteristicCallbacks {
  void onWrite(BLECharacteristic *c) override {
    std::string val = c->getValue();
    if (val.size() == sizeof(PeerPacket)) {
      memcpy(&peer_state, val.data(), sizeof(PeerPacket));
      peer_valid = true;
      if (peer_state.finished && gameMode == MODE_RACE) {
        peer_finished_first = true;
        endResult = END_LOSE;
        end_frames = 0;
        gameMode = MODE_END;
      }
    }
  }
};

// Client notification callback
static void ble_notify_cb(BLERemoteCharacteristic*, uint8_t *data, size_t len, bool) {
  if (len == sizeof(PeerPacket)) {
    memcpy(&peer_state, data, sizeof(PeerPacket));
    peer_valid = true;
    if (peer_state.finished && gameMode == MODE_RACE) {
      peer_finished_first = true;
      endResult = END_LOSE;
      end_frames = 0;
      gameMode = MODE_END;
    }
  }
}

static void ble_start_host() {
  BLEDevice::init(BLE_DEVICE_NAME);
  ble_server = BLEDevice::createServer();
  ble_server->setCallbacks(new BLEConnectionCB());
  BLEService *svc = ble_server->createService(BLE_SERVICE_UUID);
  ble_char = svc->createCharacteristic(BLE_CHAR_UUID,
    BLECharacteristic::PROPERTY_READ |
    BLECharacteristic::PROPERTY_WRITE |
    BLECharacteristic::PROPERTY_NOTIFY);
  ble_char->setCallbacks(new BLEDataCB());

  // Add descriptor so client can subscribe to notifications from host
  BLE2902 *desc = new BLE2902();
  desc->setNotifications(true);
  ble_char->addDescriptor(desc);

  svc->start();
  BLEAdvertising *adv = BLEDevice::getAdvertising();
  adv->addServiceUUID(BLE_SERVICE_UUID);
  adv->start();
  ble_is_host = true;
  ble_scanning = true;
}

static bool ble_found_device = false;
static BLEAdvertisedDevice ble_target_device;

class BLEScanCB : public BLEAdvertisedDeviceCallbacks {
  void onResult(BLEAdvertisedDevice dev) override {
    if (dev.haveServiceUUID() && dev.isAdvertisingService(BLEUUID(BLE_SERVICE_UUID))) {
      BLEDevice::getScan()->stop();
      ble_target_device = dev;
      ble_found_device = true;
    }
  }
};

static void ble_start_client() {
  BLEDevice::init(BLE_DEVICE_NAME);
  BLEScan *scan = BLEDevice::getScan();
  scan->setAdvertisedDeviceCallbacks(new BLEScanCB());
  scan->setActiveScan(true);
  scan->start(30, false);
  ble_is_host = false;
  ble_scanning = true;
}

static void ble_init_role() {
#ifdef BLE_ROLE_HOST
  ble_start_host();
#else
  ble_start_client();
#endif
}


static void ble_try_connect() {
  if (!ble_found_device) return;
  ble_client=BLEDevice::createClient();
  if (!ble_client->connect(&ble_target_device)) return;
  BLERemoteService *svc=ble_client->getService(BLE_SERVICE_UUID);
  if (!svc) { ble_client->disconnect(); return; }
  ble_remote_char=svc->getCharacteristic(BLE_CHAR_UUID);
  if (!ble_remote_char) { ble_client->disconnect(); return; }
  if (ble_remote_char->canNotify())
    ble_remote_char->registerForNotify(ble_notify_cb);
  ble_connected=true;
}

// -------------------------------------------------------
// Ghost renderer — draws peer player if on same room
// -------------------------------------------------------
static void draw_ghost() {
  if (!peer_valid) return;
  if (peer_state.room_x != room.x || peer_state.room_y != room.y) return;

  // Reuse a temporary Object just for hair node state — static so hair physics persists
  static Object ghost_obj;
  static bool ghost_init=false;
  if (!ghost_init) {
    ghost_obj={}; ghost_obj.x=peer_state.x; ghost_obj.y=peer_state.y;
    create_hair(&ghost_obj); ghost_init=true;
  }
  ghost_obj.x=(float)peer_state.x;
  ghost_obj.y=(float)peer_state.y;
  ghost_obj.djump=peer_state.djump;
  ghost_obj.flip_x=(peer_state.flip_x!=0);

  CharSelect peerCh=(peer_state.char_id==1)?CHAR_BADELINE:CHAR_MADELINE;
  draw_hair_for(&ghost_obj, ghost_obj.flip_x?-1:1, peerCh, ghost_obj.djump, true);
  draw_player_sprite(ghost_obj.x, ghost_obj.y, ghost_obj.flip_x, peerCh, true);
}

// -------------------------------------------------------
// Main screen drawing — all in PICO-8 coords (0..127)
// Layout (128 rows total):
//   0..69   sky + mountain scene
//   70..71  ground line
//   72..79  title text
//   80..95  character preview cards (16px tall at 2× = 16 PICO rows)
//   96..103 character names
//  104..127 → BLE bar drawn in raw screen pixels at y=208 (PICO row 108)
//            so it sits cleanly in the black area below the canvas
// -------------------------------------------------------

// Draw one pixel-art character card entirely in PICO-8 coords.
// px,py = top-left of the 16×16 preview area (2× scaled sprite).
static void draw_char_preview_pico(int px, int py, CharSelect ch, bool selected) {
  const uint16_t *pal = (ch==CHAR_MADELINE) ? MADELINE_PAL : BADELINE_PAL;
  uint16_t hair_col   = (ch==CHAR_MADELINE) ? MADELINE_HAIR_NORMAL : BADELINE_HAIR_NORMAL;

  // Background card (1px padding around 16×16 sprite)
  int bg_col = selected ? ((ch==CHAR_MADELINE) ? 8 : 13) : 1;
  rectfill(px-1, py-1, px+16, py+16, bg_col);

  // Draw sprite pixels at 2× scale using raw canvas calls to stay sharp
  for (int row=0;row<8;row++) {
    for (int col=0;col<8;col++) {
      int c = PLAYER_SPR[row][col];
      if (c==0) continue;
      uint16_t color = (c==9) ? hair_col : pal[c];
      // Each pixel → 2×2 block in PICO space → 4×4 on screen (SCALE=2)
      int bx = OFFSET_X + (px + col*2) * SCALE;
      int by = OFFSET_Y + (py + row*2) * SCALE;
      tft.fillRect(bx, by, 2*SCALE, 2*SCALE, color);
    }
  }
}

static void draw_mountain() {
  // Stars — deterministic, no flicker
  for (int i=0;i<18;i++) {
    int sx=(i*41+11)%122; int sy=(i*17+5)%60;
    rectfill(sx,sy,sx,sy, (i%4==0)?7:6);
  }

  // Animated snow — mirrors room particle system exactly
  if (!snow_inited) init_snow();
  for (int i=0;i<MAX_SNOW;i++) {
    snow[i].x   += snow[i].spd;
    snow[i].y   += pico_sin(snow[i].off) * 0.4f;
    snow[i].off += pico_min(0.05f, snow[i].spd / 32.0f);
    int s = (int)snow[i].s;
    // keep flakes in the sky zone (above y=68)
    if (snow[i].y < 0)  snow[i].y = pico_rnd(68);
    if (snow[i].y > 68) snow[i].y = pico_rnd(68);
    if (snow[i].x > 132) { snow[i].x = -4; snow[i].y = pico_rnd(68); }
    rectfill((int)snow[i].x, (int)snow[i].y,
             (int)snow[i].x + s, (int)snow[i].y + s, 7);
  }

  // Back hills (colour 2 = dark purple) — capped at y=68
  for (int x=0;x<=56;x++) {
    int h = 52 + abs(x-28)*16/28;
    if (h>68) h=68;
    rectfill(x, h, x, 68, 2);
  }
  for (int x=72;x<=127;x++) {
    int h = 52 + abs(x-100)*16/28;
    if (h>68) h=68;
    rectfill(x, h, x, 68, 2);
  }

  // Main mountain (colour 1 = dark blue), peak x=64 y=4, base y=70
  for (int x=10;x<=118;x++) {
    int h = 4 + abs(x-64)*66/54;
    if (h>70) h=70;
    rectfill(x, h, x, 70, 1);
  }

  // Wings — triangles pointing UP and OUT from the mountain slope
  // Madeline (left): base on slope ~y=26..38, tip points up-left
  {
    int col = (selectedChar==CHAR_MADELINE) ? 8 : 5;
    for (int i=0;i<12;i++)
      rectfill(52-i*2, 38-i, 52, 38-i, col);
  }
  // Badeline (right): mirror — tip points up-right
  {
    int col = (selectedChar==CHAR_BADELINE) ? 13 : 5;
    for (int i=0;i<12;i++)
      rectfill(76, 38-i, 76+i*2, 38-i, col);
  }

  // Ground line
  rectfill(0,70,127,71,1);
}

static void draw_main_screen() {
  canvas.fillSprite(PICO_PAL[0]);

  // --- Sky + mountain (rows 0..71) ---
  rectfill(0,0,127,71,0);
  draw_mountain();

  // --- Title (rows 73..80) ---
  tft.setTextSize(2);
  pico_print("CELESTE",   43, 73, 7);
  tft.setTextSize(1);
  // pico_print("M5CORE2 ED",36, 80, 5);

  // --- Character previews (rows 84..99) ---
  // Left card x=18, right card x=92. Sprite is 8px wide at 2× = 16px.
  // Card spans x=17..34 (centre=25) and x=91..108 (centre=99).
  draw_char_preview_pico(18, 84, CHAR_MADELINE, selectedChar==CHAR_MADELINE);
  draw_char_preview_pico(92, 84, CHAR_BADELINE, selectedChar==CHAR_BADELINE);

  // --- Names centred under each card (row 101) ---
  // pico_print uses M5GFX default font: 6px per char at textSize(1).
  // At SCALE=2 that's 12 screen px per char, but pico_print works in PICO coords:
  // each char ≈ 4 PICO px wide. "MADELINE" = 8*4 = 32px. Centre=25 → start=25-16=9
  // "BADELINE" = 8*4 = 32px. Centre=99 → start=99-16=83
  pico_print("MADELINE",  15, 101, selectedChar==CHAR_MADELINE ? 7 : 5);
  pico_print("BADELINE", 88, 101, selectedChar==CHAR_BADELINE ? 7 : 5);

  // --- BLE bar in raw screen pixels ---
  // PICO row 104 → screen y = OFFSET_Y + 104*SCALE = -8+208 = 200.
  // Names end at PICO row ~109 → screen y ~210. Use bar_y=212 for a 2px gap.
  int bar_y = 212;
  tft.fillRect(0, bar_y, 320, 28, rgb(8,8,24));
  tft.setTextSize(1);
  tft.setTextColor(PICO_PAL[5]);
  tft.drawString("BLUETOOTH:", 8, bar_y+3);
  if (ble_connected) {
    tft.setTextColor(rgb(58,181,164));
    tft.drawString("CONNECTED - RACE READY", 84, bar_y+3);
  } else if (ble_scanning) {
    tft.setTextColor(rgb(255,153,0));
    static const char *dots[]={"SEARCHING.","SEARCHING..","SEARCHING..."};
    tft.drawString(dots[(frames/5)%3], 84, bar_y+3);
  } else {
    tft.setTextColor(PICO_PAL[5]);
    tft.drawString("NOT STARTED", 84, bar_y+3);
  }
  tft.setTextColor(rgb(100,180,200));
  tft.drawString("Y=MADELINE  A=BADELINE  START=RACE  SELECT=SOLO", 8, bar_y+16);
}

// -------------------------------------------------------
// End screen
// All drawing in PICO-8 coords (0..127) + raw screen calls
// for the stats bar, mirroring the main screen pattern.
//
// Layout (128 rows):
//   0..3    result text (WIN! / LOSE / SUMMIT!)
//   4..69   sky bands + distant mountains
//  70..127  summit cliff + clouds + sprite + flag
// Stats bar drawn in raw screen pixels at y=210.
// -------------------------------------------------------

// Sky color bands — warm pink/purple matching the reference art
static void end_draw_sky(bool dim) {
  static const struct { int y,h; uint16_t c; } bands[]={
    {0,  22, rgb(107,90,138)},
    {22, 22, rgb(155,112,144)},
    {44, 22, rgb(192,136,136)},
    {66, 20, rgb(212,160,144)},
    {86, 22, rgb(224,184,168)},
    {108,20, rgb(232,200,184)},
  };
  for (auto &b : bands) {
    uint16_t c = b.c;
    if (dim) {
      uint8_t r=((c>>11)&0x1F)>>1;
      uint8_t g=((c>>5 )&0x3F)>>1;
      uint8_t b2=(c     &0x1F)>>1;
      c=(r<<11)|(g<<5)|b2;
    }
    tft.fillRect(0, OFFSET_Y+b.y*SCALE, 320, b.h*SCALE, b.c);
  }
}

// Distant soft mountain silhouettes
static void end_draw_far_mountains() {
  uint16_t col = rgb(192,154,176);
  // Four soft peaks drawn as filled triangles
  static const struct { int cx,cy,hw; } peaks[]={{30,82,20},{130,79,18},{240,81,19},{310,84,15}};
  for (auto &p : peaks) {
    for (int x=p.cx-p.hw; x<=p.cx+p.hw; x++) {
      int h = p.cy + abs(x-p.cx)*(105-p.cy)/p.hw;
      if (h>105) h=105;
      tft.fillRect(OFFSET_X+x*SCALE, OFFSET_Y+h*SCALE,
                   SCALE, (105-h)*SCALE, col);
    }
  }
}

// Cloud blobs — ellipses drawn as stacked rectfills approximating ellipse shape
static void end_draw_cloud(int cx, int cy, int rx, int ry, uint16_t col) {
  for (int dy=-ry; dy<=ry; dy++) {
    float frac = 1.0f - ((float)(dy*dy))/((float)(ry*ry));
    if (frac<=0) continue;
    int w = (int)(rx * sqrtf(frac));
    tft.fillRect(OFFSET_X+(cx-w)*SCALE, OFFSET_Y+(cy+dy)*SCALE, w*2*SCALE, SCALE, col);
  }
}

static void end_draw_clouds() {
  // Large base cloud bank
  static const struct { int x,y,rx,ry; uint16_t c; } blobs[]={
    { 16,98,30,14,rgb(237,232,224)}, {55,100,38,15,rgb(232,226,216)},
    {105,97,40,16,rgb(237,232,224)}, {155,99,35,14,rgb(224,218,206)},
    {200,97,38,15,rgb(237,232,224)}, {245,100,33,14,rgb(232,226,216)},
    {295,98,30,15,rgb(237,232,224)},
    // Purple-tinted clouds
    { 80,96,28,12,rgb(196,172,208)}, {140,97,24,10,rgb(200,176,212)}, {1,97,24,10,rgb(200,176,212)},
    // Upper wispy
    { 40,82,16, 7,rgb(221,214,204)}, {120,80,14, 6,rgb(216,208,200)},
    {220,81,18, 7,rgb(221,214,204)},
  };
  for (auto &b : blobs) end_draw_cloud(b.x,b.y,b.rx,b.ry,b.c);
}

// Dark purple cliff summit with rounded snow
static void end_draw_summit(bool show_flag) {
  // Cliff body (dark purple)
  uint16_t cliff_dark  = rgb(61,32,96);
  uint16_t cliff_light = rgb(78,40,120);
  uint16_t snow_col    = rgb(240,236,232);
  uint16_t snow_soft   = rgb(232,228,224);

  // Main cliff — column by column
  for (int x=30;x<=98;x++) {
    int top;
    if      (x<45) top=88-(x-30)*13/15;  // left slope up
    else if (x<55) top=75-(x-45)*3/10;   // left shoulder
    else if (x<=73) top=77;              // flat top
    else if (x<83) top=77+(x-73)*3/10;  // right shoulder
    else            top=80+(x-83)*13/15;  // right slope down
    if (top<75) top=75;
    tft.fillRect(OFFSET_X+x*SCALE, OFFSET_Y+top*SCALE,
                 SCALE, (105-top)*SCALE, cliff_dark);
    // Lighter top face (top 3 rows)
    tft.fillRect(OFFSET_X+x*SCALE, OFFSET_Y+top*SCALE,
                 SCALE, 3*SCALE, cliff_light);
  }

  // Rounded snow cap — wider in middle, tapers and rounds at edges
  // Uses a sin-based profile for organic softness
  for (int x=50;x<=78;x++) {
    float t = (float)(x-50)/28.0f;  // 0..1 across snow width
    // Gentle arch: highest in middle, rounds down at edges
    int snow_h = (int)(3.0f + 3.5f*sinf(t*M_PI));
    int base_y = 77;
    // Snow top
    tft.fillRect(OFFSET_X+x*SCALE, OFFSET_Y+(base_y-snow_h)*SCALE,
                 SCALE, (snow_h+2)*SCALE, snow_col);
  }
  // Rounded drip blobs on shoulders
  end_draw_cloud(45, 81, 7, 4, snow_soft);
  end_draw_cloud(83, 81, 7, 4, snow_soft);
  // Tiny drip tips
  end_draw_cloud(40, 86, 4, 3, snow_col);
  end_draw_cloud(88, 86, 4, 3, snow_col);

  if (show_flag) {
    // Flagpole — muted brownish grey
    uint16_t pole_col = rgb(122,96,88);
    for (int y=56;y<77;y++)
      tft.fillRect(OFFSET_X+72*SCALE, OFFSET_Y+y*SCALE, SCALE, SCALE, pole_col);
    // Pastel red flag — simple triangle
    uint16_t flag_col  = rgb(232,160,160);
    uint16_t flag_dark = rgb(208,136,136);
    for (int i=0;i<9;i++) {
      int fw = 9-i;
      tft.fillRect(OFFSET_X+73*SCALE, OFFSET_Y+(56+i)*SCALE, fw*SCALE, SCALE, flag_col);
    }
    // Stripe detail
    tft.fillRect(OFFSET_X+73*SCALE, OFFSET_Y+59*SCALE, 7*SCALE, SCALE, flag_dark);
  }
}

// Draw the player sprite for end screen directly in screen pixels at 6× scale.
// sx,sy = top-left in raw screen pixel coords.
// ghost=true renders at half brightness (LOSE screen).
static void end_draw_sprite(int sx, int sy, bool ghost) {
  const int SPR_SCALE = 6;
  const uint16_t *pal = (selectedChar==CHAR_MADELINE) ? MADELINE_PAL : BADELINE_PAL;
  uint16_t hair_col;
  if (selectedChar==CHAR_MADELINE)
    hair_col = ghost ? rgb(127,34,34) : MADELINE_HAIR_NORMAL;
  else
    hair_col = ghost ? rgb(77,44,91)  : BADELINE_HAIR_NORMAL;

  // Static hair nodes trailing left from head anchor (pixel 4,3 of sprite)
  int ax = sx + 4*SPR_SCALE;
  int ay = sy + 3*SPR_SCALE;
  for (int i=0;i<5;i++) {
    int sz = (i<3 ? 2 : 1) * SPR_SCALE;
    int hx = ax - i*SPR_SCALE;
    int hy = ay - (i/2)*SPR_SCALE/2;
    uint16_t hc = ghost ? rgb(((hair_col>>11)&0x1F)<<2,
                               ((hair_col>>5)&0x3F)<<1,
                               (hair_col&0x1F)<<2) : hair_col;
    tft.fillRect(hx, hy, sz, sz, hc);
  }

  // Sprite pixels
  for (int row=0;row<8;row++) {
    for (int col=0;col<8;col++) {
      int c = PLAYER_SPR[row][col];
      if (c==0 || !pal[c]) continue;
      uint16_t color = (c==9) ? hair_col : pal[c];
      if (ghost) {
        uint8_t r=((color>>11)&0x1F)>>1;
        uint8_t g=((color>>5 )&0x3F)>>1;
        uint8_t b=( color     &0x1F)>>1;
        color=(r<<11)|(g<<5)|b;
      }
      tft.fillRect(sx+col*SPR_SCALE, sy+row*SPR_SCALE, SPR_SCALE, SPR_SCALE, color);
    }
  }
}

// Bottom stats bar in raw screen pixels
static void end_draw_stats_bar(const char *line1, const char *line2, uint16_t col) {
  tft.fillRect(0, 210, 320, 30, rgb(15,5,25));
  tft.setTextSize(1);
  tft.setTextColor(col);
  tft.drawString(line1, 10, 216);
  tft.drawString(line2, 10, 228);
}

static void draw_end_screen() {
  canvas.fillSprite(PICO_PAL[0]);

  // Background layers
  end_draw_sky(endResult==END_LOSE);
  end_draw_far_mountains();
  end_draw_clouds();

  bool show_flag = (endResult != END_LOSE);
  end_draw_summit(show_flag);

  // Sprite feet land on snow surface (PICO y=77 → screen y = OFFSET_Y+77*SCALE = -8+154 = 146)
  // Sprite is 8 rows × 6px = 48px tall → origin screen y = 146-48 = 98
  // WIN/SOLO: left of flag (flag pole at PICO x=72 → screen x=OFFSET_X+72*SCALE=176)
  //           sprite 8px wide × 6 = 48px, place at screen x=110
  // LOSE: centred on summit → screen x=120
  int sprite_sx = (endResult==END_LOSE) ? 120 : 110;
  int sprite_sy = 98;
  end_draw_sprite(sprite_sx, sprite_sy, endResult==END_LOSE);

  // Result text — drawn in PICO coords
  if (endResult==END_WIN) {
    tft.setTextSize(2);
    pico_print("WIN!", 50, 20, 7);
    tft.setTextSize(1);  // restore default
  } else if (endResult==END_LOSE) {
    tft.setTextSize(2);
    pico_print("LOSE", 48, 20, 13);
    tft.setTextSize(1);
  } else {
    tft.setTextSize(2);
    pico_print("SUMMIT!", 40, 2, 7);
    tft.setTextSize(1);
  }

  // Stats box for solo — drawn in raw screen pixels, right side
  if (endResult==END_SOLO) {
    tft.fillRect(196, 60, 116, 46, rgb(15,5,25));
    tft.drawRect(196, 60, 116, 46, rgb(200,190,200));
    tft.setTextSize(1);
    tft.setTextColor(rgb(255,251,232));
    char tbuf[24]; int h=minutes/60, m=minutes%60;
    sprintf(tbuf,"TIME  %02d:%02d:%02d",h,m,seconds);
    tft.drawString(tbuf, 202, 68);
    char dbuf[16]; sprintf(dbuf,"DEATHS  %d",deaths);
    tft.drawString(dbuf, 202, 82);
    tft.setTextColor(rgb(180,200,220));
    tft.drawString("START->MENU", 202, 96);
  }

  // Stats bar
  char tbuf[32]; int h2=minutes/60, m2=minutes%60;
  if (endResult==END_WIN) {
    char line1[40]; sprintf(line1,"TIME %02d:%02d:%02d   DEATHS %d",h2,m2,seconds,deaths);
    end_draw_stats_bar(line1, "START -> RETURN TO MENU", rgb(255,251,232));
  } else if (endResult==END_LOSE) {
    char line1[40]; sprintf(line1,"TIME %02d:%02d:%02d   DEATHS %d",h2,m2,seconds,deaths);
    end_draw_stats_bar("OPPONENT FINISHED FIRST",
                       "START -> RETURN TO MENU", rgb(200,176,216));
  } else {
    end_draw_stats_bar("", "START -> RETURN TO MENU", rgb(255,251,232));
  }
}

// -------------------------------------------------------
// Main screen input handling
// -------------------------------------------------------
static void update_main_screen(uint32_t raw_cur, uint32_t raw_prv) {
  if (raw_just(BUTTON_Y, raw_cur, raw_prv)) selectedChar = CHAR_MADELINE;
  if (raw_just(BUTTON_A, raw_cur, raw_prv)) selectedChar = CHAR_BADELINE;

  // DEBUG: remove before final build
  if (raw_just(BUTTON_X, raw_cur, raw_prv)) { endResult = END_WIN;  end_frames = 0; gameMode = MODE_END; }
  if (raw_just(BUTTON_B, raw_cur, raw_prv)) { endResult = END_LOSE; end_frames = 0; gameMode = MODE_END; }

  // START -> race if connected, otherwise ignored
  if (raw_just(BUTTON_START, raw_cur, raw_prv)) {
    if (ble_connected) {
      gameMode = MODE_RACE;
      begin_game();
    }
  }

  // SELECT -> solo
  if (raw_just(BUTTON_SELECT, raw_cur, raw_prv)) {
    gameMode = MODE_SOLO;
    begin_game();
  }

  // Client only: attempt connection once when host is found
#ifndef BLE_ROLE_HOST
  static bool connect_attempted = false;
  if (ble_found_device && !ble_connected && !connect_attempted) {
    connect_attempted = true;
    ble_try_connect();
  }
#endif
}

// -------------------------------------------------------
// Arduino entry points
// -------------------------------------------------------
void setup() {
  auto cfg = M5.config();
  M5.begin(cfg);

  canvas.createSprite(320, 240);
  canvas.setTextSize(1);

  if (!gamepad.begin(0x50)) {
    M5.Display.drawString("Gamepad not found!", 10, 10);
    while (1) delay(100);
  }
  gamepad.pinModeBulk(BUTTON_X | BUTTON_Y | BUTTON_A | BUTTON_B | BUTTON_SELECT | BUTTON_START, INPUT_PULLUP);

  srand(millis());
  init_tile_flags_custom();
  init_types();
  init_particles();

  gameMode = MODE_MAIN_SCREEN;
  ble_init_role();  // auto-starts based on role define
}

void loop() {
  M5.update();

  // ---- Read gamepad ----
  btn_prev=btn_held; raw_prev=raw_held;
  uint32_t raw_buttons=~gamepad.digitalReadBulk(BUTTON_X|BUTTON_Y|BUTTON_A|BUTTON_B|BUTTON_SELECT|BUTTON_START);
  raw_held=raw_buttons;

  int jx=1023-gamepad.analogRead(14);
  int jy=1023-gamepad.analogRead(15);

  btn_held=0;
  if (jx>624)                              btn_held|=(1<<K_RIGHT);
  if (jx<400)                              btn_held|=(1<<K_LEFT);
  if (jy>624)                              btn_held|=(1<<K_UP);
  if (jy<400)                              btn_held|=(1<<K_DOWN);
  if (raw_buttons&BUTTON_A||(raw_buttons&BUTTON_X)) btn_held|=(1<<K_JUMP);
  if (raw_buttons&BUTTON_B||(raw_buttons&BUTTON_Y)) btn_held|=(1<<K_DASH);

  // ================================================================
  // MAIN SCREEN MODE
  // ================================================================
  if (gameMode==MODE_MAIN_SCREEN) {
    frames=(frames+1)%30;
    update_main_screen(raw_held, raw_prev);
    draw_main_screen();
    canvas.pushSprite(0,0);
    delay(16);
    return;
  }

  // ================================================================
  // END SCREEN MODE
  // ================================================================
  if (gameMode==MODE_END) {
    end_frames++;
    // START returns to main menu
    if (raw_just(BUTTON_START, raw_held, raw_prev)) {
      gameMode=MODE_MAIN_SCREEN;
      canvas.pushSprite(0,0);
      delay(16);
      return;
    }
    draw_end_screen();
    canvas.pushSprite(0,0);
    delay(16);
    return;
  }

  // ================================================================
  // GAME MODES (SOLO / RACE) — original loop logic preserved exactly
  // ================================================================
  frames=(frames+1)%30;
  if (frames==0 && level_index()<30) {
    seconds=(seconds+1)%60; if (seconds==0) minutes++;
  }
  if (music_timer>0) { music_timer--; if (!music_timer) pico_music(10,0,7); }
  if (sfx_timer>0)   sfx_timer--;
  if (freeze>0)      { freeze--; goto draw_frame; }

  if (shake>0) shake--;
  if (will_restart && delay_restart>0) {
    delay_restart--;
    if (!delay_restart) { will_restart=false; load_room(room.x,room.y); }
  }

  for (int i=0;i<MAX_OBJECTS;i++) {
    if (!objects[i].alive) continue;
    obj_move(&objects[i],objects[i].spd.x,objects[i].spd.y);
    if (objects[i].type->update_fn) objects[i].type->update_fn(&objects[i]);
  }

  if (is_title()) {
    if (!start_game&&(btn(K_JUMP)||btn(K_DASH))) {
      pico_music(-1); start_game_flash=50; start_game=true; pico_sfx(38);
    }
    if (start_game) { start_game_flash--; if (start_game_flash<=-30) begin_game(); }
  }

  // ---- DRAW ----
  draw_frame:
  if (freeze>0) { delay(16); return; }

  int bg_col=flash_bg?frames/5:(new_bg?2:0);
  rectfill(0,0,127,127,bg_col);

  if (!is_title()) {
    for (int i=0;i<MAX_CLOUDS;i++) {
      clouds[i].x+=clouds[i].spd;
      rectfill((int)clouds[i].x,(int)clouds[i].y,
               (int)(clouds[i].x+clouds[i].w),
               (int)(clouds[i].y+4+(1-clouds[i].w/64)*12),
               new_bg?14:1);
      if (clouds[i].x>128) { clouds[i].x=-clouds[i].w; clouds[i].y=pico_rnd(120); }
    }
  }
  map_draw_sprites();


  // Platforms behind
  for (int i=0;i<MAX_OBJECTS;i++) {
    if (!objects[i].alive) continue;
    if (objects[i].type==&T_platform && objects[i].type->draw_fn)
      objects[i].type->draw_fn(&objects[i]);
  }

  // Ghost (race mode, same room)
  if (gameMode==MODE_RACE) draw_ghost();

  // All other objects
  for (int i=0;i<MAX_OBJECTS;i++) {
    if (!objects[i].alive||objects[i].type==&T_platform) continue;
    if (objects[i].type->draw_fn) objects[i].type->draw_fn(&objects[i]);
    else if (objects[i].spr_id>0)
      spr(objects[i].spr_id,objects[i].x,objects[i].y,objects[i].flip_x,objects[i].flip_y);
  }

  // Particles
  for (int i=0;i<MAX_PARTS;i++) {
    particles[i].x+=particles[i].spd;
    particles[i].y+=pico_sin(particles[i].off);
    particles[i].off+=pico_min(0.05f,particles[i].spd/32.0f);
    int s=(int)particles[i].s;
    rectfill((int)particles[i].x,(int)particles[i].y,
             (int)particles[i].x+s,(int)particles[i].y+s,particles[i].c);
    if (particles[i].x>132) { particles[i].x=-4; particles[i].y=pico_rnd(128); }
  }

  // Dead particles
  for (int i=0;i<dead_count;) {
    dead_particles[i].x+=dead_particles[i].spd.x;
    dead_particles[i].y+=dead_particles[i].spd.y;
    dead_particles[i].t--;
    if (dead_particles[i].t<=0) { dead_particles[i]=dead_particles[--dead_count]; continue; }
    int t=(int)dead_particles[i].t;
    rectfill((int)(dead_particles[i].x-t/5),(int)(dead_particles[i].y-t/5),
             (int)(dead_particles[i].x+t/5),(int)(dead_particles[i].y+t/5),14+t%2);
    i++;
  }

  // Screen border
  rectfill(-5,-5,-1,133,0); rectfill(-5,-5,133,-1,0);
  rectfill(-5,128,133,133,0); rectfill(128,-5,133,133,0);

  if (is_title()) {
    pico_print("x+c",58,80,5);
    pico_print("matt thorson",42,96,5);
    pico_print("noel berry",46,102,5);
  }

  canvas.pushSprite(0,0);
  delay(16);
}
