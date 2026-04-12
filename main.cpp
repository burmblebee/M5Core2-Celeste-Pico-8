// ============================================================
//  ~celeste~ for M5Core2 + Adafruit Seesaw Gamepad
//  Translated from PICO-8 Lua by Matt Thorson & Noel Berry
//
//  Dependencies:
//    - M5Unified library
//    - Adafruit_seesaw library
//
//  Wiring: Seesaw gamepad on I2C (SDA=32, SCL=33 on Core2)
//  Compile: Arduino IDE or PlatformIO with M5Core2 board
// ============================================================

#include <M5Unified.h>
#include <Adafruit_seesaw.h>
#include <math.h>

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

// -------------------------------------------------------
// Display: we render to a 128×128 canvas centred on screen
// -------------------------------------------------------
// -------------------------------------------------------
// Display: render 128×128 PICO-8 canvas scaled to fit the
// M5Core2's 320×240 screen.
//
// SCALE 2 → 256×256px canvas
//   OFFSET_X = (320-256)/2 =  32px  (centred horizontally)
//   OFFSET_Y = (240-256)/2 =  -8px  (clips 8px top+bottom)
// The 8px clip is invisible in practice — those rows are
// covered by the black screen-border rectfills in _draw().
//
// Change SCALE to 1 for a tiny 128×128 centred view, or
// leave at 2 for the best full-screen fit.
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

// -------------------------------------------------------
// Globals
// -------------------------------------------------------
Adafruit_seesaw gamepad;
// M5Unified exposes the display via M5.Display (an M5GFX instance)
#define tft M5.Display

// Off-screen canvas for flicker-free rendering
static M5Canvas canvas(&M5.Display);
#undef tft
#define tft canvas

// Button state (current frame)
static uint32_t btn_held  = 0;
static uint32_t btn_prev  = 0;

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
static int  level_index();


struct Vec2f { float x, y; };
struct Vec2i { int   x, y; };
struct Room  { int   x, y; } room = {0, 0};

// -------------------------------------------------------
// Math helpers  (PICO-8 compatibility wrappers)
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
// Tile collision helpers (forward declarations)
// -------------------------------------------------------
static int level_index() { return room.x % 8 + room.y * 8; }
static bool is_title()   { return level_index() == 31; }

// -------------------------------------------------------
// Input helpers
// -------------------------------------------------------
static bool btn(int k)  { return (btn_held >> k) & 1; }
// (btn_p = "was pressed this frame" — use if needed)

// -------------------------------------------------------
// Tilemap — box-rendering test room
//
// Each room is 16×16 tiles (each tile = 8×8 px → 128×128 px).
// '1' = solid ground tile (flag 0 set), '0' = empty.
// This single test room has a floor, two platforms, and walls.
//
// To add more rooms: extend ROOM_DATA with extra 16×16 grids
// and index them by (room.y * 8 + room.x).
// -------------------------------------------------------
#define MAP_W  16
#define MAP_H  16

#define TILE_EMPTY   0
#define TILE_SOLID   1
#define TILE_SPIKE_D 17
#define TILE_SPIKE_U 27
#define TILE_SPIKE_L 43
#define TILE_SPIKE_R 59

// -------------------------------------------------------
// Room data — 3 rooms indexed by level_index() 0,1,2
// Each room's exit gap is centred on columns 6-9 (x=48..79).
// The next room's spawn is placed at the FLOOR directly below
// that gap, so the player lands naturally.
//
// Room 0: simple intro, exit top-centre
// Room 1: tighter, spikes + moving gap approach
// Room 2: harder, requires dash to reach top
// -------------------------------------------------------
static const uint8_t ROOM_DATA[3][MAP_H][MAP_W] = {

  // ── Room 0 (level 0) ────────────────────────────────
  {{1,1,1,1,1,1,0,0,0,0,1,1,1,1,1,1},  // row 0  exit gap cols 6-9
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 1
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 2
   {1,0,0,0,0,0,0,0,0,0,0,0,1,1,0,1},  // row 3  right high ledge
   {1,0,1,1,0,0,0,0,0,0,0,0,0,0,0,1},  // row 4  left high ledge
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 5
   {1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1},  // row 6  centre ledge
   {1,0,0,0,1,1,0,0,0,0,0,0,0,0,0,1},  // row 7  left-mid ledge
   {1,0,0,0,0,0,0,0,0,0,0,1,1,0,0,1},  // row 8  right-mid ledge
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 9
   {1,0,0,1,1,0,0,0,0,0,1,1,0,0,0,1},  // row 10 two low ledges
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 11
   {1,1,1,0,0,0,0,0,0,0,0,0,0,1,1,1},  // row 12 side steps
   {1,0,0,0,0,17,0,0,0,0,27,0,0,0,0,1},// row 13 spikes
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 14
   {1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1}}, // row 15 floor

  // ── Room 1 (level 1) ────────────────────────────────
  // Spawn drops in at floor below gap (cols 6-9 → x≈56, floor row15 → y=112)
  {{1,1,1,1,1,1,0,0,0,0,1,1,1,1,1,1},  // row 0  exit gap cols 6-9
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 1
   {1,0,0,1,1,1,0,0,0,0,0,0,0,0,0,1},  // row 2  left shelf
   {1,0,0,0,0,0,0,0,0,0,0,1,1,1,0,1},  // row 3  right shelf
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 4
   {1,0,0,0,0,0,0,1,1,1,0,0,0,0,0,1},  // row 5  centre shelf
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 6
   {1,0,1,1,0,0,0,0,0,0,0,0,1,1,0,1},  // row 7  two small ledges
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 8
   {1,0,0,0,0,1,1,1,1,1,0,0,0,0,0,1},  // row 9  wide platform
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 10
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 11
   {1,1,1,0,0,0,0,0,0,0,0,0,0,1,1,1},  // row 12 side steps
   {1,0,0,0,17,0,0,0,0,0,0,27,0,0,0,1},// row 13 spikes
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 14
   {1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1}}, // row 15 floor

  // ── Room 2 (level 2) ────────────────────────────────
  // Tighter — requires dash to cross the gap in the middle
  {{1,1,1,1,1,1,0,0,0,0,1,1,1,1,1,1},  // row 0  exit gap cols 6-9
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 1
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 2
   {1,0,1,1,1,0,0,0,0,0,0,1,1,1,0,1},  // row 3  mirrored shelves
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 4
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 5
   {1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,1},  // row 6  gap in middle forces dash
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 7
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 8
   {1,0,1,1,0,0,0,0,0,0,0,0,1,1,0,1},  // row 9  side ledges
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 10
   {1,0,0,0,0,0,1,1,1,1,0,0,0,0,0,1},  // row 11 central platform
   {1,1,1,0,0,17,0,0,0,0,27,0,0,1,1,1},// row 12 spikes on steps
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 13
   {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1},  // row 14
   {1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1}}, // row 15 floor
};

// Tile flag bits per tile id (bit 0 = solid, bit 4 = ice)
static uint8_t tile_flags[256] = {};

static void init_tile_flags() {
  tile_flags[TILE_SOLID]   = (1 << 0);   // solid
  tile_flags[TILE_SPIKE_D] = 0;
  tile_flags[TILE_SPIKE_U] = 0;
  tile_flags[TILE_SPIKE_L] = 0;
  tile_flags[TILE_SPIKE_R] = 0;
  // Add ice tiles here: tile_flags[YOUR_ICE_ID] = (1<<4);
}

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
// Box-based renderer
//
// spr() draws a solid coloured box representing each entity.
// Colour is chosen by sprite ID so different game objects are
// visually distinct without any real sprite data.
//
// Tile colours used in map_draw_boxes():
//   solid ground  → colour 6 (light grey)
//   spike down    → colour 8 (red)
//   spike up      → colour 8
//   spike left/r  → colour 8
// -------------------------------------------------------

// Map PICO-8 sprite IDs to palette colours for box rendering
static int spr_color(int id) {
  if (id ==  1 || id ==  2 || id ==  3 ||
      id ==  4 || id ==  5 || id ==  6 || id == 7)  return 12; // player  → blue
  if (id == 11 || id == 12)                          return  5; // platform → dark grey
  if (id == 18 || id == 19)                          return  9; // spring  → orange
  if (id == 22)                                      return 12; // balloon → blue
  if (id == 23 || id == 24 || id == 25)              return  4; // fall floor → brown
  if (id == 26)                                      return 10; // fruit   → yellow
  if (id == 28)                                      return 10; // fly fruit → yellow
  if (id == 29 || id == 30 || id == 31)              return  6; // smoke   → grey
  if (id ==  8 || id ==  9 || id == 10)              return  9; // key     → orange
  if (id == 20)                                      return  9; // chest   → orange
  if (id == 64 || id == 65 ||
      id == 80 || id == 81)                          return  5; // fake wall → dark grey
  if (id == 96 || id == 97 ||
      id == 112 || id == 113)                        return  7; // big chest → white
  if (id == 102)                                     return  7; // orb     → white
  if (id == 118 || id == 119 || id == 120)           return 11; // flag    → green
  return 7; // default white
}

static void spr(int id, float x, float y,
                bool flip_x = false, bool flip_y = false) {
  (void)flip_x; (void)flip_y;
  int col = spr_color(id);
  // Outer box
  tft.fillRect(OFFSET_X + (int)x * SCALE,
               OFFSET_Y + (int)y * SCALE,
               8 * SCALE, 8 * SCALE,
               PICO_PAL[col & 15]);
  // 1-pixel dark border for readability
  tft.drawRect(OFFSET_X + (int)x * SCALE,
               OFFSET_Y + (int)y * SCALE,
               8 * SCALE, 8 * SCALE,
               PICO_PAL[0]);
}

// Draw the room terrain as coloured boxes (replaces map_draw with sprite blitting)
static void map_draw_boxes() {
  for (int ty = 0; ty < MAP_H; ty++) {
    for (int tx = 0; tx < MAP_W; tx++) {
      uint8_t t = mget(tx, ty);
      int col = -1;
      if (t == TILE_SOLID)                                               col = 6;  // grey
      else if (t == TILE_SPIKE_D || t == TILE_SPIKE_U ||
               t == TILE_SPIKE_L || t == TILE_SPIKE_R)                  col = 8;  // red
      if (col >= 0) {
        tft.fillRect(OFFSET_X + tx * 8 * SCALE,
                     OFFSET_Y + ty * 8 * SCALE,
                     8 * SCALE, 8 * SCALE,
                     PICO_PAL[col]);
        tft.drawRect(OFFSET_X + tx * 8 * SCALE,
                     OFFSET_Y + ty * 8 * SCALE,
                     8 * SCALE, 8 * SCALE,
                     PICO_PAL[0]);
      }
    }
  }
}

// -------------------------------------------------------
// Drawing primitives (PICO-8 → M5GFX)
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
static void pico_print(const char *s, int x, int y, int col) {
  tft.setTextColor(PICO_PAL[col & 15]);
  tft.drawString(s, OFFSET_X + x * SCALE, OFFSET_Y + y * SCALE);
}
static void pico_line(int x0, int y0, int x1, int y1, int col) {
  tft.drawLine(OFFSET_X + x0 * SCALE, OFFSET_Y + y0 * SCALE,
               OFFSET_X + x1 * SCALE, OFFSET_Y + y1 * SCALE,
               PICO_PAL[col & 15]);
}
// map_draw_boxes() declared above replaces the old tile-sheet map_draw()

// -------------------------------------------------------
// Audio stub  (M5Core2 has a speaker, wire in your tones)
// -------------------------------------------------------
static void psfx(int /*num*/) { /* TODO: play tone */ }
static void pico_sfx(int /*num*/) { /* TODO */ }
static void pico_music(int /*track*/, int /*fade*/ = 0,
                       int /*mask*/ = 7) { /* TODO */ }

// -------------------------------------------------------
// Object / entity system
// -------------------------------------------------------
struct HitBox { float x, y, w, h; };

struct Object;

// Type descriptor (equivalent to PICO-8 type tables)
struct ObjectType {
  int   tile        = 0;
  bool  if_not_fruit = false;
  void (*init_fn)  (Object *) = nullptr;
  void (*update_fn)(Object *) = nullptr;
  void (*draw_fn)  (Object *) = nullptr;
};

// -------------------------------------------------------
// Forward-declare all types so Objects can reference them
// -------------------------------------------------------
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
static ObjectType T_chest;
static ObjectType T_platform;
static ObjectType T_message;
static ObjectType T_big_chest;
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

  // --- player fields ---
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

  // --- spawn fields ---
  Vec2f target        = {0, 0};
  int   state         = 0;
  int   delay         = 0;

  // --- spring / misc ---
  int   hide_in       = 0;
  int   hide_for      = 0;
  int   timer         = 0;

  // --- balloon ---
  float offset        = 0;
  float start         = 0;

  // --- platform ---
  float last          = 0;
  int   dir           = 0;

  // --- lifeup ---
  int   duration      = 0;
  float flash         = 0;

  // --- hair (5 nodes) ---
  struct HairNode { float x, y; int size; } hair[5];
  bool  hair_init     = false;

  // --- chest/big_chest ---
  int   score         = 0;
  bool  show          = false;

  // --- sfx_delay for fly_fruit ---
  int   sfx_delay     = 0;
  bool  fly           = false;
  float step          = 0;

  // --- big_chest particles ---
  struct BCP { float x, y, h, spd; } bcp[60];
  int   bcp_count     = 0;
};

static Object objects[MAX_OBJECTS];

static Object *init_object(ObjectType *type, float x, float y);
static void    destroy_object(Object *obj);

// -------------------------------------------------------
// Collision helpers (methods on Object)
// -------------------------------------------------------
static bool obj_is_solid(Object *obj, float ox, float oy);
static bool obj_is_ice(Object *obj, float ox, float oy);

static Object *obj_collide(Object *obj, ObjectType *type,
                           float ox, float oy) {
  for (int i = 0; i < MAX_OBJECTS; i++) {
    Object *other = &objects[i];
    if (!other->alive || other->type != type || other == obj
        || !other->collideable) continue;
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

// -------------------------------------------------------
// Tile collision
// -------------------------------------------------------
static bool tile_flag_at(float x, float y, float w, float h, int flag) {
  for (int i = pico_flr(pico_max(0, x / 8));
       i <= (int)pico_min(15, (x + w - 1) / 8); i++) {
    for (int j = pico_flr(pico_max(0, y / 8));
         j <= (int)pico_min(15, (y + h - 1) / 8); j++) {
      if (fget(mget(i, j), flag))   // <-- remove room.x*16, room.y*16
        return true;
    }
  }
  return false;
}
static bool solid_at(float x, float y, float w, float h) {
  return tile_flag_at(x, y, w, h, 0);
}
static bool ice_at(float x, float y, float w, float h) {
  return tile_flag_at(x, y, w, h, 4);
}
static bool obj_is_solid(Object *obj, float ox, float oy) {
  if (oy > 0 && !obj_check(obj, &T_platform, ox, 0) &&
       obj_check(obj, &T_platform, ox, oy)) return true;
  return solid_at(obj->x + obj->hitbox.x + ox,
                  obj->y + obj->hitbox.y + oy,
                  obj->hitbox.w, obj->hitbox.h)
      || obj_check(obj, &T_fall_floor, ox, oy)
      || obj_check(obj, &T_fake_wall,  ox, oy);
}
static bool obj_is_ice(Object *obj, float ox, float oy) {
  return ice_at(obj->x + obj->hitbox.x + ox,
                obj->y + obj->hitbox.y + oy,
                obj->hitbox.w, obj->hitbox.h);
}

static bool spikes_at(float x, float y, float w, float h,
                      float xspd, float yspd) {
  for (int i = pico_flr(pico_max(0, x / 8));
       i <= (int)pico_min(15, (x + w - 1) / 8); i++) {
    for (int j = pico_flr(pico_max(0, y / 8));
         j <= (int)pico_min(15, (y + h - 1) / 8); j++) {
      uint8_t t = mget(i, j);   // <-- remove room.x*16, room.y*16
      if (t == 17 && ((int)(y + h - 1) % 8 >= 6 || y + h == j * 8 + 8) && yspd >= 0) return true;
      if (t == 27 && (int)y % 8 <= 2 && yspd <= 0) return true;
      if (t == 43 && (int)x % 8 <= 2 && xspd <= 0) return true;
      if (t == 59 && ((int)(x + w - 1) % 8 >= 6 || x + w == i * 8 + 8) && xspd >= 0) return true;
    }
  }
  return false;
}

// -------------------------------------------------------
// Object movement
// -------------------------------------------------------
static void obj_move_x(Object *obj, float amount, int start) {
  if (obj->solids) {
    int step = pico_sign(amount);
    for (int i = start; i <= (int)pico_abs(amount); i++) {
      if (!obj_is_solid(obj, (float)step, 0)) { obj->x += step; }
      else { obj->spd.x = 0; obj->rem.x = 0; break; }
    }
  } else { obj->x += amount; }
}
static void obj_move_y(Object *obj, float amount) {
  if (obj->solids) {
    int step = pico_sign(amount);
    for (int i = 0; i <= (int)pico_abs(amount); i++) {
      if (!obj_is_solid(obj, 0, (float)step)) { obj->y += step; }
      else { obj->spd.y = 0; obj->rem.y = 0; break; }
    }
  } else { obj->y += amount; }
}
static void obj_move(Object *obj, float ox, float oy) {
  obj->rem.x += ox;
  int ax = pico_flr(obj->rem.x + 0.5f);
  obj->rem.x -= ax;
  obj_move_x(obj, (float)ax, 0);

  obj->rem.y += oy;
  int ay = pico_flr(obj->rem.y + 0.5f);
  obj->rem.y -= ay;
  obj_move_y(obj, (float)ay);
}

// -------------------------------------------------------
// Hair
// -------------------------------------------------------
static void create_hair(Object *obj) {
  for (int i = 0; i < 5; i++) {
    obj->hair[i] = {obj->x, obj->y,
                    (int)pico_max(1, pico_min(2, (float)(3 - i)))};
  }
  obj->hair_init = true;
}
static void draw_hair(Object *obj, int facing) {
  float lx = obj->x + 4 - facing * 2;
  float ly = obj->y + (btn(K_DOWN) ? 4.0f : 3.0f);
  for (int i = 0; i < 5; i++) {
    obj->hair[i].x += (lx - obj->hair[i].x) / 1.5f;
    obj->hair[i].y += (ly + 0.5f - obj->hair[i].y) / 1.5f;
    circfill(obj->hair[i].x, obj->hair[i].y, obj->hair[i].size, 8);
    lx = obj->hair[i].x;
    ly = obj->hair[i].y;
  }
}

// -------------------------------------------------------
// Particle systems (global arrays)
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

static void init_particles() {
  for (int i = 0; i < MAX_CLOUDS; i++)
    clouds[i] = {pico_rnd(128), pico_rnd(128), 1 + pico_rnd(4), 32 + pico_rnd(32)};
  for (int i = 0; i < MAX_PARTS; i++)
    particles[i] = {pico_rnd(128), pico_rnd(128),
                    (float)pico_flr(pico_rnd(5) / 4),
                    0.25f + pico_rnd(5),
                    pico_rnd(1),
                    6 + pico_flr(0.5f + pico_rnd(1))};
}

// -------------------------------------------------------
// Forward declarations for game functions
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
  t->p_jump = false; t->p_dash = false;
  t->grace  = 0;     t->jbuffer = 0;
  t->djump  = max_djump;
  t->dash_time = 0;  t->dash_effect_time = 0;
  t->dash_target = {0, 0}; t->dash_accel = {0, 0};
  t->hitbox = {1, 3, 6, 5};
  t->spr_off = 0; t->was_on_ground = false;
  create_hair(t);
}

static void player_update(Object *t) {
  if (pause_player) return;
  float input = btn(K_RIGHT) ? 1.0f : (btn(K_LEFT) ? -1.0f : 0.0f);

  if (spikes_at(t->x + t->hitbox.x, t->y + t->hitbox.y,
                t->hitbox.w, t->hitbox.h, t->spd.x, t->spd.y))
    kill_player(t);
  if (t->y > 128) kill_player(t);

  bool on_ground = obj_is_solid(t, 0, 1);
  bool on_ice    = obj_is_ice(t, 0, 1);

  if (on_ground && !t->was_on_ground)
    init_object(&T_smoke, t->x, t->y + 4);

  bool jump = btn(K_JUMP) && !t->p_jump;
  t->p_jump = btn(K_JUMP);
  if (jump)        t->jbuffer = 4;
  else if (t->jbuffer > 0) t->jbuffer--;

  bool dash = btn(K_DASH) && !t->p_dash;
  t->p_dash = btn(K_DASH);

  if (on_ground) {
    t->grace = 6;
    if (t->djump < max_djump) { psfx(54); t->djump = max_djump; }
  } else if (t->grace > 0) t->grace--;

  t->dash_effect_time--;
  if (t->dash_time > 0) {
    init_object(&T_smoke, t->x, t->y);
    t->dash_time--;
    t->spd.x = pico_appr(t->spd.x, t->dash_target.x, t->dash_accel.x);
    t->spd.y = pico_appr(t->spd.y, t->dash_target.y, t->dash_accel.y);
  } else {
    float maxrun = 1.0f, accel = 0.6f, deccel = 0.15f;
    if (!on_ground)        accel = 0.4f;
    else if (on_ice)       accel = 0.05f;

    if (pico_abs(t->spd.x) > maxrun)
      t->spd.x = pico_appr(t->spd.x, pico_sign(t->spd.x) * maxrun, deccel);
    else
      t->spd.x = pico_appr(t->spd.x, input * maxrun, accel);

    if (t->spd.x != 0) t->flip_x = (t->spd.x < 0);

    float maxfall = 2.0f, gravity = 0.21f;
    if (pico_abs(t->spd.y) <= 0.15f) gravity *= 0.5f;

    if (input != 0 && obj_is_solid(t, (int)input, 0) &&
        !obj_is_ice(t, (int)input, 0)) {
      maxfall = 0.4f;
      if (pico_rnd(10) < 2)
        init_object(&T_smoke, t->x + input * 6, t->y);
    }
    if (!on_ground) t->spd.y = pico_appr(t->spd.y, maxfall, gravity);

    // jump
    if (t->jbuffer > 0) {
      if (t->grace > 0) {
        psfx(1); t->jbuffer = 0; t->grace = 0; t->spd.y = -2;
        init_object(&T_smoke, t->x, t->y + 4);
      } else {
        int wd = (obj_is_solid(t, -3, 0) ? -1 :
                  obj_is_solid(t,  3, 0) ?  1 : 0);
        if (wd != 0) {
          psfx(2); t->jbuffer = 0; t->spd.y = -2;
          t->spd.x = -wd * (maxrun + 1);
          if (!obj_is_ice(t, wd * 3, 0))
            init_object(&T_smoke, t->x + wd * 6, t->y);
        }
      }
    }

    // dash
    float d_full = 5.0f, d_half = d_full * 0.70710678118f;
    if (t->djump > 0 && dash) {
      init_object(&T_smoke, t->x, t->y);
      t->djump--; t->dash_time = 4; has_dashed = true;
      t->dash_effect_time = 10;
      float v_input = btn(K_UP) ? -1.0f : (btn(K_DOWN) ? 1.0f : 0.0f);
      if (input != 0) {
        if (v_input != 0) { t->spd.x = input * d_half; t->spd.y = v_input * d_half; }
        else              { t->spd.x = input * d_full; t->spd.y = 0; }
      } else if (v_input != 0) { t->spd.x = 0; t->spd.y = v_input * d_full; }
      else                     { t->spd.x = t->flip_x ? -1.0f : 1.0f; t->spd.y = 0; }

      psfx(3); freeze = 2; shake = 6;
      t->dash_target = {2.0f * pico_sign(t->spd.x), 2.0f * pico_sign(t->spd.y)};
      t->dash_accel  = {1.5f, 1.5f};
      if (t->spd.y < 0) t->dash_target.y *= 0.75f;
      if (t->spd.y != 0) t->dash_accel.x *= 0.70710678118f;
      if (t->spd.x != 0) t->dash_accel.y *= 0.70710678118f;
    } else if (dash && t->djump <= 0) {
      psfx(9); init_object(&T_smoke, t->x, t->y);
    }
  }

  // animation
  t->spr_off += 0.25f;
  if (!on_ground) {
    t->spr_id = obj_is_solid(t, (int)input, 0) ? 5 : 3;
  } else if (btn(K_DOWN)) { t->spr_id = 6; }
  else if (btn(K_UP))   { t->spr_id = 7; }
  else if (t->spd.x == 0 || (!btn(K_LEFT) && !btn(K_RIGHT))) { t->spr_id = 1; }
  else                  { t->spr_id = 1 + (int)t->spr_off % 4; }

  if (t->y < -4 && level_index() < 30) next_room();
  t->was_on_ground = on_ground;
}

static void player_draw(Object *t) {
  if (t->x < -1 || t->x > 121) {
    t->x = pico_clamp(t->x, -1, 121); t->spd.x = 0;
  }
  // set hair color based on djump
  draw_hair(t, t->flip_x ? -1 : 1);
  spr(t->spr_id, t->x, t->y, t->flip_x, t->flip_y);
}

// -------------------------------------------------------
// Player spawn type
// -------------------------------------------------------
static void player_spawn_init(Object *t) {
  pico_sfx(4);
  t->spr_id = 3;
  t->target = {t->x, t->y};
  t->y = 128; t->spd.y = -4;
  t->state = 0; t->delay = 0; t->solids = false;
  create_hair(t);
}
static void player_spawn_update(Object *t) {
  if (t->state == 0) {
    if (t->y < t->target.y + 16) { t->state = 1; t->delay = 3; }
  } else if (t->state == 1) {
    t->spd.y += 0.5f;
    if (t->spd.y > 0 && t->delay > 0) { t->spd.y = 0; t->delay--; }
    if (t->spd.y > 0 && t->y > t->target.y) {
      t->y = t->target.y; t->spd = {0, 0};
      t->state = 2; t->delay = 5; shake = 5;
      init_object(&T_smoke, t->x, t->y + 4); pico_sfx(5);
    }
  } else if (t->state == 2) {
    t->delay--; t->spr_id = 6;
    if (t->delay < 0) {
      destroy_object(t);
      init_object(&T_player, t->x, t->y);
    }
  }
}
static void player_spawn_draw(Object *t) {
  draw_hair(t, 1);
  spr(t->spr_id, t->x, t->y, t->flip_x, t->flip_y);
}

// -------------------------------------------------------
// Spring type
// -------------------------------------------------------
static void spring_init(Object *t) { t->hide_in = 0; t->hide_for = 0; }
static void spring_update(Object *t) {
  if (t->hide_for > 0) {
    t->hide_for--;
    if (t->hide_for <= 0) { t->spr_id = 18; t->delay = 0; }
  } else if (t->spr_id == 18) {
    Object *hit = obj_collide(t, &T_player, 0, 0);
    if (hit && hit->spd.y >= 0) {
      t->spr_id = 19;
      hit->y = t->y - 4; hit->spd.x *= 0.2f; hit->spd.y = -3;
      hit->djump = max_djump; t->delay = 10;
      init_object(&T_smoke, t->x, t->y);
      Object *below = obj_collide(t, &T_fall_floor, 0, 1);
      if (below) break_fall_floor(below);
      psfx(8);
    }
  } else if (t->delay > 0) {
    t->delay--;
    if (t->delay <= 0) t->spr_id = 18;
  }
  if (t->hide_in > 0) {
    t->hide_in--;
    if (t->hide_in <= 0) { t->hide_for = 60; t->spr_id = 0; }
  }
}
static void break_spring(Object *obj) { obj->hide_in = 15; }

// -------------------------------------------------------
// Fall floor type
// -------------------------------------------------------
static void fall_floor_init(Object *t) { t->state = 0; t->solids = true; }
static void fall_floor_update(Object *t) {
  if (t->state == 0) {
    if (obj_check(t, &T_player, 0, -1) ||
        obj_check(t, &T_player, -1,  0) ||
        obj_check(t, &T_player,  1,  0))
      break_fall_floor(t);
  } else if (t->state == 1) {
    t->delay--;
    if (t->delay <= 0) { t->state = 2; t->delay = 60; t->collideable = false; }
  } else if (t->state == 2) {
    t->delay--;
    if (t->delay <= 0 && !obj_check(t, &T_player, 0, 0)) {
      psfx(7); t->state = 0; t->collideable = true;
      init_object(&T_smoke, t->x, t->y);
    }
  }
}
static void fall_floor_draw(Object *t) {
  if (t->state != 2)
    spr(t->state != 1 ? 23 : 23 + (15 - t->delay) / 5, t->x, t->y);
}
static void break_fall_floor(Object *obj) {
  if (obj->state == 0) {
    psfx(15); obj->state = 1; obj->delay = 15;
    init_object(&T_smoke, obj->x, obj->y);
    Object *hit = obj_collide(obj, &T_spring, 0, -1);
    if (hit) break_spring(hit);
  }
}

// -------------------------------------------------------
// Smoke type
// -------------------------------------------------------
static void smoke_init(Object *t) {
  t->spr_id = 29; t->spd.y = -0.1f;
  t->spd.x = 0.3f + pico_rnd(0.2f);
  t->x += -1 + pico_rnd(2); t->y += -1 + pico_rnd(2);
  t->flip_x = pico_maybe(); t->flip_y = pico_maybe();
  t->solids = false;
}
static void smoke_update(Object *t) {
  t->spr_off += 0.2f;
  if (t->spr_off >= 3.0f) destroy_object(t);   // spr 29..31
  t->spr_id = 29 + (int)t->spr_off;
}

// -------------------------------------------------------
// Fruit type
// -------------------------------------------------------
static void fruit_init(Object *t) { t->start = t->y; t->spr_off = 0; }
static void fruit_update(Object *t) {
  Object *hit = obj_collide(t, &T_player, 0, 0);
  if (hit) {
    hit->djump = max_djump; sfx_timer = 20; pico_sfx(13);
    got_fruit[level_index()] = true;
    init_object(&T_lifeup, t->x, t->y);
    destroy_object(t); return;
  }
  t->spr_off += 1;
  t->y = t->start + pico_sin(t->spr_off / 40.0f) * 2.5f;
}

// -------------------------------------------------------
// Lifeup type
// -------------------------------------------------------
static void lifeup_init(Object *t) {
  t->spd.y = -0.25f; t->duration = 30;
  t->x -= 2; t->y -= 4; t->flash = 0; t->solids = false;
}
static void lifeup_update(Object *t) {
  t->duration--;
  if (t->duration <= 0) destroy_object(t);
}
static void lifeup_draw(Object *t) {
  t->flash += 0.5f;
  pico_print("1000", (int)t->x - 2, (int)t->y, 7 + (int)t->flash % 2);
}

// -------------------------------------------------------
// Balloon type
// -------------------------------------------------------
static void balloon_init(Object *t) {
  t->offset = pico_rnd(1); t->start = t->y; t->timer = 0;
  t->hitbox = {-1, -1, 10, 10};
}
static void balloon_update(Object *t) {
  if (t->spr_id == 22) {
    t->offset += 0.01f;
    t->y = t->start + pico_sin(t->offset) * 2;
    Object *hit = obj_collide(t, &T_player, 0, 0);
    if (hit && hit->djump < max_djump) {
      psfx(6); init_object(&T_smoke, t->x, t->y);
      hit->djump = max_djump; t->spr_id = 0; t->timer = 60;
    }
  } else if (t->timer > 0) { t->timer--; }
  else { psfx(7); init_object(&T_smoke, t->x, t->y); t->spr_id = 22; }
}
static void balloon_draw(Object *t) {
  if (t->spr_id == 22) {
    spr(13 + (int)(t->offset * 8) % 3, t->x, t->y + 6);
    spr(t->spr_id, t->x, t->y);
  }
}

// -------------------------------------------------------
// Fake wall type
// -------------------------------------------------------
static void fake_wall_update(Object *t) {
  t->hitbox = {-1, -1, 18, 18};
  Object *hit = obj_collide(t, &T_player, 0, 0);
  if (hit && hit->dash_effect_time > 0) {
    hit->spd.x = -pico_sign(hit->spd.x) * 1.5f;
    hit->spd.y = -1.5f; hit->dash_time = -1;
    sfx_timer = 20; pico_sfx(16); destroy_object(t);
    init_object(&T_smoke, t->x,     t->y    );
    init_object(&T_smoke, t->x + 8, t->y    );
    init_object(&T_smoke, t->x,     t->y + 8);
    init_object(&T_smoke, t->x + 8, t->y + 8);
    init_object(&T_fruit, t->x + 4, t->y + 4);
  }
  t->hitbox = {0, 0, 16, 16};
}
static void fake_wall_draw(Object *t) {
  spr(64, t->x,     t->y    );
  spr(65, t->x + 8, t->y    );
  spr(80, t->x,     t->y + 8);
  spr(81, t->x + 8, t->y + 8);
}

// -------------------------------------------------------
// Key type
// -------------------------------------------------------
static void key_update(Object *t) {
  int was = pico_flr(t->spr_off);
  t->spr_off = 9 + (pico_sin((float)frames / 30.0f) + 0.5f) * 1.0f;
  int is = pico_flr(t->spr_off);
  if (is == 10 && is != was) t->flip_x = !t->flip_x;
  t->spr_id = (int)t->spr_off;
  if (obj_check(t, &T_player, 0, 0)) {
    pico_sfx(23); sfx_timer = 10; destroy_object(t); has_key = true;
  }
}

// -------------------------------------------------------
// Chest type
// -------------------------------------------------------
static void chest_init(Object *t) {
  t->x -= 4; t->start = t->x; t->timer = 20;
}
static void chest_update(Object *t) {
  if (has_key) {
    t->timer--;
    t->x = t->start - 1 + pico_rnd(3);
    if (t->timer <= 0) {
      sfx_timer = 20; pico_sfx(16);
      init_object(&T_fruit, t->x, t->y - 4);
      destroy_object(t);
    }
  }
}

// -------------------------------------------------------
// Platform type
// -------------------------------------------------------
static void platform_init(Object *t) {
  t->x -= 4; t->solids = false;
  t->hitbox.w = 16; t->last = t->x;
}
static void platform_update(Object *t) {
  t->spd.x = t->dir * 0.65f;
  if (t->x < -16) t->x = 128;
  else if (t->x > 128) t->x = -16;
  if (!obj_check(t, &T_player, 0, 0)) {
    Object *hit = obj_collide(t, &T_player, 0, -1);
    if (hit) obj_move_x(hit, t->x - t->last, 1);
  }
  t->last = t->x;
}
static void platform_draw(Object *t) {
  spr(11, t->x,     t->y - 1);
  spr(12, t->x + 8, t->y - 1);
}

// -------------------------------------------------------
// Flag type
// -------------------------------------------------------
static void flag_init(Object *t) {
  t->x += 5; t->score = 0; t->show = false;
  for (int i = 0; i < 30; i++) if (got_fruit[i]) t->score++;
}
static void flag_draw(Object *t) {
  t->spr_id = 118 + (frames / 5) % 3;
  spr(t->spr_id, t->x, t->y);
  if (t->show) {
    rectfill(32, 2, 96, 31, 0);
    spr(26, 55, 6);
    char buf[16]; sprintf(buf, "x%d", t->score);
    pico_print(buf, 64, 9, 7);
    // draw_time(49,16) — inline here
    char tbuf[16];
    int h = minutes / 60, m = minutes % 60;
    sprintf(tbuf, "%02d:%02d:%02d", h, m, seconds);
    rectfill(49, 16, 49 + 32, 16 + 6, 0);
    pico_print(tbuf, 50, 17, 7);
    char dbuf[24]; sprintf(dbuf, "deaths:%d", deaths);
    pico_print(dbuf, 48, 24, 7);
  } else if (obj_check(t, &T_player, 0, 0)) {
    pico_sfx(55); sfx_timer = 30; t->show = true;
  }
}

// -------------------------------------------------------
// Room title type
// -------------------------------------------------------
static void room_title_init(Object *t) { t->delay = 5; }
static void room_title_draw(Object *t) {
  t->delay--;
  if (t->delay < -30) { destroy_object(t); return; }
  if (t->delay < 0) {
    rectfill(24, 58, 104, 70, 0);
    if (room.x == 3 && room.y == 1)     pico_print("old site", 48, 62, 7);
    else if (level_index() == 30)        pico_print("summit",   52, 62, 7);
    else {
      int level = (1 + level_index()) * 100;
      char buf[12]; sprintf(buf, "%d m", level);
      pico_print(buf, 52 + (level < 1000 ? 2 : 0), 62, 7);
    }
    // draw_time(4,4)
    char tbuf[16];
    int h = minutes / 60, m2 = minutes % 60;
    sprintf(tbuf, "%02d:%02d:%02d", h, m2, seconds);
    rectfill(4, 4, 36, 10, 0);
    pico_print(tbuf, 5, 5, 7);
  }
}

// -------------------------------------------------------
// Object type descriptors
// -------------------------------------------------------
static void set_type(ObjectType &t, int tile, bool if_not_fruit,
                     void(*init_fn)(Object*),
                     void(*update_fn)(Object*),
                     void(*draw_fn)(Object*)) {
  t.tile         = tile;
  t.if_not_fruit = if_not_fruit;
  t.init_fn      = init_fn;
  t.update_fn    = update_fn;
  t.draw_fn      = draw_fn;
}

static void init_types() {
  set_type(T_player,       0,   false, player_init,       player_update,       player_draw      );
  set_type(T_player_spawn, 255, false, player_spawn_init, player_spawn_update, player_spawn_draw); // 255 = never in map
  set_type(T_spring,       18,  false, spring_init,       spring_update,       nullptr          );
  set_type(T_balloon,      22,  false, balloon_init,      balloon_update,      balloon_draw     );
  set_type(T_fall_floor,   23,  false, fall_floor_init,   fall_floor_update,   fall_floor_draw  );
  set_type(T_smoke,        0,   false, smoke_init,        smoke_update,        nullptr          );
  set_type(T_fruit,        26,  true,  fruit_init,        fruit_update,        nullptr          );
  set_type(T_lifeup,       0,   false, lifeup_init,       lifeup_update,       lifeup_draw      );
  set_type(T_fake_wall,    64,  true,  nullptr,           fake_wall_update,    fake_wall_draw   );
  set_type(T_key,          8,   true,  nullptr,           key_update,          nullptr          );
  set_type(T_chest,        20,  true,  chest_init,        chest_update,        nullptr          );
  set_type(T_platform,     11,  false, platform_init,     platform_update,     platform_draw    );
  set_type(T_room_title,   0,   false, room_title_init,   nullptr,             room_title_draw  );
  set_type(T_flag,         118, false, flag_init,         nullptr,             flag_draw        );
}

// -------------------------------------------------------
// Object pool management
// -------------------------------------------------------
static Object *init_object(ObjectType *type, float x, float y) {
  if (type->if_not_fruit && got_fruit[level_index()]) return nullptr;
  for (int i = 0; i < MAX_OBJECTS; i++) {
    if (!objects[i].alive) {
      objects[i] = {};           // zero-initialise
      objects[i].alive       = true;
      objects[i].type        = type;
      objects[i].collideable = true;
      objects[i].solids      = true;
      objects[i].spr_id      = type->tile;
      objects[i].x = x; objects[i].y = y;
      objects[i].hitbox = {0, 0, 8, 8};
      if (type->init_fn) type->init_fn(&objects[i]);
      return &objects[i];
    }
  }
  return nullptr;  // pool full
}
static void destroy_object(Object *obj) {
  if (obj) obj->alive = false;
}

// -------------------------------------------------------
// Kill player
// -------------------------------------------------------
static void kill_player(Object *obj) {
  sfx_timer = 12; pico_sfx(0); deaths++; shake = 10;
  dead_count = 0;
  for (int dir = 0; dir < 8; dir++) {
    if (dead_count >= MAX_DEAD) break;
    float angle = dir / 8.0f;
    dead_particles[dead_count++] = {
      obj->x + 4, obj->y + 4, 10,
      {pico_sin(angle) * 3, pico_cos(angle) * 3}
    };
  }
  destroy_object(obj);
  restart_room();
}

// -------------------------------------------------------
// Room loading
// -------------------------------------------------------
static void restart_room() { will_restart = true; delay_restart = 15; }

static void next_room() {
  int next = level_index() + 1;
  if (next >= 3) next = 0;   // loop back or handle end
  load_room(next % 8, next / 8);
}

static ObjectType *all_types[] = {
  &T_player_spawn, &T_spring, &T_balloon, &T_fall_floor,
  &T_fruit, &T_fake_wall, &T_key, &T_chest, &T_flag
};
static const int NUM_TYPES = sizeof(all_types) / sizeof(all_types[0]);

static void load_room(int x, int y) {
  has_dashed = false; has_key = false;
  for (int i = 0; i < MAX_OBJECTS; i++) objects[i].alive = false;
  room.x = x; room.y = y;

  for (int tx = 0; tx < 16; tx++) {
    for (int ty = 0; ty < 16; ty++) {
      uint8_t tile = mget(tx, ty);
      if (tile == 11) { auto *p = init_object(&T_platform, tx*8, ty*8); if(p) p->dir = -1; }
      else if (tile == 12) { auto *p = init_object(&T_platform, tx*8, ty*8); if(p) p->dir = 1; }
      else {
        for (int k = 0; k < NUM_TYPES; k++)
          if (all_types[k]->tile == tile)
            init_object(all_types[k], tx * 8, ty * 8);
      }
    }
  }
  if (!is_title()) init_object(&T_room_title, 0, 0);

  // Spawn at the floor below the exit gap (col 7 = x 56, floor = y 112)
  // Room 0 is the exception — spawn at left side near floor as intro
  int spawnX = (level_index() == 0) ? 16 : 56;
  int spawnY = 112;
  init_object(&T_player_spawn, spawnX, spawnY);
}

// -------------------------------------------------------
// Title / begin game
// -------------------------------------------------------
static void title_screen() {
  for (int i = 0; i < 30; i++) got_fruit[i] = false;
  frames = 0; deaths = 0; max_djump = 1;
  start_game = false; start_game_flash = 0;
  pico_music(40, 0, 7);
  load_room(7, 3);
}
static void begin_game() {
  frames = 0; seconds = 0; minutes = 0;
  music_timer = 0; start_game = false;
  pico_music(0, 0, 7);
  load_room(0, 0);
}

// -------------------------------------------------------
// Arduino entry points
// -------------------------------------------------------
void setup() {
  auto cfg = M5.config();
  M5.begin(cfg);

  canvas.createSprite(320, 240);
  canvas.setTextSize(1);

  // Init seesaw gamepad (default I2C addr 0x50)
  if (!gamepad.begin(0x50)) {
    M5.Display.drawString("Gamepad not found!", 10, 10);
    while (1) delay(100);
  }
  gamepad.pinModeBulk(
    BUTTON_X | BUTTON_Y | BUTTON_A | BUTTON_B |
    BUTTON_SELECT | BUTTON_START, INPUT_PULLUP);

  // In setup(), after gamepad.begin():
  M5.Display.drawString("Press A or B to start", 20, 120);

  srand(millis());
  init_tile_flags();
  init_types();
  init_particles();
  title_screen();
}

void loop() {
  M5.update();   // required by M5Unified each frame

  // ---- Read gamepad ----
  btn_prev = btn_held;
  uint32_t raw = ~gamepad.digitalReadBulk(
    BUTTON_X | BUTTON_Y | BUTTON_A | BUTTON_B |
    BUTTON_SELECT | BUTTON_START);

  // Analog stick (512 = centre)
  int jx = 1023 - gamepad.analogRead(14);
  int jy = 1023 - gamepad.analogRead(15);

  btn_held = 0;
  if (jx > 624)                             btn_held |= (1 << K_RIGHT);
  if (jx < 400)                             btn_held |= (1 << K_LEFT);
  if (jy > 624)                             btn_held |= (1 << K_UP);
  if (jy < 400)                             btn_held |= (1 << K_DOWN);
  if (raw & BUTTON_A || (raw & BUTTON_X))   btn_held |= (1 << K_JUMP);
  if (raw & BUTTON_B || (raw & BUTTON_Y))   btn_held |= (1 << K_DASH);

  // ---- UPDATE ----
  frames = (frames + 1) % 30;
  if (frames == 0 && level_index() < 30) {
    seconds = (seconds + 1) % 60;
    if (seconds == 0) minutes++;
  }
  if (music_timer > 0) { music_timer--; if (!music_timer) pico_music(10, 0, 7); }
  if (sfx_timer > 0)   sfx_timer--;
  if (freeze > 0)      { freeze--; goto draw_frame; }

  if (shake > 0) shake--;
  if (will_restart && delay_restart > 0) {
    delay_restart--;
    if (!delay_restart) { will_restart = false; load_room(room.x, room.y); }
  }

  for (int i = 0; i < MAX_OBJECTS; i++) {
    if (!objects[i].alive) continue;
    obj_move(&objects[i], objects[i].spd.x, objects[i].spd.y);
    if (objects[i].type->update_fn) objects[i].type->update_fn(&objects[i]);
  }

  if (is_title()) {
    if (!start_game && (btn(K_JUMP) || btn(K_DASH))) {
      pico_music(-1); start_game_flash = 50; start_game = true; pico_sfx(38);
    }
    if (start_game) { start_game_flash--; if (start_game_flash <= -30) begin_game(); }
  }

  // ---- DRAW ----
  draw_frame:
  if (freeze > 0) { delay(16); return; }

  int bg_col = flash_bg ? frames / 5 : (new_bg ? 2 : 0);
  rectfill(0, 0, 127, 127, bg_col);

  // Clouds
  if (!is_title()) {
    for (int i = 0; i < MAX_CLOUDS; i++) {
      clouds[i].x += clouds[i].spd;
      rectfill((int)clouds[i].x, (int)clouds[i].y,
               (int)(clouds[i].x + clouds[i].w),
               (int)(clouds[i].y + 4 + (1 - clouds[i].w / 64) * 12),
               new_bg ? 14 : 1);
      if (clouds[i].x > 128) { clouds[i].x = -clouds[i].w; clouds[i].y = pico_rnd(120); }
    }
  }

  map_draw_boxes();   // draw all solid/spike tiles as coloured boxes

  // platforms first (drawn behind other entities)
  for (int i = 0; i < MAX_OBJECTS; i++) {
    if (!objects[i].alive) continue;
    if (objects[i].type == &T_platform) {
      if (objects[i].type->draw_fn) objects[i].type->draw_fn(&objects[i]);
    }
  }

  // all other objects
  for (int i = 0; i < MAX_OBJECTS; i++) {
    if (!objects[i].alive || objects[i].type == &T_platform) continue;
    if (objects[i].type->draw_fn) objects[i].type->draw_fn(&objects[i]);
    else if (objects[i].spr_id > 0)
      spr(objects[i].spr_id, objects[i].x, objects[i].y,
          objects[i].flip_x, objects[i].flip_y);
  }

  // Particles
  for (int i = 0; i < MAX_PARTS; i++) {
    particles[i].x += particles[i].spd;
    particles[i].y += pico_sin(particles[i].off);
    particles[i].off += pico_min(0.05f, particles[i].spd / 32.0f);
    int s = (int)particles[i].s;
    rectfill((int)particles[i].x, (int)particles[i].y,
             (int)particles[i].x + s, (int)particles[i].y + s,
             particles[i].c);
    if (particles[i].x > 132) { particles[i].x = -4; particles[i].y = pico_rnd(128); }
  }

  // Dead particles
  for (int i = 0; i < dead_count; ) {
    dead_particles[i].x += dead_particles[i].spd.x;
    dead_particles[i].y += dead_particles[i].spd.y;
    dead_particles[i].t--;
    if (dead_particles[i].t <= 0) {
      dead_particles[i] = dead_particles[--dead_count]; continue;
    }
    int t = (int)dead_particles[i].t;
    rectfill((int)(dead_particles[i].x - t/5), (int)(dead_particles[i].y - t/5),
             (int)(dead_particles[i].x + t/5), (int)(dead_particles[i].y + t/5),
             14 + t % 2);
    i++;
  }

  // Screen border (screenshake mask)
  rectfill(-5, -5, -1, 133, 0);
  rectfill(-5, -5, 133, -1,  0);
  rectfill(-5, 128, 133, 133, 0);
  rectfill(128, -5, 133, 133, 0);

  if (is_title()) {
    pico_print("x+c",          58, 80,  5);
    pico_print("matt thorson", 42, 96,  5);
    pico_print("noel berry",   46, 102, 5);
  }

  canvas.pushSprite(0, 0);
  delay(16);  // ~60 fps cap
}