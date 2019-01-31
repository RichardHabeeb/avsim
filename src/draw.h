#pragma once
#include <road.h>

void setup_draw(road_t *, uint32_t num_roads);
void cleanup_draw(void);
void draw(road_t *, uint32_t num_roads);

#define DRAW_SCALE_MAX    (0xFF)
#define DRAW_ROTATION_MAX (0xFFFF)

void set_draw_scale(SDL_Point s);
void set_draw_rotation(uint16_t r);
void set_draw_translation(SDL_Point s);

SDL_Point   get_draw_scale();
uint16_t    get_draw_rotation();
SDL_Point   get_draw_translation();
