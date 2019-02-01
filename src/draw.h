#pragma once

#include <sim.h>
#include <road.h>
#include <SDL2/SDL.h>

typedef struct vis {
    SDL_Window *window;
    SDL_Renderer *rend;
    SDL_Texture *world_tex;
    SDL_Texture **road_tex;
    SDL_Rect *road_dim;
    SDL_Rect view;
    float view_angle;
} vis_t;

void setup_draw(vis_t *, sim_t *);
void cleanup_draw(vis_t *);
void draw(vis_t *, sim_t *);

void map_point_to_drawn_object(vis_t *, sim_t *, SDL_Point, car_t **, road_t **); 

#define DRAW_SCALE_MAX    (0xFF)
#define DRAW_ROTATION_MAX (0xFFFF)

void set_draw_scale(vis_t *vis, SDL_Point s);
void set_draw_rotation(vis_t *, uint16_t r);
void set_draw_translation(vis_t *, SDL_Point s);

SDL_Point   get_draw_scale(vis_t *);
uint16_t    get_draw_rotation(vis_t *);
SDL_Point   get_draw_translation(vis_t *);
