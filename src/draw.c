#include <stdio.h>
#include <stdint.h>
#include <SDL2/SDL.h>

#include <config.h>
#include <draw.h>
#include <road.h>
#include <car.h>

static SDL_Window *window = NULL;
static SDL_Renderer *renderer = NULL;

void setup_draw(void) {
    if(SDL_Init(SDL_INIT_VIDEO) < 0) {
        //TODO error
    }

    window = SDL_CreateWindow(
            "Autonomous Car Simulator",
            SDL_WINDOWPOS_UNDEFINED,
            SDL_WINDOWPOS_UNDEFINED,
            WINDOW_SIZE_X,
            WINDOW_SIZE_Y,
            SDL_WINDOW_SHOWN);
    if(window == NULL) {
        //TODO error
    }

    renderer = SDL_CreateRenderer(window, -1, SDL_RENDERER_ACCELERATED);
    if(renderer == NULL) {
        //TODO error
    }
    SDL_SetRenderDrawBlendMode(renderer, SDL_BLENDMODE_BLEND);
}


void cleanup_draw(void) {
    SDL_DestroyWindow(window);
    SDL_Quit();
}



static void draw_full_screen_road(road_t *road) {
    uint32_t i,j;

    uint32_t road_width_px  = WINDOW_SIZE_X*14/16;

    uint32_t px_per_meter = road_width_px / (road->length / CFG_SPACE_SCALE);
    road_width_px = road->length*px_per_meter/CFG_SPACE_SCALE; /* fix truncation problems */
    uint32_t lane_height_px = 5*px_per_meter;
    
    uint32_t road_height_px = lane_height_px*road->num_lanes;
    uint32_t road_top = WINDOW_SIZE_Y/2 - road_height_px/2;
    uint32_t road_left = WINDOW_SIZE_X/2 - road_width_px/2;

    uint32_t stripe_length_px = 1*px_per_meter;
    uint32_t stripe_height_px = stripe_length_px/16;

    stripe_length_px = stripe_length_px > 0 ? stripe_length_px : 1;
    stripe_height_px = stripe_height_px > 0 ? stripe_height_px : 1;

    SDL_Rect road_surface = {road_left, road_top, road_width_px, road_height_px};
    SDL_SetRenderDrawColor(renderer, 0x30, 0x30, 0x30, 0xFF);
    SDL_RenderFillRect(renderer, &road_surface);
 
    /* Draw stripes */
    if(road->num_lanes > 1) {
        for(i = 1; i < road->num_lanes; i++) {
            for(j = 0; j < road_width_px; j+=4*stripe_length_px) {
                SDL_Rect lane_stripe = {
                    road_left + j,
                    road_top + lane_height_px + (i-1)*lane_height_px,
                    stripe_length_px,
                    stripe_height_px};
                SDL_SetRenderDrawColor(renderer, 0xFF, 0xFF, 0x55, 0xFF);
                SDL_RenderFillRect(renderer, &lane_stripe);
            }
        }
    }

    uint32_t car_height_px = 3*px_per_meter;

    
    for(i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];

        /* draw sensor views */
        sensor_view_t view;
        build_sensor_view(car, road, &view);
        SDL_SetRenderDrawColor(renderer, 0x00, 0x00, 0xFF, 0x20);
        if(view.back < view.front) {        
            SDL_Rect view_rect = {
                road_left + view.back*px_per_meter/CFG_SPACE_SCALE,
                road_top + view.left*lane_height_px,
                (view.front-view.back)*px_per_meter/CFG_SPACE_SCALE,
                (view.right-view.left)*lane_height_px
            };
            SDL_RenderFillRect(renderer, &view_rect);
        } else {
            SDL_Rect view_rect = {
                road_left,
                road_top + view.left*lane_height_px,
                (view.front)*px_per_meter/CFG_SPACE_SCALE,
                (view.right-view.left)*lane_height_px
            };
            SDL_RenderFillRect(renderer, &view_rect);
            
            view_rect = (SDL_Rect){
                road_left + view.back*px_per_meter/CFG_SPACE_SCALE,
                road_top + view.left*lane_height_px,
                (road->length-view.back)*px_per_meter/CFG_SPACE_SCALE,
                (view.right-view.left)*lane_height_px
            };
            SDL_RenderFillRect(renderer, &view_rect);
        }
        

        /* draw car */
        SDL_Rect car_rect = {
            road_left + (car->pos-car->length)*px_per_meter/CFG_SPACE_SCALE,
            road_top + (lane_height_px/2 - car_height_px/2) + car->lane*lane_height_px,
            car->length*px_per_meter/CFG_SPACE_SCALE,
            car_height_px
        };
        if(car->acc >= 0) {
            SDL_SetRenderDrawColor(renderer, 0x00, 0xFF, 0x00, 0xFF);
        } else {
           SDL_SetRenderDrawColor(renderer, 0xFF, 0x00, 0x00, 0xFF);
        }
        SDL_RenderFillRect(renderer, &car_rect);

    }
}


void draw(road_t *road) {
    SDL_SetRenderDrawColor(renderer, 0xAA, 0xAA, 0xAA, 0xFF);
    SDL_RenderClear(renderer);

    draw_full_screen_road(road);


    SDL_RenderPresent(renderer);

}

