#include <stdio.h>
#include <stdint.h>
#include <SDL2/SDL.h>

#include <util.h>
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

    
    /* draw sensor views */
    for(i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];

        sensor_view_t view;
        build_sensor_view(car, road, &view);
        SDL_SetRenderDrawColor(renderer, 0x00, 0x00, 0xFF, 0x20);

        uint32_t view_top = road_top + view.left*lane_height_px;
        uint32_t view_height = (1+view.right-view.left)*lane_height_px;

        if(view_top+view_height >= road_top+(road->num_lanes-1)*lane_height_px) {
            view_height -= lane_height_px;
        }


        if(view.back < view.front) {        
            SDL_Rect view_rect = {
                road_left + view.back*px_per_meter/CFG_SPACE_SCALE,
                view_top,
                (view.front-view.back)*px_per_meter/CFG_SPACE_SCALE,
                view_height
            };
            SDL_RenderFillRect(renderer, &view_rect);
        } else {
            SDL_Rect view_rect = {
                road_left,
                view_top,
                (view.front)*px_per_meter/CFG_SPACE_SCALE,
                view_height
            };
            SDL_RenderFillRect(renderer, &view_rect);
            
            view_rect = (SDL_Rect){
                road_left + view.back*px_per_meter/CFG_SPACE_SCALE,
                view_top,
                (road->length-view.back)*px_per_meter/CFG_SPACE_SCALE,
                view_height
            };
            SDL_RenderFillRect(renderer, &view_rect);
        }
    }

    /* draw car */
    for(i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];
        
        SDL_SetRenderDrawColor(renderer, 0xFF - 0x80*car->spd/car->top_spd, (0xFF*car->spd/car->top_spd), 0x00, 0xFF);

        uint32_t car_top =
            road_top + 
            (lane_height_px/2 - car_height_px/2) + 
            car->lane*lane_height_px;

        if(car->r_blinker) {
            car_top += lane_height_px - (lane_height_px*car->lane_change_remaining_ticks/(CFG_CAR_LANE_CHANGE_S*CFG_TICKS_PER_S));
        } else if(car->l_blinker) {
            car_top -= lane_height_px - (lane_height_px*car->lane_change_remaining_ticks/(CFG_CAR_LANE_CHANGE_S*CFG_TICKS_PER_S));
        }
                


        if(car->pos >= car->length) {
            SDL_Rect car_rect = {
                road_left + (car->pos-car->length)*px_per_meter/CFG_SPACE_SCALE,
                car_top,
                car->length*px_per_meter/CFG_SPACE_SCALE,
                car_height_px
            };
            SDL_RenderFillRect(renderer, &car_rect);
        } else {
            uint32_t rear_pos = sub_mod(car->pos, car->length, road->length);

            SDL_Rect car_rect = {
                road_left,
                car_top,
                car->pos*px_per_meter/CFG_SPACE_SCALE,
                car_height_px
            };
            SDL_RenderFillRect(renderer, &car_rect);
            
            car_rect = (SDL_Rect){
                road_left + rear_pos*px_per_meter/CFG_SPACE_SCALE,
                car_top,
                (car->length - car->pos)*px_per_meter/CFG_SPACE_SCALE,
                car_height_px
            };
            SDL_RenderFillRect(renderer, &car_rect);
        }

        

    }
}


void draw(road_t *road) {
    SDL_SetRenderDrawColor(renderer, 0xAA, 0xAA, 0xAA, 0xFF);
    SDL_RenderClear(renderer);

    draw_full_screen_road(road);


    SDL_RenderPresent(renderer);

}

