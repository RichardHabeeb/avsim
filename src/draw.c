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
static SDL_Texture *world = NULL;

static SDL_Texture *full_screen_road = NULL;
static SDL_Rect full_screen_road_rect;

static SDL_Rect view_rect = {
    CFG_WORLD_SIZE_X/2 - CFG_WINDOW_SIZE_X/2,
    CFG_WORLD_SIZE_Y/2 - CFG_WINDOW_SIZE_Y/2,
    CFG_WINDOW_SIZE_X,
    CFG_WINDOW_SIZE_Y};

static uint16_t view_rotation = 0;

void set_draw_scale(SDL_Point s) {
    s.x = max(1, min(DRAW_SCALE_MAX, s.x))*CFG_WORLD_SIZE_X/(DRAW_SCALE_MAX);
    s.y = max(1, min(DRAW_SCALE_MAX, s.y))*CFG_WORLD_SIZE_Y/(DRAW_SCALE_MAX);

    view_rect.x -= (s.x-view_rect.w)/2;
    view_rect.y -= (s.y-view_rect.h)/2;
    view_rect.w = s.x;
    view_rect.h = s.y;

    view_rect.x = max(0, min(CFG_WORLD_SIZE_X-view_rect.w, view_rect.x));
    view_rect.y = max(0, min(CFG_WORLD_SIZE_Y-view_rect.h, view_rect.y));

}

SDL_Point get_draw_scale() {
    SDL_Point s;
    s.x = max(1, min(DRAW_SCALE_MAX, view_rect.w*DRAW_SCALE_MAX/(CFG_WORLD_SIZE_X)));
    s.y = max(1, min(DRAW_SCALE_MAX, view_rect.h*DRAW_SCALE_MAX/(CFG_WORLD_SIZE_Y)));
    printf("%i %i\n",s.x, s.y);
    return s;
}

void set_draw_translation(SDL_Point s) {
    view_rect.x = max(0, min(CFG_WORLD_SIZE_X-view_rect.w, s.x));
    view_rect.y = max(0, min(CFG_WORLD_SIZE_Y-view_rect.h, s.y));
}

SDL_Point get_draw_translation() {
    return (SDL_Point) {view_rect.x, view_rect.y};
}




void setup_draw(road_t *roads, uint32_t num_roads) {
    if(SDL_Init(SDL_INIT_VIDEO) < 0) {
        //TODO error
    }

    window = SDL_CreateWindow(
            "Autonomous Car Simulator (Press SPACE to pause, Q to quit)",
            SDL_WINDOWPOS_UNDEFINED,
            SDL_WINDOWPOS_UNDEFINED,
            CFG_WINDOW_SIZE_X,
            CFG_WINDOW_SIZE_Y,
            SDL_WINDOW_SHOWN);
    if(window == NULL) {
        //TODO error
    }

    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "1");

    renderer = SDL_CreateRenderer(window, -1, SDL_RENDERER_ACCELERATED);
    if(renderer == NULL) {
        //TODO error
    }
    SDL_SetRenderDrawBlendMode(renderer, SDL_BLENDMODE_BLEND);

    world = SDL_CreateTexture(renderer,
                              SDL_PIXELFORMAT_RGBA8888,
                              SDL_TEXTUREACCESS_TARGET,
                              CFG_WORLD_SIZE_X,
                              CFG_WORLD_SIZE_Y);

    if(num_roads == 1) {

        /* Scale the road to fit the world size */
        uint32_t road_width_px  = CFG_WORLD_SIZE_X*14/16;
        uint32_t px_per_m = road_width_px / (roads[0].length / CFG_SPACE_SCALE);
        road_width_px = roads[0].length*px_per_m/CFG_SPACE_SCALE; /* fix truncation problems */
        uint32_t lane_height_px = CFG_SINGLE_LANE_HEIGHT_M*px_per_m;
        uint32_t road_height_px = lane_height_px*roads[0].num_lanes;
        
        full_screen_road_rect.w = road_width_px;
        full_screen_road_rect.h = road_height_px;
        full_screen_road_rect.x = CFG_WORLD_SIZE_X/2 - road_width_px/2;
        full_screen_road_rect.y = CFG_WORLD_SIZE_Y/2 - road_height_px/2;      

        full_screen_road = SDL_CreateTexture(renderer,
                                             SDL_PIXELFORMAT_RGBA8888,
                                             SDL_TEXTUREACCESS_TARGET,
                                             road_width_px,
                                             road_height_px);
    } else {
        //TODO support for road networks
    }
    
}



void cleanup_draw(void) {
    SDL_DestroyWindow(window);
    SDL_Quit();
}
void map_point_to_drawn_object(uint32_t x, uint32_t y, car_t **car, road_t **road) {

}



static void draw_road(road_t *road, uint32_t road_width_px, uint32_t road_height_px) {
    uint32_t i,j;

    /* Assumes that widths and heights have been scaled so that px_per_m is an int w/o truncation */
    uint32_t px_per_m = road_width_px / (road->length / CFG_SPACE_SCALE);

    uint32_t lane_height_px = CFG_SINGLE_LANE_HEIGHT_M*px_per_m;

    /* Draw road surface */
    SDL_Rect road_surface = {0, 0, road_width_px, road_height_px};
    SDL_SetRenderDrawColor(renderer, 0x30, 0x30, 0x30, 0xFF);
    SDL_RenderFillRect(renderer, &road_surface);
 
    /* Draw stripes */
    uint32_t stripe_length_px = 1*px_per_m;
    uint32_t stripe_height_px = stripe_length_px/16;
    stripe_length_px = stripe_length_px > 0 ? stripe_length_px : 1;
    stripe_height_px = stripe_height_px > 0 ? stripe_height_px : 1;
    if(road->num_lanes > 1) {
        for(i = 1; i < road->num_lanes; i++) {
            for(j = 0; j < road_width_px; j+=4*stripe_length_px) {
                SDL_Rect lane_stripe = {
                    j,
                    lane_height_px + (i-1)*lane_height_px,
                    stripe_length_px,
                    stripe_height_px};
                SDL_SetRenderDrawColor(renderer, 0xFF, 0xFF, 0x55, 0xFF);
                SDL_RenderFillRect(renderer, &lane_stripe);
            }
        }
    }

    /* draw sensor views */
    for(i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];

        sensor_view_t view;
        build_sensor_view(car, road, &view);
        SDL_SetRenderDrawColor(renderer, 0x00, 0x00, 0xFF, 0x20);

        uint32_t view_top = view.left*lane_height_px;
        uint32_t view_height = (1+view.right-view.left)*lane_height_px;

        /* temporary bugfix for visualization */
        if(view_top+view_height >= (road->num_lanes-1)*lane_height_px) {
            view_height -= lane_height_px;
        }


        if(view.back < view.front) {        
            SDL_Rect view_rect = {
                view.back*px_per_m/CFG_SPACE_SCALE,
                view_top,
                (view.front-view.back)*px_per_m/CFG_SPACE_SCALE,
                view_height
            };
            SDL_RenderFillRect(renderer, &view_rect);
        } else {
            SDL_Rect view_rect = {
                0,
                view_top,
                (view.front)*px_per_m/CFG_SPACE_SCALE,
                view_height
            };
            SDL_RenderFillRect(renderer, &view_rect);
            
            view_rect = (SDL_Rect){
                view.back*px_per_m/CFG_SPACE_SCALE,
                view_top,
                (road->length-view.back)*px_per_m/CFG_SPACE_SCALE,
                view_height
            };
            SDL_RenderFillRect(renderer, &view_rect);
        }
    }

    /* Draw cars */
    uint32_t car_height_px = CFG_CAR_WIDTH_M*px_per_m;
    for(i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];
        
        SDL_SetRenderDrawColor(renderer, 0xFF - 0x80*car->spd/car->top_spd, (0xFF*car->spd/car->top_spd), 0x00, 0xFF);

        uint32_t car_top = (lane_height_px/2 - car_height_px/2) + car->lane*lane_height_px;

        if(car->r_blinker) {
            car_top += lane_height_px - (lane_height_px*car->lane_change_remaining_ticks/(CFG_CAR_LANE_CHANGE_S*CFG_TICKS_PER_S));
        } else if(car->l_blinker) {
            car_top -= lane_height_px - (lane_height_px*car->lane_change_remaining_ticks/(CFG_CAR_LANE_CHANGE_S*CFG_TICKS_PER_S));
        }

        if(car->pos >= car->length) {
            SDL_Rect car_rect = {
                (car->pos-car->length)*px_per_m/CFG_SPACE_SCALE,
                car_top,
                car->length*px_per_m/CFG_SPACE_SCALE,
                car_height_px
            };
            SDL_RenderFillRect(renderer, &car_rect);
        } else {
            uint32_t rear_pos = sub_mod(car->pos, car->length, road->length);

            SDL_Rect car_rect = {
                0,
                car_top,
                car->pos*px_per_m/CFG_SPACE_SCALE,
                car_height_px
            };
            SDL_RenderFillRect(renderer, &car_rect);
            
            car_rect = (SDL_Rect){
                rear_pos*px_per_m/CFG_SPACE_SCALE,
                car_top,
                (car->length - car->pos)*px_per_m/CFG_SPACE_SCALE,
                car_height_px
            };
            SDL_RenderFillRect(renderer, &car_rect);
        }
    }

}



void draw(road_t *roads, uint32_t num_roads) {
    SDL_SetRenderTarget(renderer, world);
    SDL_SetRenderDrawColor(renderer, 0xAA, 0xAA, 0xAA, 0xFF);
    SDL_RenderClear(renderer);

    if(num_roads == 1) {
        SDL_SetRenderTarget(renderer, full_screen_road);
        draw_road(roads, full_screen_road_rect.w, full_screen_road_rect.h);
        //draw_full_screen_road(road);
        //
        
        SDL_SetRenderTarget(renderer, world);
        SDL_RenderCopyEx(renderer, full_screen_road, NULL, &full_screen_road_rect, 0, NULL, SDL_FLIP_NONE);

    }

    const SDL_Rect window_rect = {0,0,CFG_WINDOW_SIZE_X,CFG_WINDOW_SIZE_Y};
    SDL_SetRenderTarget(renderer, NULL);
    SDL_RenderClear(renderer);


    SDL_RenderCopyEx(renderer, world, &view_rect, &window_rect, view_rotation*360.0/65535.0, NULL, SDL_FLIP_NONE);

    SDL_RenderPresent(renderer);

}

