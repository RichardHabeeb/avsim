#include <stdio.h>
#include <stdint.h>
#include <SDL2/SDL.h>

#include <util.h>
#include <sim.h>
#include <config.h>
#include <draw.h>
#include <road.h>
#include <car.h>


void set_draw_scale(vis_t * vis, SDL_Point s) {
    s.x = max(1, min(DRAW_SCALE_MAX, s.x))*CFG_WORLD_SIZE_X/(DRAW_SCALE_MAX);
    s.y = max(1, min(DRAW_SCALE_MAX, s.y))*CFG_WORLD_SIZE_Y/(DRAW_SCALE_MAX);

    vis->view.x -= (s.x-vis->view.w)/2;
    vis->view.y -= (s.y-vis->view.h)/2;
    vis->view.w = s.x;
    vis->view.h = s.y;

    vis->view.x = max(0, min(CFG_WORLD_SIZE_X-vis->view.w, vis->view.x));
    vis->view.y = max(0, min(CFG_WORLD_SIZE_Y-vis->view.h, vis->view.y));

}

SDL_Point get_draw_scale(vis_t *vis) {
    return (SDL_Point) {
        max(1, min(DRAW_SCALE_MAX, vis->view.w*DRAW_SCALE_MAX/(CFG_WORLD_SIZE_X))),
        max(1, min(DRAW_SCALE_MAX, vis->view.h*DRAW_SCALE_MAX/(CFG_WORLD_SIZE_Y)))};
}


void set_draw_translation(vis_t *vis, SDL_Point s) {
    vis->view.x = max(0, min(CFG_WORLD_SIZE_X-vis->view.w, s.x));
    vis->view.y = max(0, min(CFG_WORLD_SIZE_Y-vis->view.h, s.y));
}

SDL_Point get_draw_translation(vis_t *vis) {
    return (SDL_Point) {vis->view.x, vis->view.y};
}



void setup_draw(vis_t *vis, sim_t *sim) {
    if(SDL_Init(SDL_INIT_VIDEO) < 0) {
        printf("Failed to initialize SDL\n");
        return;
    }

    vis->window = SDL_CreateWindow(
            "Autonomous Car Simulator (Press SPACE to pause, Q to quit)",
            SDL_WINDOWPOS_UNDEFINED,
            SDL_WINDOWPOS_UNDEFINED,
            CFG_WINDOW_SIZE_X,
            CFG_WINDOW_SIZE_Y,
            SDL_WINDOW_SHOWN); //TODO resizeable window
    if(vis->window == NULL) {
        printf("Failed to initialize SDL window\n");
        return;
    }

    vis->rend = SDL_CreateRenderer(vis->window, -1, SDL_RENDERER_ACCELERATED);
    if(vis->rend == NULL) {
        printf("Failed to initialize SDL vis->rend\n");
        return;
    }

    SDL_SetRenderDrawBlendMode(vis->rend, SDL_BLENDMODE_BLEND);
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "1");

    vis->world_tex = SDL_CreateTexture(
            vis->rend,
            SDL_PIXELFORMAT_RGBA8888,
            SDL_TEXTUREACCESS_TARGET,
            CFG_WORLD_SIZE_X,
            CFG_WORLD_SIZE_Y);

    vis->view.x = CFG_WORLD_SIZE_X/2 - CFG_WINDOW_SIZE_X/2;
    vis->view.y = CFG_WORLD_SIZE_Y/2 - CFG_WINDOW_SIZE_Y/2;
    vis->view.w = CFG_WINDOW_SIZE_X;
    vis->view.h = CFG_WINDOW_SIZE_Y;
    
    vis->road_tex = (SDL_Texture **)malloc(sizeof(SDL_Texture *)*sim->model.num_roads);
    vis->road_dim = (SDL_Rect *)malloc(sizeof(SDL_Rect)*sim->model.num_roads);

    if(sim->model.num_roads == 1) {
        road_t *road = &sim->model.roads[0];
        SDL_Rect *road_dim = &vis->road_dim[0];

        road_dim->w = CFG_WORLD_SIZE_X*14/16;

        /* fix truncation problems TODO: scale better */
        uint32_t px_per_m = road_dim->w / (road->length / CFG_SPACE_SCALE);

        road_dim->w = road->length*px_per_m/CFG_SPACE_SCALE; 
        road_dim->h = CFG_SINGLE_LANE_HEIGHT_M*px_per_m*road->num_lanes;
        road_dim->x = CFG_WORLD_SIZE_X/2 - road_dim->w/2;
        road_dim->y = CFG_WORLD_SIZE_Y/2 - road_dim->h/2; 

        vis->road_tex[0] = SDL_CreateTexture(vis->rend,
                                             SDL_PIXELFORMAT_RGBA8888,
                                             SDL_TEXTUREACCESS_TARGET,
                                             road_dim->w,
                                             road_dim->h);
    } else {
        //TODO support for road networks
    }
    
}



void cleanup_draw(vis_t *vis) {
    SDL_DestroyWindow(vis->window);
    SDL_DestroyRenderer(vis->rend);
    //TODO destroy textures, free mallocs
    SDL_Quit();
}


void map_point_to_drawn_object(uint32_t x, uint32_t y, car_t **car, road_t **road) {
    //TODO
}



static void draw_road(vis_t *vis, road_t *road, uint32_t road_width_px, uint32_t road_height_px) {

    uint32_t i,j;

    /* Assumes that widths and heights have been scaled so that px_per_m is an int w/o truncation */
    uint32_t px_per_m = road_width_px / (road->length / CFG_SPACE_SCALE);

    uint32_t lane_height_px = CFG_SINGLE_LANE_HEIGHT_M*px_per_m;

    /* Draw road surface */
    SDL_Rect road_surface = {0, 0, road_width_px, road_height_px};
    SDL_SetRenderDrawColor(vis->rend, 0x30, 0x30, 0x30, 0xFF);
    SDL_RenderFillRect(vis->rend, &road_surface);
 
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
                SDL_SetRenderDrawColor(vis->rend, 0xFF, 0xFF, 0x55, 0xFF);
                SDL_RenderFillRect(vis->rend, &lane_stripe);
            }
        }
    }

    /* draw sensor views */
    for(i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];

        sensor_view_t view;
        build_sensor_view(car, road, &view);
        SDL_SetRenderDrawColor(vis->rend, 0x00, 0x00, 0xFF, 0x20);

        uint32_t view_top = view.left*lane_height_px;
        uint32_t view_height = (1+view.right-view.left)*lane_height_px;


        if(view.back < view.front) {        
            SDL_Rect view_rect = {
                view.back*px_per_m/CFG_SPACE_SCALE,
                view_top,
                (view.front-view.back)*px_per_m/CFG_SPACE_SCALE,
                view_height
            };
            SDL_RenderFillRect(vis->rend, &view_rect);
        } else {
            SDL_Rect view_rect = {
                0,
                view_top,
                (view.front)*px_per_m/CFG_SPACE_SCALE,
                view_height
            };
            SDL_RenderFillRect(vis->rend, &view_rect);
            
            view_rect = (SDL_Rect){
                view.back*px_per_m/CFG_SPACE_SCALE,
                view_top,
                (road->length-view.back)*px_per_m/CFG_SPACE_SCALE,
                view_height
            };
            SDL_RenderFillRect(vis->rend, &view_rect);
        }
    }

    /* Draw cars */
    uint32_t car_height_px = CFG_CAR_WIDTH_M*px_per_m;
    for(i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];
        
        SDL_SetRenderDrawColor(vis->rend, 0xFF - 0x80*car->spd/car->top_spd, (0xFF*car->spd/car->top_spd), 0x00, 0xFF);

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
            SDL_RenderFillRect(vis->rend, &car_rect);
        } else {
            uint32_t rear_pos = sub_mod(car->pos, car->length, road->length);

            SDL_Rect car_rect = {
                0,
                car_top,
                car->pos*px_per_m/CFG_SPACE_SCALE,
                car_height_px
            };
            SDL_RenderFillRect(vis->rend, &car_rect);
            
            car_rect = (SDL_Rect){
                rear_pos*px_per_m/CFG_SPACE_SCALE,
                car_top,
                (car->length - car->pos)*px_per_m/CFG_SPACE_SCALE,
                car_height_px
            };
            SDL_RenderFillRect(vis->rend, &car_rect);
        }
    }
}



void draw(vis_t *vis, sim_t *sim) {
    /* Render the world BG */
    SDL_SetRenderTarget(vis->rend, vis->world_tex);
    SDL_SetRenderDrawColor(vis->rend, 0xAA, 0xAA, 0xAA, 0xFF);
    SDL_RenderClear(vis->rend);

    /* Render roads into the world */
    if(sim->model.num_roads == 1) {
        SDL_SetRenderTarget(vis->rend, vis->road_tex[0]);
        draw_road(vis, sim->model.roads, vis->road_dim->w, vis->road_dim->h);
        
        SDL_SetRenderTarget(vis->rend, vis->world_tex);
        SDL_RenderCopyEx(vis->rend, vis->road_tex[0], NULL, vis->road_dim, 0.0, NULL, SDL_FLIP_NONE);
    } else {
        //TODO
    }

    /* Render to the window */
    SDL_SetRenderTarget(vis->rend, NULL);
    SDL_RenderClear(vis->rend);

    const SDL_Rect window_rect = {0,0,CFG_WINDOW_SIZE_X,CFG_WINDOW_SIZE_Y};
    SDL_RenderCopyEx(vis->rend, vis->world_tex, &vis->view, &window_rect, 0.0, NULL, SDL_FLIP_NONE);

    SDL_RenderPresent(vis->rend);
}

