#include <cstdint>
#include <algorithm>

#include <SDL2/SDL.h>
#include <SDL2/SDL2_gfxPrimitives.h>

#include "src/visualization/vis2d.h"
#include "src/simulation/sim.h"
#include "src/roads/segment.h"
#include "src/common/ctypes.h"

extern "C" {
#include "src/common/config.h"
#include "src/vehicles/simple_car.h"
}

namespace avsim {
namespace visualization {

void Vis2d::setScale(point_int64_t s) {
    s.x = std::max(1L, std::min(ScaleMax, s.x))
          * CFG_WORLD_SIZE_X / ScaleMax;

    s.y = std::max(1L, std::min(ScaleMax, s.y))
          * CFG_WORLD_SIZE_Y / ScaleMax;

    view.x -= (s.x-view.w)/2;
    view.y -= (s.y-view.h)/2;
    view.w = s.x;
    view.h = s.y;

    view.x = std::max(0, std::min(CFG_WORLD_SIZE_X-view.w, view.x));
    view.y = std::max(0, std::min(CFG_WORLD_SIZE_Y-view.h, view.y));
}


point_int64_t Vis2d::getScale() {
    return {
        std::max(1L,
                 std::min(ScaleMax,
                          view.w*ScaleMax/CFG_WORLD_SIZE_X)),
        std::max(1L,
                 std::min(ScaleMax,
                          view.h*ScaleMax/CFG_WORLD_SIZE_Y))
    };
}

void  Vis2d::setTranslation(SDL_Point s) {
    view.x = std::max(0, std::min(CFG_WORLD_SIZE_X-view.w, s.x));
    view.y = std::max(0, std::min(CFG_WORLD_SIZE_Y-view.h, s.y));
}


SDL_Point Vis2d::getTranslation() {
    return (SDL_Point) {view.x, view.y};
}


Vis2d::Error Vis2d::setup(simulation::Sim &sim) {
    if(SDL_Init(SDL_INIT_VIDEO) < 0) {
        return InternalError;
    }
    window = SDL_CreateWindow(
            "Autonomous Car Simulator (Press SPACE to pause, Q to quit)",
            SDL_WINDOWPOS_UNDEFINED,
            SDL_WINDOWPOS_UNDEFINED,
            CFG_WINDOW_SIZE_X,
            CFG_WINDOW_SIZE_Y,
            SDL_WINDOW_SHOWN); //TODO resizeable window
    if(window == NULL) {
        return InternalError;
    }

    rend = SDL_CreateRenderer(window, -1, SDL_RENDERER_ACCELERATED);
    if(rend == NULL) {
        return InternalError;
    }

    SDL_SetRenderDrawBlendMode(rend, SDL_BLENDMODE_BLEND);
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "1");

    world_tex = SDL_CreateTexture(
            rend,
            SDL_PIXELFORMAT_RGBA8888,
            SDL_TEXTUREACCESS_TARGET,
            CFG_WORLD_SIZE_X,
            CFG_WORLD_SIZE_Y);

    view.x = CFG_WORLD_SIZE_X/2 - CFG_WINDOW_SIZE_X/2;
    view.y = CFG_WORLD_SIZE_Y/2 - CFG_WINDOW_SIZE_Y/2;
    view.w = CFG_WINDOW_SIZE_X;
    view.h = CFG_WINDOW_SIZE_Y;
    
    road_tex.reserve(sim.roads.size());

    for(auto it = sim.roads.begin();
        it != sim.roads.end(); ++it)
    {
        auto road = *it;
        road_tex.push_back({
            SDL_CreateTexture(
                rend,
                SDL_PIXELFORMAT_RGBA8888,
                SDL_TEXTUREACCESS_TARGET,
                toPixels(road->width()).v,
                toPixels(road->height()).v),
            road
        });
    } 
    return NoError;
}


Vis2d::~Vis2d() {
    SDL_DestroyWindow(window);
    SDL_DestroyRenderer(rend);
    //TODO destroy textures, free mallocs
    SDL_Quit();
}

Vis2d::Error Vis2d::mapPointToDrawnObject(
    simulation::Sim &sim,
    SDL_Point p,
    car_t **car_ret,
    roads::RoadSegment **road_ret)
{

    if(road_ret != NULL) {
        for(auto it = sim.roads.begin();
            it != sim.roads.end(); ++it)
        {
            /* TODO */
        }
    }

    if(car_ret != NULL) {
        for(auto it = sim.cars.begin();
            it != sim.cars.end(); ++it)
        {
            /* TODO */
        }
    }
    
    return NoError;
}



Vis2d::Error Vis2d::drawRoad(roads::RoadSegment &road)
{
    auto road_width_px = toPixels(road.width());
    auto road_height_px = toPixels(road.height());
    //pixels_t lane_height_px = {
    //    road_height_px.v /
    //    static_cast<decltype(pixels_t::v)>(road.lanes())};

    /* Draw road surface */
    SDL_Rect road_surface = {0, 0, 
        static_cast<int>(road_width_px.v),
        static_cast<int>(road_height_px.v)};
    SDL_SetRenderDrawColor(rend, 0x30, 0x30, 0x30, 0xFF);
    SDL_RenderFillRect(rend, &road_surface);
 
    /* Draw stripes */
//    uint32_t stripe_length_px = 1*px_per_m;
//    uint32_t stripe_height_px = stripe_length_px/16;
//    stripe_length_px = stripe_length_px > 0 ? stripe_length_px : 1;
//    stripe_height_px = stripe_height_px > 0 ? stripe_height_px : 1;
//    if(road.num_lanes > 1) {
//        for(i = 1; i < road.num_lanes; i++) {
//            for(j = 0; j < road_width_px; j+=4*stripe_length_px) {
//                SDL_Rect lane_stripe = {
//                    j,
//                    lane_height_px + (i-1)*lane_height_px,
//                    stripe_length_px,
//                    stripe_height_px};
//                SDL_SetRenderDrawColor(rend, 0xFF, 0xFF, 0x55, 0xFF);
//                SDL_RenderFillRect(rend, &lane_stripe);
//            }
//        }
//    }

    /* draw sensor views */
//    for(i = 0; i < road.num_cars; i++) {
//        car_t *car = &road.cars[i];
//
//        if(!car->selected) continue;
//
//        sensor_view_t view;
//        build_sensor_view(car, &road, &view);
//        SDL_SetRenderDrawColor(rend, 0x00, 0x00, 0xFF, 0x20);
//
//        uint32_t view_top = view.left*lane_height_px;
//        uint32_t view_height = (1+view.right-view.left)*lane_height_px;
//
//
//        if(view.back < view.front) {        
//            SDL_Rect view_rect = {
//                view.back*px_per_m/CFG_SPACE_SCALE,
//                view_top,
//                (view.front-view.back)*px_per_m/CFG_SPACE_SCALE,
//                view_height
//            };
//            SDL_RenderFillRect(rend, &view_rect);
//        } else {
//            SDL_Rect view_rect = {
//                0,
//                view_top,
//                (view.front)*px_per_m/CFG_SPACE_SCALE,
//                view_height
//            };
//            SDL_RenderFillRect(rend, &view_rect);
//            
//            view_rect = (SDL_Rect){
//                view.back*px_per_m/CFG_SPACE_SCALE,
//                view_top,
//                (road.length-view.back)*px_per_m/CFG_SPACE_SCALE,
//                view_height
//            };
//            SDL_RenderFillRect(rend, &view_rect);
//        }
//    }

    /* Draw cars */
//    uint32_t car_height_px = CFG_CAR_WIDTH_M*px_per_m;
//    for(i = 0; i < road.num_cars; i++) {
//        car_t *car = &road.cars[i];
//        
//        SDL_SetRenderDrawColor(rend, 0xFF - 0x80*car->spd/car->top_spd, (0xFF*car->spd/car->top_spd), 0x00, 0xFF);
//
//        uint32_t car_top = (lane_height_px/2 - car_height_px/2) + car->lane*lane_height_px;
//
//        if(car->r_blinker) {
//            car_top += lane_height_px - (lane_height_px*car->lane_change_remaining_ticks/(CFG_CAR_LANE_CHANGE_S*CFG_TICKS_PER_S));
//        } else if(car->l_blinker) {
//            car_top -= lane_height_px - (lane_height_px*car->lane_change_remaining_ticks/(CFG_CAR_LANE_CHANGE_S*CFG_TICKS_PER_S));
//        }
//
//        if(car->pos >= car->length) {
//            SDL_Rect car_rect = {
//                (car->pos-car->length)*px_per_m/CFG_SPACE_SCALE,
//                car_top,
//                car->length*px_per_m/CFG_SPACE_SCALE,
//                car_height_px
//            };
//            SDL_RenderFillRect(rend, &car_rect);
//        } else {
//            uint32_t rear_pos = sub_mod(car->pos, car->length, road.length);
//
//            SDL_Rect car_rect = {
//                0,
//                car_top,
//                car->pos*px_per_m/CFG_SPACE_SCALE,
//                car_height_px
//            };
//            SDL_RenderFillRect(rend, &car_rect);
//            
//            car_rect = (SDL_Rect){
//                rear_pos*px_per_m/CFG_SPACE_SCALE,
//                car_top,
//                (car->length - car->pos)*px_per_m/CFG_SPACE_SCALE,
//                car_height_px
//            };
//            SDL_RenderFillRect(rend, &car_rect);
//        }
//    }
    return NoError;
}


Vis2d::Error Vis2d::draw(simulation::Sim &sim) {
    /* Render the world BG */
    SDL_SetRenderTarget(rend, world_tex);
    SDL_SetRenderDrawColor(rend, 0xAA, 0xAA, 0xAA, 0xFF);
    SDL_RenderClear(rend);

    /* Render roads into the world */
    for(auto it = road_tex.begin(); it != road_tex.end(); ++it)
    {
        auto tex = (*it).first;
        auto road = (*it).second;

        SDL_SetRenderTarget(rend, tex);
        drawRoad(*road);
        
        SDL_Rect r = roadToSDLRect(*road);
        SDL_SetRenderTarget(rend, world_tex);
        SDL_RenderCopyEx(rend,
                         tex,
                         NULL,
                         &r,
                         0.0,
                         NULL,
                         SDL_FLIP_NONE);
    }

    /* Render to the window */
    SDL_SetRenderTarget(rend, NULL);
    SDL_RenderClear(rend);

    const SDL_Rect window_rect = {
        0,
        0,
        CFG_WINDOW_SIZE_X,
        CFG_WINDOW_SIZE_Y
    };

    SDL_RenderCopyEx(
        rend,
        world_tex,
        &view,
        &window_rect,
        0.0,
        NULL,
        SDL_FLIP_NONE);

    SDL_RenderPresent(rend);
    return NoError;
}


} /* visualization */
} /* avsim */
