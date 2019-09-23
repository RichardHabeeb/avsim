#include <cstdint>
#include <algorithm>
#include <iostream>

#include <SDL2/SDL.h>
#include <SDL2/SDL2_gfxPrimitives.h>

#include "src/visualization/vis2d.h"
#include "src/simulation/sim.h"
#include "src/roads/segment.h"
#include "src/common/config.h"
#include "src/common/ctypes.h"
#include "src/common/algorithm.h"

extern "C" {
#include "src/vehicles/simple_car.h"
}

namespace avsim {
namespace visualization {


void Vis2d::setScale(double s) {
    _world_scale = common::clamp(s, 0.25, 5.0);
    SDL_RenderSetScale(rend, _world_scale, _world_scale);
}


double Vis2d::getScale() {
    return _world_scale;
}

void  Vis2d::setTranslation(point_pixels_t s) {
    
    auto window_size = getWindowSize();

    _world_origin.x = {common::clamp(s.x.v,
        static_cast<int64_t>(window_size.x.v/_world_scale) - toPixels(default_cfg.world_width).v,
        0L)};
    _world_origin.y = {common::clamp(s.y.v,
        static_cast<int64_t>(window_size.y.v/_world_scale) - toPixels(default_cfg.world_height).v,
        0L)};
}


point_pixels_t Vis2d::getTranslation() {
    return _world_origin;
}


point_pixels_t Vis2d::getWindowSize() {
    int window_w, window_h;
    SDL_GetWindowSize(window, &window_w, &window_h);
    return {
        .x = {window_w},
        .y = {window_h},
    };
}


Vis2d::Error Vis2d::setup(simulation::Sim &sim) {
    _pixels_per_meter = 8.0;
    _world_scale = 1.0;

    if(SDL_Init(SDL_INIT_VIDEO) < 0) {
        return InternalError;
    }
    SDL_GL_SetAttribute(SDL_GL_MULTISAMPLEBUFFERS, 1);
    SDL_GL_SetAttribute(SDL_GL_MULTISAMPLESAMPLES, 8);
    SDL_GL_SetAttribute(SDL_GL_ACCELERATED_VISUAL, 1);

    window = SDL_CreateWindow(
            "Autonomous Car Simulator (Press SPACE to pause, Q to quit)",
            SDL_WINDOWPOS_UNDEFINED,
            SDL_WINDOWPOS_UNDEFINED,
            default_cfg.window_width.v,
            default_cfg.window_height.v,
            SDL_WINDOW_SHOWN |
            SDL_WINDOW_RESIZABLE |
            SDL_WINDOW_OPENGL);
    if(window == NULL) {
        return InternalError;
    }

    rend = SDL_CreateRenderer(window, -1, SDL_RENDERER_ACCELERATED);
    if(rend == NULL) {
        return InternalError;
    }

    SDL_SetRenderDrawBlendMode(rend, SDL_BLENDMODE_BLEND);
    SDL_SetHint(SDL_HINT_RENDER_SCALE_QUALITY, "1");


    auto tiles_w = toPixels(default_cfg.world_width).v / default_cfg.world_tile_size.v;
    auto tiles_h = toPixels(default_cfg.world_height).v / default_cfg.world_tile_size.v;

    /* for now we use a uniform bg tile */
    auto bg_tex0 = SDL_CreateTexture(
        rend,
        SDL_PIXELFORMAT_RGBA8888,
        SDL_TEXTUREACCESS_TARGET,
        default_cfg.world_tile_size.v,
        default_cfg.world_tile_size.v);
    if(bg_tex0 == NULL) {
        return InternalError;
    }
    SDL_SetRenderTarget(rend, bg_tex0);
    SDL_SetRenderDrawColor(rend, 0xAA, 0xAA, 0xAA, 0xFF);
    SDL_RenderClear(rend);

    auto bg_tex1 = SDL_CreateTexture(
        rend,
        SDL_PIXELFORMAT_RGBA8888,
        SDL_TEXTUREACCESS_TARGET,
        default_cfg.world_tile_size.v,
        default_cfg.world_tile_size.v);
    if(bg_tex1 == NULL) {
        return InternalError;
    }
    SDL_SetRenderTarget(rend, bg_tex1);
    SDL_SetRenderDrawColor(rend, 0xBB, 0xBB, 0xBB, 0xFF);
    SDL_RenderClear(rend);

    bool checkered_r = false; /* do a checkerboard pattern */
    

    _world_tiles.resize(tiles_h);
    for(auto r = _world_tiles.begin(); r != _world_tiles.end(); ++r) {
        (*r).resize(tiles_w);
        bool checkered_c = checkered_r;
        for(auto c = (*r).begin(); c != (*r).end(); ++c) { 
            if(checkered_c) {
                *c = bg_tex0;
            } else {
                *c = bg_tex1;
            }
            checkered_c = !checkered_c;
        }
        checkered_r = !checkered_r;
    }


    _roads.reserve(sim.roads.size());

    for(auto it = sim.roads.begin();
        it != sim.roads.end(); ++it)
    {
        auto road = *it;
        auto _roadsture = SDL_CreateTexture(
            rend,
            SDL_PIXELFORMAT_RGBA8888,
            SDL_TEXTUREACCESS_TARGET,
            toPixels(road->width()).v,
            toPixels(road->height()).v);
        if(_roadsture == NULL) {
            std::cout << "Error: road texture too large\n";
            return InternalError;
        }

        _roads.push_back({_roadsture, road});
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


Vis2d::Error Vis2d::drawBackground() {
    
    SDL_SetRenderTarget(rend, NULL);
    SDL_RenderClear(rend);

    /* Render the world BG */
    SDL_Rect rect; 
    rect.w = static_cast<int>(default_cfg.world_tile_size.v);
    rect.h = static_cast<int>(default_cfg.world_tile_size.v);
    rect.x = _world_origin.x.v;
    rect.y = _world_origin.y.v;


    for(auto r = _world_tiles.begin(); r != _world_tiles.end(); ++r) {
        rect.x = _world_origin.x.v;
        for(auto c = (*r).begin(); c != (*r).end(); ++c) {
            /* Blit texture to window */
            SDL_RenderCopyEx(rend,
                *c,
                NULL,
                &rect,
                0.0,
                NULL,
                SDL_FLIP_NONE);

            rect.x += rect.w;
        }
        rect.y += rect.h;
    }

    return NoError;
}


Vis2d::Error Vis2d::drawRoad(roads::RoadSegment &road)
{
    auto road_width_px = toPixels(road.width());
    auto road_height_px = toPixels(road.height());


    /* Draw road surface */
    SDL_Rect road_surface = {
        0,
        0, 
        static_cast<int>(road_width_px.v),
        static_cast<int>(road_height_px.v)
    };
    SDL_SetRenderDrawColor(rend, 0x30, 0x30, 0x30, 0xFF);
    SDL_RenderFillRect(rend, &road_surface);
 

    /* Draw stripes */
    SDL_SetRenderDrawColor(rend, 0xFF, 0xFF, 0x55, 0xFF);

    pixels_t lane_height_px = {
        road_height_px.v /
        static_cast<decltype(pixels_t::v)>(road.lanes())
    };
    
    /* Two-way road */
    if( road.forward_lanes.size() > 0 &&
        road.opposite_lanes.size() > 0)
    {
        /* Draw center stripes */
        SDL_Rect stripe;
        stripe.w = road_surface.w;
        stripe.h = toPixels({0.2}).v;
        stripe.x = 0;
        stripe.y = road_surface.h/2 - 2*stripe.h;

        SDL_RenderFillRect(rend, &stripe); 

        stripe.y = road_surface.h/2 + 2*stripe.h;
        SDL_RenderFillRect(rend, &stripe);


    
    } else {
    }
    return NoError;
}



Vis2d::Error Vis2d::drawRoads(simulation::Sim &sim) {

    /* Render roads into the world */
    for(auto it = _roads.begin(); it != _roads.end(); ++it)
    {
        auto tex = (*it).first;
        auto road = (*it).second;

        SDL_SetRenderTarget(rend, tex);
        auto ret = drawRoad(*road);
        if(ret != NoError) {
            return ret;
        }
        
        SDL_Rect r = roadToSDLRect(*road);
        SDL_SetRenderTarget(rend, NULL);
        SDL_RenderCopyEx(rend,
                         tex,
                         NULL,
                         &r,
                         0.0,
                         NULL,
                         SDL_FLIP_NONE);
    }
    return NoError;
}


Vis2d::Error Vis2d::drawCars(simulation::Sim &sim) {
    return NoError;
}


Vis2d::Error Vis2d::draw(simulation::Sim &sim) {


    drawBackground();
    drawRoads(sim);
    drawCars(sim);

    /* Render to the window */
//    SDL_SetRenderTarget(rend, NULL);
//    SDL_RenderClear(rend);
//
//    point_pixels_t window_size = getWindowSize();
//    const SDL_Rect window_rect = {
//        0,
//        0,
//        static_cast<int>(window_size.x.v),
//        static_cast<int>(window_size.y.v),
//    };
//
//    
//    SDL_RenderCopyEx(
//        rend,
//        world_tex,
//        &view,
//        &window_rect,
//        0.0,
//        NULL,
//        SDL_FLIP_NONE);

    SDL_RenderPresent(rend);
    return NoError;
}


} /* visualization */
} /* avsim */
