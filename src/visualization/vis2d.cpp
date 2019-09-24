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
        auto road_texture = SDL_CreateTexture(
            rend,
            SDL_PIXELFORMAT_RGBA8888,
            SDL_TEXTUREACCESS_TARGET,
            toPixels(road->width()).v,
            toPixels(road->height()).v);
        if(road_texture == NULL) {
            std::cout << "Error: road texture invalid: "
                << toPixels(road->width()).v << "x"
                << toPixels(road->height()).v << "\n";
            return InternalError;
        }

        SDL_SetRenderTarget(rend, road_texture);
        auto ret = drawRoad(*road);
        if(ret != NoError) {
            return ret;
        }
        _roads.push_back({road_texture, road});
    }

    _intersections.reserve(sim.intersections.size());
    for(auto it = sim.intersections.begin();
        it != sim.intersections.end(); ++it)
    {
        auto inter = *it;
        auto inter_texture = SDL_CreateTexture(
            rend,
            SDL_PIXELFORMAT_RGBA8888,
            SDL_TEXTUREACCESS_TARGET,
            toPixels(inter->width()).v,
            toPixels(inter->height()).v);
        if(inter_texture == NULL) {
            std::cout << "Error: road texture invalid: "
                << toPixels(inter->width()).v << "x"
                << toPixels(inter->height()).v << "\n";
        }
        SDL_SetRenderTarget(rend, inter_texture);
        SDL_SetRenderDrawColor(rend, 0x30, 0x30, 0x30, 0xFF);
        SDL_RenderClear(rend);

        _intersections.push_back({inter_texture, inter});
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



void Vis2d::drawLaneStripes(
    SDL_Rect &stripe,
    SDL_Rect &road_surface,
    pixels_t lane_height_px,
    size_t num)
{
    SDL_SetRenderDrawColor(rend, 0xFF, 0xFF, 0x55, 0xFF);

    for(size_t i = 0; i < num; ++i) {

        while(stripe.x < road_surface.x+road_surface.w) {
            SDL_RenderFillRect(rend, &stripe);
            stripe.x += 2*stripe.w;
        }

        stripe.x = 0;
        stripe.y += lane_height_px.v;
    }
}

void Vis2d::drawCenterStripes(
    SDL_Rect &road_surface,
    pixels_t stripe_h,
    pixels_t y_offset)
{
    SDL_SetRenderDrawColor(rend, 0xFF, 0xFF, 0x55, 0xFF);

    /* Draw center stripes */
    SDL_Rect center;
    center.w = road_surface.w;
    center.h = stripe_h.v;
    center.x = 0;
    center.y = y_offset.v - 2*center.h;

    SDL_RenderFillRect(rend, &center);

    center.y = road_surface.h/2 + 2*center.h;
    SDL_RenderFillRect(rend, &center);
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


    pixels_t lane_height_px = {
        road_height_px.v /
        static_cast<decltype(pixels_t::v)>(road.lanes())
    };

    pixels_t stripe_h = toPixels({0.2});

    SDL_Rect stripe = {
        .x = static_cast<int>(0),
        .y = static_cast<int>(lane_height_px.v),
        .w = static_cast<int>(toPixels({2}).v),
        .h = static_cast<int>(stripe_h.v),
    };

    /* Draw stripes */
    drawLaneStripes(stripe, road_surface, lane_height_px, road.forward_lanes.size()-1);

    /* Two-way road */
    if(road.opposite_lanes.size() > 0)
    {
        drawCenterStripes(road_surface, stripe_h, {stripe.y});
    }

    stripe.y += lane_height_px.v;
    drawLaneStripes(stripe, road_surface, lane_height_px, road.opposite_lanes.size()-1);

    return NoError;
}



Vis2d::Error Vis2d::drawRoads(simulation::Sim &sim) {

    /* Render roads into the world */
    for(auto it = _roads.begin(); it != _roads.end(); ++it)
    {
        auto tex = (*it).first;
        auto road = (*it).second;

        /* blit the texture to the world */
        SDL_Rect r = toSDLRect(*road);
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


Vis2d::Error Vis2d::drawIntersections(simulation::Sim &sim) {

    for(auto it = _intersections.begin(); it != _intersections.end(); ++it)
    {
        auto tex = (*it).first;
        auto intersection = (*it).second;

        /* blit the texture to the world */
        SDL_Rect r = toSDLRect(*intersection);
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
    auto ret = drawBackground();
    if(ret != NoError) return ret;

    ret = drawRoads(sim);
    if(ret != NoError) return ret;

    ret = drawIntersections(sim);
    if(ret != NoError) return ret;

    ret = drawCars(sim);
    if(ret != NoError) return ret;

    SDL_RenderPresent(rend);
    return NoError;
}


} /* visualization */
} /* avsim */
