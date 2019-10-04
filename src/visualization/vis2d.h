#pragma once

#include <vector>
#include <SDL2/SDL.h>

#include "src/visualization/visualization.h"
#include "src/roads/segment.h"
#include "src/simulation/sim.h"
#include "src/common/ctypes.h"
#include "src/vehicles/vehicle.h"


namespace avsim {
namespace visualization {

class Vis2d : public Visualization {
public:
    using RoadTexPair = std::pair<
        SDL_Texture *,
        std::shared_ptr<roads::RoadSegment>>;
    using IntersectionTexPair = std::pair<
        SDL_Texture *,
        std::shared_ptr<roads::Intersection>>;
    using CarTexPair = std::pair<
        SDL_Texture *,
        std::shared_ptr<vehicles::Vehicle>>;

	Vis2d() = default;
	~Vis2d();

	Error setup(simulation::Sim &sim);
	Error draw(simulation::Sim &sim);

	void setScale(double s);
	void setRotation(uint16_t r);
	void setTranslation(point_pixels_t s);
    double getScale();
	uint16_t getRotation();
	point_pixels_t getTranslation();

    point_pixels_t getWindowSize();

private:

    Error drawBackground();
    Error drawRoad(
        roads::RoadSegment &road);

    Error drawRoads(simulation::Sim &);
    Error drawIntersections(simulation::Sim &);
    Error drawCars(simulation::Sim &);

    void drawLaneStripes(
        SDL_Rect &stripe,
        SDL_Rect &road_surface,
        pixels_t lane_height_px,
        size_t num);
    void drawCenterStripes(
        SDL_Rect &road_surface,
        pixels_t stripe_h,
        pixels_t y_offset);

    SDL_Point * trajToSDLPoints(
        const common::Trajectory& traj);


    constexpr pixels_t toPixels(meters_t m) const
    {
        return {
            static_cast<decltype(pixels_t::v)>(
                m.v * _pixels_per_meter)
        };
    }

    constexpr SDL_Point toSDLPoint(const common::PointMeters &p) const {
        return {
            .x = static_cast<int>(toPixels(p.x()).v + _world_origin.x.v),
            .y = static_cast<int>(toPixels(p.y()).v + _world_origin.y.v),
        };
    }


    constexpr SDL_Rect toSDLRect(const common::RectMeters &r) const
    {
        return {
            .x = static_cast<int>(toPixels(r.left()).v + _world_origin.x.v),
            .y = static_cast<int>(toPixels(r.top()).v + _world_origin.y.v),
            .w = static_cast<int>(toPixels(r.width()).v),
            .h = static_cast<int>(toPixels(r.height()).v),
        };
    }


    /* Number of pixels in a meter on the world frame */
    double _pixels_per_meter;

    point_pixels_t _world_origin;
    double _world_scale;

    SDL_Window *window;
    SDL_Renderer *rend;

    pixels_t _world_tile_size;
    std::vector<std::vector<SDL_Texture *>> _world_tiles;

    std::vector<RoadTexPair> _roads;
    std::vector<IntersectionTexPair> _intersections;
    std::vector<CarTexPair> _cars;
};

} /* visualization */
} /* avsim */
