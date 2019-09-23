#pragma once

#include <vector>
#include <SDL2/SDL.h>

#include "src/visualization/visualization.h"
#include "src/roads/segment.h"
#include "src/simulation/sim.h"
#include "src/common/ctypes.h"


namespace avsim {
namespace visualization {

class Vis2d : public Visualization {
public:
    using RoadTexPair = std::pair<SDL_Texture *, std::shared_ptr<roads::RoadSegment>>;

	Vis2d() = default;
	~Vis2d();

	Error setup(simulation::Sim &sim);
	Error draw(simulation::Sim &sim);
	Error mapPointToDrawnObject(simulation::Sim &sim, SDL_Point, car_t **, roads::RoadSegment **);

	void setScale(double s);
	void setRotation(uint16_t r);
	void setTranslation(SDL_Point s);
    double getScale();
	uint16_t getRotation();
	SDL_Point getTranslation();

    point_pixels_t getWindowSize(); 

private:

    Error drawRoad(
        roads::RoadSegment &road);

    constexpr pixels_t toPixels(meters_t m) const
    {
        return {
            static_cast<decltype(pixels_t::v)>(
                m.v * _pixels_per_meter)
        };
    }

    constexpr SDL_Rect roadToSDLRect(roads::RoadSegment &r) const 
    {
        return {
            .x = static_cast<int>(toPixels(r.x()).v),
            .y = static_cast<int>(toPixels(r.y()).v),
            .w = static_cast<int>(toPixels(r.width()).v),
            .h = static_cast<int>(toPixels(r.height()).v),
        };
    }

    /* Number of pixels in a meter on the world frame */
    double _pixels_per_meter;

    double _view_scale;
    double _view_angle;
    SDL_Rect _default_view;
    SDL_Rect view;

    SDL_Window *window;
    SDL_Renderer *rend;
    SDL_Texture *world_tex;
    std::vector<RoadTexPair> road_tex;
};

} /* visualization */
} /* avsim */
