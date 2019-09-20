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

	void setScale(point_int64_t s);
	void setRotation(uint16_t r);
	void setTranslation(SDL_Point s);
	point_int64_t getScale();
	uint16_t getRotation();
	SDL_Point getTranslation();

    point_pixels_t getWindowSize(); 

	static const int64_t ScaleMax;
	
private:

    Error drawRoad(
        roads::RoadSegment &road);

    constexpr pixels_t toPixels(meters_t m) const
    {
        return {
            static_cast<decltype(pixels_t::v)>(m.v * 5.0)
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


    SDL_Window *window;
    SDL_Renderer *rend;
    SDL_Texture *world_tex;
    std::vector<RoadTexPair> road_tex;
    SDL_Rect view;
    float view_angle;
};

} /* visualization */
} /* avsim */
