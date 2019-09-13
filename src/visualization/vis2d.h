#pragma once

#include <vector>
#include <SDL2/SDL.h>

#include "src/visualization/visualization.h"

extern "C" {
#include "src/simulation/sim.h"
#include "src/roads/loop.h"
}

namespace avsim {
namespace visualization {

class Vis2d : public Visualization {
public:
	Vis2d() = default;
	~Vis2d();

	Error setup(simulation::Sim &sim);
	Error draw(simulation::Sim &sim);
	Error mapPointToDrawnObject(simulation::Sim &sim, SDL_Point, car_t **, road_t **);

	void setScale(SDL_Point s);
	void setRotation(uint16_t r);
	void setTranslation(SDL_Point s);
	SDL_Point getScale();
	uint16_t getRotation();
	SDL_Point getTranslation();

	static constexpr uint32_t DRAW_SCALE_MAX = 0xFF;
	static constexpr uint32_t DRAW_ROTATION_MAX = 0xFFFF;
	
private:

    Error drawRoad(
        road_t &road,
        uint32_t road_width_px,
        uint32_t road_height_px);

    SDL_Window *window;
    SDL_Renderer *rend;
    SDL_Texture *world_tex;
    std::vector<SDL_Texture *> road_tex;
    std::vector<SDL_Rect> road_dim;
    SDL_Rect view;
    float view_angle;
};

} /* visualization */
} /* avsim */
