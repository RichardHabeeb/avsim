#include <iostream>
#include <random>
#include <ctime>
#include <unistd.h>
#include <SDL2/SDL.h>

extern "C" {
#include "src/common/config.h"
#include "src/roads/loop.h"
#include "src/vehicles/simple_car.h"
#include "src/planner/basic_ai.h"
}

#include "src/simulation/sim.h"
#include "src/visualization/vis2d.h"

namespace avsim {

static simulation::Sim::Action handle_events(
    simulation::Sim &sim,
    visualization::Vis2d &vis)
{
    static SDL_Point prev_mouse_pos;
    SDL_Event e;

    while(SDL_PollEvent(&e) != 0)
    {
        if(e.type == SDL_QUIT) {
            return simulation::Sim::SimQuit;

        } else if(e.type == SDL_KEYDOWN) {
            switch(e.key.keysym.sym) {
                case SDLK_q:
                case SDLK_ESCAPE:
                    return simulation::Sim::SimQuit;
                case SDLK_SPACE:
                    sim.paused(!sim.paused());
                    break;
                default:
                    break;
            }
        } else if(e.type == SDL_MOUSEBUTTONDOWN) {
            if(e.button.button == SDL_BUTTON_LEFT) {
                car_t *clicked_car;
                road_t *clicked_road;
                vis.mapPointToDrawnObject(
                        sim,
                        (SDL_Point) { e.button.x, e.button.y },
                        &clicked_car,
                        &clicked_road);
                if(clicked_car != NULL) {
                    clicked_car->selected = !clicked_car->selected;
                }
            }

        } else if(e.type == SDL_MOUSEBUTTONUP) {

        } else if(e.type == SDL_MOUSEMOTION) {
            if((e.motion.state & SDL_BUTTON_RMASK) > 0) {
                SDL_Point translation = vis.getTranslation();
                translation.x -= e.motion.x - prev_mouse_pos.x;
                translation.y -= e.motion.y - prev_mouse_pos.y;
                vis.setTranslation(translation);
            }

            prev_mouse_pos.x = e.motion.x;
            prev_mouse_pos.y = e.motion.y;

        } else if(e.type == SDL_MOUSEWHEEL) {
            SDL_Point s = vis.getScale();
            if(e.wheel.y > 0) {
                s.x -= visualization::Vis2d::DRAW_SCALE_MAX/32;
                s.y -= visualization::Vis2d::DRAW_SCALE_MAX/32;
            } else {
                s.x += visualization::Vis2d::DRAW_SCALE_MAX/32;
                s.y += visualization::Vis2d::DRAW_SCALE_MAX/32;
            }
            vis.setScale(s);
        }
    }
    return simulation::Sim::SimContinue;
}


bool tick(simulation::Sim &sim, visualization::Vis2d &vis) {

    if(handle_events(sim, vis) == simulation::Sim::SimQuit) {
        return simulation::Sim::SimQuit;
    }

    if(!sim.paused()) {
        for(auto it = sim.roadsBegin(); it != sim.roadsEnd(); ++it) {
            road_tick(&(*it));
        }
    }

    vis.draw(sim);

    return simulation::Sim::SimContinue;
}


void setup_car_params(car_t &car, road_t &road) {
    car.length  = (CFG_CAR_MIN_LEN_M      + std::rand()%(CFG_CAR_MAX_LEN_M - CFG_CAR_MIN_LEN_M))*CFG_SPACE_SCALE;
    car.top_spd = (CFG_CAR_MIN_TOP_SPD_MS + std::rand()%(CFG_CAR_MAX_TOP_SPD_MS - CFG_CAR_MIN_TOP_SPD_MS))*CFG_SPACE_SCALE;
    car.lane    = (rand()%road.num_lanes);
    car.front_sensor_range = CFG_CAR_FRONT_RANGE_M*CFG_SPACE_SCALE;
    car.rear_sensor_range = CFG_CAR_REAR_RANGE_M*CFG_SPACE_SCALE;
    car.side_sensor_range = CFG_CAR_SIDE_RANGE_LANES;
    car.top_acc = CFG_CAR_TOP_ACC*CFG_SPACE_SCALE;
    car.top_dec = CFG_CAR_TOP_DEC*CFG_SPACE_SCALE;
    car.planner = basic_ai_planner;
    do {
        car.pos = (rand()%road.length); //TODO abort on too many attempts
    } while(collision_check(&road, &car));
}

#ifdef CFG_SINGLE_ROAD
static void setup_single_road(simulation::Sim &sim) {
    road_t &single_road = *sim.roadsBegin();
    car_t *cars = &(*sim.carsBegin());
    single_road.num_lanes = CFG_SINGLE_NUM_LANES;
    single_road.length = CFG_SINGLE_LEN_M * CFG_SPACE_SCALE;
    single_road.num_cars = 0;//CFG_NUM_CARS;
    single_road.cars = NULL;// cars;
}
#endif

}

int main(int argc, char* argv[]) {
    static avsim::simulation::Sim sim;
    static avsim::visualization::Vis2d vis;

    srand(time(NULL));

#ifdef CFG_SINGLE_ROAD
    sim.numRoads(1);
    sim.numCars(CFG_NUM_CARS);

    avsim::setup_single_road(sim);

    for(auto it = sim.carsBegin(); it != sim.carsEnd(); ++it) {
        avsim::setup_car_params(*it, *sim.roadsBegin());
    }
#endif
    vis.setup(sim);

    while(avsim::tick(sim, vis) == avsim::simulation::Sim::SimContinue) {
        usleep(CFG_TICK_SLP_US); //TODO framerate control
    }

	return 0;
}

