#include <iostream>
#include <random>
#include <ctime>
#include <memory>
#include <unistd.h>
#include <SDL2/SDL.h>

extern "C" {
#include "src/vehicles/simple_car.h"
#include "src/planner/basic_ai.h"
}

#include "src/simulation/sim.h"
#include "src/visualization/vis2d.h"
#include "src/common/config.h"
#include "src/roads/segment.h"

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
            return simulation::Sim::Quit;

        } else if(e.type == SDL_KEYDOWN) {
            switch(e.key.keysym.sym) {
                case SDLK_q:
                case SDLK_ESCAPE:
                    return simulation::Sim::Quit;
                case SDLK_SPACE:
                    sim.paused(!sim.paused());
                    break;
                default:
                    break;
            }
        } else if(e.type == SDL_MOUSEBUTTONDOWN) {
            if(e.button.button == SDL_BUTTON_LEFT) {
                car_t *clicked_car;
                roads::RoadSegment *clicked_road;
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
            point_int64_t s = vis.getScale();
            if(e.wheel.y > 0) {
                s.x -= visualization::Vis2d::ScaleMax/32;
                s.y -= visualization::Vis2d::ScaleMax/32;
            } else {
                s.x += visualization::Vis2d::ScaleMax/32;
                s.y += visualization::Vis2d::ScaleMax/32;
            }
            vis.setScale(s);
        }
    }
    return simulation::Sim::Continue;
}


simulation::Sim::Action tick(simulation::Sim &sim, visualization::Vis2d &vis) {

    if(handle_events(sim, vis) == simulation::Sim::Quit) {
        return simulation::Sim::Quit;
    }

    if(!sim.paused()) {
        for(auto it = sim.roads.begin(); 
            it != sim.roads.end(); ++it)
        {
            (*it)->tick();
        }
        for(auto it = sim.cars.begin();
            it != sim.cars.end(); ++it)
        {
            //(*it)->tick();
        }
    }

    vis.draw(sim);

    return simulation::Sim::Continue;
}


void setup_car_params(
    car_t &car,
    roads::RoadSegment &road,
    simulation::Sim &sim)
{
    car.length = CFG_SPACE_SCALE * 
        (CFG_CAR_MIN_LEN_M + std::rand() %
            (CFG_CAR_MAX_LEN_M - CFG_CAR_MIN_LEN_M));
    car.top_spd = CFG_SPACE_SCALE * 
        (CFG_CAR_MIN_TOP_SPD_MS + std::rand() %
            (CFG_CAR_MAX_TOP_SPD_MS - CFG_CAR_MIN_TOP_SPD_MS));

    car.lane = (rand()%road.lanes());
    car.front_sensor_range = CFG_CAR_FRONT_RANGE_M*CFG_SPACE_SCALE;
    car.rear_sensor_range = CFG_CAR_REAR_RANGE_M*CFG_SPACE_SCALE;
    car.side_sensor_range = CFG_CAR_SIDE_RANGE_LANES;
    car.top_acc = CFG_CAR_TOP_ACC*CFG_SPACE_SCALE;
    car.top_dec = CFG_CAR_TOP_DEC*CFG_SPACE_SCALE;
    car.planner = basic_ai_planner;
    do {
        //TODO abort on too many attempts
        car.pos = ((double)rand() / RAND_MAX) *
            std::floor(road.length().v);
    } while(sim.collisionCheck() != simulation::Sim::NoCollision);
}

#ifdef CFG_SINGLE_ROAD
static void setup_single_road(simulation::Sim &sim) {
    auto road = std::make_shared<roads::RoadSegment>();

    for(size_t i = 0; i < CFG_SINGLE_NUM_LANES; ++i) {
        road->forward_lanes.push_back(
            std::make_shared<roads::Lane>());
    }
    road->width({CFG_SINGLE_LEN_M});
    road->height({(double)CFG_SINGLE_LANE_HEIGHT_M * road->lanes()});

    sim.roads.push_back(road);
}
#endif

}

int main(int argc, char* argv[]) {
    using namespace avsim;
    static simulation::Sim sim;
    static visualization::Vis2d vis;

    srand(time(NULL));

    sim.cars.reserve(CFG_NUM_CARS);

#ifdef CFG_SINGLE_ROAD
    setup_single_road(sim);
    for(size_t i = 0; i < CFG_NUM_CARS; ++i) {
        auto car = std::make_shared<car_t>();
        setup_car_params(*car, *sim.roads[0], sim);
        sim.cars.push_back(car);
    }
#endif
    vis.setup(sim);

    while(tick(sim, vis) == simulation::Sim::Continue) {
        usleep(CFG_TICK_SLP_US); //TODO framerate control
    }

	return 0;
}

