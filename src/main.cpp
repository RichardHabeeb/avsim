#include <iostream>
#include <random>
#include <ctime>
#include <memory>
#include <time.h>
#include <SDL2/SDL.h>

#include "src/simulation/sim.h"
#include "src/visualization/vis2d.h"
#include "src/common/config.h"
#include "src/roads/segment.h"

extern "C" {
#include "src/vehicles/simple_car.h"
#include "src/planner/basic_ai.h"
}


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
                car_t *clicked_car = NULL;
                roads::RoadSegment *clicked_road = NULL;
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
                auto translation = vis.getTranslation();
                auto scale = vis.getScale();
                translation.x.v += (e.motion.x - prev_mouse_pos.x)/scale;
                translation.y.v += (e.motion.y - prev_mouse_pos.y)/scale;
                vis.setTranslation(translation);
            }

            prev_mouse_pos.x = e.motion.x;
            prev_mouse_pos.y = e.motion.y;

        } else if(e.type == SDL_MOUSEWHEEL) {
            double s = vis.getScale();
            if(e.wheel.y > 0) {
                s += 0.025;
            } else {
                s -= 0.025;
            }
            vis.setScale(s);
        } else if(e.type == SDL_WINDOWEVENT) {
            switch(e.window.event) {
                case SDL_WINDOWEVENT_RESIZED:
                case SDL_WINDOWEVENT_SIZE_CHANGED:
                    vis.setScale(vis.getScale());
                    vis.setTranslation(vis.getTranslation());
                    break;
                default:
                    break;
            }
        }
    }
    return simulation::Sim::Continue;
}


simulation::Sim::Action tick(simulation::Sim &sim, visualization::Vis2d &vis) {

    if(handle_events(sim, vis) == simulation::Sim::Quit) {
        return simulation::Sim::Quit;
    }

    sim.tick();
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
        road->opposite_lanes.push_back(
            std::make_shared<roads::Lane>());
    }
    road->width({CFG_SINGLE_LEN_M});
    road->height({(double)CFG_SINGLE_LANE_HEIGHT_M * road->lanes()});
    road->x({50});
    road->y({50});

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
    if(vis.setup(sim) != visualization::Vis2d::NoError) {
        return -1;
    }

    do {
        clock_t start = clock();
        if(tick(sim, vis) == simulation::Sim::Quit) {
            break;
        }
        clock_t end = clock();

        nanoseconds_t tick_runtime = 
            {(end - start) * 1000000000L / CLOCKS_PER_SEC};

        timespec t = {
            .tv_sec = 0,
            .tv_nsec =
                default_cfg.tick_duration.v - tick_runtime.v,
        };
        nanosleep(&t, NULL);
    } while(1);

	return 0;
}

