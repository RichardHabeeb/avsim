#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <unistd.h>
#include <time.h>
#include <string.h>
#include <SDL2/SDL.h>

#include <config.h>
#include <sim.h>
#include <draw.h>
#include <road.h>
#include <car.h>


static sim_action_t handle_events(sim_t *sim, vis_t *vis) {
    static SDL_Point prev_mouse_pos; 
    SDL_Event e;

    while(SDL_PollEvent(&e) != 0)
    {
        if(e.type == SDL_QUIT) {
            return SIM_QUIT;

        } else if(e.type == SDL_KEYDOWN) {
            switch(e.key.keysym.sym) {
                case SDLK_q:
                case SDLK_ESCAPE:
                    return SIM_QUIT;
                case SDLK_SPACE:
                    sim->paused = !sim->paused;
                    break;
                default:
                    break;
            }
        } else if(e.type == SDL_MOUSEBUTTONDOWN) {
            if(e.button.button == SDL_BUTTON_LEFT) {
                car_t * clicked_car = NULL;
                map_point_to_drawn_object(
                        vis,
                        sim,
                        (SDL_Point) { e.button.x, e.button.y },
                        &clicked_car,
                        NULL);
                if(clicked_car != NULL) {
                    clicked_car->selected = !clicked_car->selected;
                }
            }

        } else if(e.type == SDL_MOUSEBUTTONUP) {

        } else if(e.type == SDL_MOUSEMOTION) {
            if((e.motion.state & SDL_BUTTON_RMASK) > 0) {
                SDL_Point translation = get_draw_translation(vis);
                translation.x -= e.motion.x - prev_mouse_pos.x;
                translation.y -= e.motion.y - prev_mouse_pos.y;
                set_draw_translation(vis, translation); 
            }

            prev_mouse_pos.x = e.motion.x;
            prev_mouse_pos.y = e.motion.y;

        } else if(e.type == SDL_MOUSEWHEEL) {
            SDL_Point s = get_draw_scale(vis);
            if(e.wheel.y > 0) {
                s.x -= DRAW_SCALE_MAX/32;
                s.y -= DRAW_SCALE_MAX/32;
            } else {
                s.x += DRAW_SCALE_MAX/32;
                s.y += DRAW_SCALE_MAX/32;
            }
            set_draw_scale(vis, s);
        }
    }
    return SIM_CONTINUE;
}


static bool tick(sim_t *sim, vis_t *vis) {

    if(handle_events(sim, vis) == SIM_QUIT) {
        return SIM_QUIT;
    }

    if(!sim->paused) {
        for(uint32_t i = 0; i < sim->model.num_roads; i++) {
            road_tick(&sim->model.roads[i]);
        }
    }

    draw(vis, sim);

    return SIM_CONTINUE;
}


void setup_car_params(car_t * car, road_t * road) {
    memset(car, 0, sizeof(car_t));
    car->length  = (CFG_CAR_MIN_LEN_M      + rand()%(CFG_CAR_MAX_LEN_M - CFG_CAR_MIN_LEN_M))*CFG_SPACE_SCALE;
    car->top_spd = (CFG_CAR_MIN_TOP_SPD_MS + rand()%(CFG_CAR_MAX_TOP_SPD_MS - CFG_CAR_MIN_TOP_SPD_MS))*CFG_SPACE_SCALE;
    car->lane    = (rand()%road->num_lanes);
    car->front_sensor_range = CFG_CAR_FRONT_RANGE_M*CFG_SPACE_SCALE;
    car->rear_sensor_range = CFG_CAR_REAR_RANGE_M*CFG_SPACE_SCALE;
    car->side_sensor_range = CFG_CAR_SIDE_RANGE_LANES;
    car->top_acc = CFG_CAR_TOP_ACC*CFG_SPACE_SCALE;
    car->top_dec = CFG_CAR_TOP_DEC*CFG_SPACE_SCALE;
    
    do {
        car->pos = (rand()%road->length); //TODO abort on too many attempts
    } while(collision_check(road, car));
}

#ifdef CFG_SINGLE_ROAD
static void setup_single_road(road_t *single_road, car_t *cars) {
    single_road->num_lanes = CFG_SINGLE_NUM_LANES;
    single_road->length = CFG_SINGLE_LEN_M * CFG_SPACE_SCALE;
    single_road->num_cars = CFG_NUM_CARS;
    single_road->cars = cars;
}
#endif

int main(int argc, char* argv[]) {
    static sim_t sim;
    static vis_t vis;

    srand(time(NULL));

#ifdef CFG_SINGLE_ROAD
    sim.model.roads = (road_t *)malloc(sizeof(road_t));
    sim.model.cars = (car_t *)malloc(sizeof(car_t)*CFG_NUM_CARS);
    sim.model.num_roads = 1;
    sim.model.num_cars = CFG_NUM_CARS;

    setup_single_road(sim.model.roads, sim.model.cars);

    for(uint32_t i = 0; i < CFG_NUM_CARS; i++) {
        setup_car_params(&sim.model.cars[i], sim.model.roads);
    }
#endif

    setup_draw(&vis, &sim);

    while(tick(&sim, &vis) == SIM_CONTINUE) {
        usleep(CFG_TICK_SLP_US); //TODO framerate control
    }

    cleanup_draw(&vis);

    free(sim.model.cars);
    free(sim.model.roads);
}

