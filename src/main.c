#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>
#include <string.h>
#include <SDL2/SDL.h>

#include <draw.h>
#include <road.h>
#include <car.h>

#define TICK_DURATION_NS 1000*1000*0
#define ROAD_NUM_LANES 4
#define ROAD_LENGTH 250
#define NUM_CARS 2




/* Single road, for now */
static road_t single_road;
static car_t cars[NUM_CARS];

static bool handle_events() {
    SDL_Event e;
    while(SDL_PollEvent(&e) != 0)
    {
        if(e.type == SDL_QUIT) return false;
        else if(e.type == SDL_KEYDOWN) {
            switch(e.key.keysym.sym) {
                case SDLK_q:
                case SDLK_ESCAPE:
                    return false;
                default:
                    break;
            }
        }
    }
    return true;
}

static bool tick() {
    
    if(handle_events() == false) {
        return false;
    }

    road_tick(&single_road);

    draw(&single_road);

    return true;
}


int main(int argc, char* argv[]) {
    setup_draw();

    single_road.num_lanes = ROAD_NUM_LANES;
    single_road.length = ROAD_LENGTH;
    single_road.num_cars = NUM_CARS;
    single_road.cars = cars;
    memset(cars, 0, sizeof(car_t)*NUM_CARS);
    cars[0].spd = 0;
    cars[0].max_spd = 40;

    cars[1].spd = 10;
    cars[1].max_spd = 40;
    cars[1].lane = 1;
    cars[0].length = 4;
    cars[1].length = 6;
    cars[0].acc=1;

    while(tick()) {
        nanosleep(&(const struct timespec){.tv_sec=1, .tv_nsec=TICK_DURATION_NS}, NULL);
    }

    cleanup_draw();
}

