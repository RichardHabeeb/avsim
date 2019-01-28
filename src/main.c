#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <unistd.h>
#include <time.h>
#include <string.h>
#include <SDL2/SDL.h>

#include <config.h>
#include <draw.h>
#include <road.h>
#include <car.h>


static road_t single_road;
static car_t cars[CFG_NUM_CARS];


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

static void setup_single_road() {
    single_road.num_lanes = CFG_SINGLE_NUM_LANES;
    single_road.length = CFG_SINGLE_LEN_M * CFG_SPACE_SCALE;
    single_road.num_cars = CFG_NUM_CARS;
    single_road.cars = cars;
}

void setup_car_params(car_t * car, road_t * road) {
    memset(car, 0, sizeof(car_t));
    car->length  = (CFG_CAR_MIN_LEN_M      + rand()%(CFG_CAR_MAX_LEN_M - CFG_CAR_MIN_LEN_M))*CFG_SPACE_SCALE;
    car->spd     = (CFG_CAR_MIN_SPD_MS     + rand()%(CFG_CAR_MAX_SPD_MS - CFG_CAR_MIN_SPD_MS))*CFG_SPACE_SCALE;
    car->top_spd = (CFG_CAR_MIN_TOP_SPD_MS + rand()%(CFG_CAR_MAX_TOP_SPD_MS - CFG_CAR_MIN_TOP_SPD_MS))*CFG_SPACE_SCALE;
    car->lane    = (rand()%road->num_lanes);
    car->pos     = (rand()%road->length);
    car->front_sensor_range = CFG_CAR_FRONT_RANGE_M*CFG_SPACE_SCALE;
    car->rear_sensor_range = CFG_CAR_REAR_RANGE_M*CFG_SPACE_SCALE;
    car->side_sensor_range = CFG_CAR_SIDE_RANGE_LANES;
    car->top_acc = CFG_CAR_TOP_ACC*CFG_SPACE_SCALE;
    car->top_dec = CFG_CAR_TOP_DEC*CFG_SPACE_SCALE;
}


int main(int argc, char* argv[]) {
    srand(time(NULL));
    setup_draw();

#ifdef CFG_SINGLE_ROAD
    setup_single_road();

    for(uint32_t i = 0; i < CFG_NUM_CARS; i++) {
        setup_car_params(&single_road.cars[i], &single_road);
    }
#endif

    while(tick()) {
        usleep(CFG_TICK_SLP_US);
    }

    cleanup_draw();
}

