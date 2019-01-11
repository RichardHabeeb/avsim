#include <stdint.h>
#include <time.h>
#include <string.h>

#include <draw.h>
#include <input.h>
#include <road.h>
#include <car.h>

#define TICK_DURATION_NS 1000*1000*50
#define ROAD_NUM_LANES 4
#define ROAD_LENGTH 10000
#define NUM_CARS 2


/* Single road, for now */
static road_t single_road;
static car_t cars[NUM_CARS];


static bool tick() {
    key_t in_key = pop_input_buf();
    while(in_key != INPUT_BUF_EMPTY) {
        if(in_key == 'q') {
            return FALSE;
        }
        in_key = pop_input_buf();
    }

    road_tick(&single_road);

    draw(&single_road);

    return TRUE;
}


int main(int argc, char* argv[]) {
    setup_draw();

    single_road.num_lanes = ROAD_NUM_LANES;
    single_road.length = ROAD_LENGTH;
    single_road.num_cars = NUM_CARS;
    single_road.cars = cars;
    memset(cars, 0, sizeof(car_t)*NUM_CARS);
    cars[0].spd = 20;
    cars[0].max_spd = 100;

    cars[1].spd = cars[1].max_spd = 80;
    cars[1].lane = 1;
    cars[0].length = 2;
    cars[1].length = 4;
    cars[0].acc=1;

    while(tick()) {
        nanosleep(&(const struct timespec){.tv_sec=0, .tv_nsec=TICK_DURATION_NS}, NULL);
    }

    cleanup_draw();
}

