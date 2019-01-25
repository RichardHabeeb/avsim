#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#include <config.h>
#include <car.h>

#include <stdio.h>

static void apply_dynamics(car_t *car) {
    car->spd += car->acc/CFG_TICKS_PER_S;
    if(car->spd > car->max_spd) {
        car->spd = car->max_spd;
    }

    car->pos += car->spd/CFG_TICKS_PER_S;
}



static void build_sensor_reading_list() {
}


static void driver_control() {

}





void car_tick(car_t *car, car_t *nearby_cars) {
    build_sensor_reading_list();

    driver_control();

    apply_dynamics(car);
}
