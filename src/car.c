#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#include <road.h>
#include <car.h>



static void apply_dynamics(car_t *car) {
    if(car == NULL) return;
    
    car->spd += car->acc;
    if(car->spd > car->max_spd) {
        car->spd = car->max_spd;
    }

    car->pos += car->spd;
}




static void driver_control() {

}


void car_tick(car_t *car) {

    driver_control();

    apply_dynamics(car);
}
