#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#include <car.h>



static void apply_dynamics(car_t *car) {
    if(car == NULL) return;
    
    car->spd += car->acc;
    if(car->spd > car->max_spd) {
        car->spd = car->max_spd;
    }

    car->pos += car->spd;
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
