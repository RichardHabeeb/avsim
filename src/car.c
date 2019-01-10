#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#include <car.h>

void car_tick(car_t *car) {
    if(car == NULL) return;
    
    car->spd += car->acc;
    if(car->spd > car->max_spd) {
        car->spd = car->max_spd;
    }

    car->pos += car->spd;
}
