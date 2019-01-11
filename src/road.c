#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#include <car.h>
#include <road.h>








void road_tick(road_t *road) {
    if(road == NULL) return;

    for(uint32_t i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];

        car_tick(car);

        car->pos %= road->length;
    }
}
