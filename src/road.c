#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#include <car.h>
#include <road.h>


static void correct_car_pos(road_t *road, car_t *car) {
    car->pos %= road->length;
}

static inline uint32_t sub_until_zero(uint32_t a, uint32_t b) {
    return (b <= a) ? a - b : 0; 
}

static uint32_t sub_mod(uint32_t a, uint32_t b, uint32_t m) {
    return (a >= b) ? a - b : m - b + a;
}

void build_sensor_view(car_t *car, road_t *road, sensor_view_t *view) {
    view->l = sub_until_zero(car->lane, car->side_sensor_range);
    view->r = car->lane + car->side_sensor_range;
    view->f = (car->pos + car->front_sensor_range)%road->length;
    view->b = sub_mod(car->pos, car->rear_sensor_range + car->length, road->length);
}



car_t * apply_car_sensors(road_t *road, car_t *car) {
    sensor_view_t view;
    build_sensor_view(car, road, &view);

    //for(uint32_t i = 0; i < road->num_cars; i++) {
    //    
    //}
    return NULL;
}

void road_tick(road_t *road) {
    if(road == NULL) return;

    for(uint32_t i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];

        car_tick(car);
        correct_car_pos(road, car);
    }
}
