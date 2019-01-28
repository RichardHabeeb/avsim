#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#include <util.h>
#include <car.h>
#include <road.h>


static void correct_car_pos(road_t *road, car_t *car) {
    car->pos %= road->length;
}


void build_sensor_view(car_t *car, road_t *road, sensor_view_t *view) {
    view->left  = sub_until_zero(car->lane, car->side_sensor_range);
    view->right = min(car->lane + car->side_sensor_range, road->num_lanes);
    view->front = (car->pos + car->front_sensor_range)%road->length;
    view->back  = sub_mod(car->pos, car->rear_sensor_range + car->length, road->length);
}



car_t * apply_car_sensors(road_t *road, car_t *car) {
    sensor_view_t view;
    build_sensor_view(car, road, &view);

    car_t * sensed_list = NULL;
    for(uint32_t i = 0; i < road->num_cars; i++) {
        car_t * c = &road->cars[i];

        //TODO handle looping
        if(     c != car &&
                c->lane >= view.left &&
                c->lane <= view.right &&
                ((c->pos >= view.back && sub_mod(c->pos, c->length, road->length) <= view.front) ||
                (view.front <= view.back && c->pos >= view.back) ||
                (view.front <= view.back && sub_mod(c->pos, c->length, road->length) <= view.front) ||
                (view.front <= view.back && c->pos <= view.front && sub_mod(c->pos, c->length, road->length) >= view.back)))
        {
            c->sensor_list_next = sensed_list;
            sensed_list = c;
        }
    }
    return sensed_list;
}

void road_tick(road_t *road) {
    if(road == NULL) return;

    for(uint32_t i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];

        car_tick(car, apply_car_sensors(road, car));
        correct_car_pos(road, car);
    }
}
