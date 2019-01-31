#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

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
    //TODO handle non-looping roads/intersections
    //TODO improve performance
    sensor_view_t view;
    build_sensor_view(car, road, &view);

    car_t * sensed_list = NULL;
    for(uint32_t i = 0; i < road->num_cars; i++) {
        car_t * c = &road->cars[i];

        if(c != car &&
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


bool collision_check(road_t * road, car_t *car1) {
    //TODO improve perf 
    uint32_t car1_rear = sub_mod(car1->pos, car1->length, road->length);
    
    for(uint32_t i = 0; i < road->num_cars; i++) {
        car_t *car2 = &road->cars[i];
        uint32_t car2_rear = sub_mod(car2->pos, car2->length, road->length);


        if(car1 != car2 && (
           (car1->lane == car2->lane) ||
           (car1->lane+1 == car2->lane && car1->r_blinker) ||
           (car1->lane == car2->lane+1 && car2->r_blinker) || 
           (car1->lane+1 == car2->lane && car2->l_blinker) ||
           (car1->lane == car2->lane+1 && car1->l_blinker) 
           ) && (
           (car1->pos >= car2_rear && car1_rear <= car2->pos) ||
           (car1->pos < car1->length && car2->pos < car1->pos) ||
           (car1->pos < car1->length && car1_rear < car2->pos) ||
           (car2->pos < car2->length && car1->pos < car2->pos) ||
           (car2->pos < car2->length && car2_rear < car1->pos)))
        {
            return true;
        }  
    }

    return false;
}

void road_tick(road_t *road) {
    if(road == NULL) return;

    for(uint32_t i = 0; i < road->num_cars; i++) {
        car_t *car = &road->cars[i];

        car_tick(car, apply_car_sensors(road, car));
        correct_car_pos(road, car);

        if(collision_check(road, car)) {
            printf("COLLISION %i\n", i);
        }
    }
}
