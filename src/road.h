#pragma once
#include <stdbool.h>
#include <stddef.h>
#include <car.h>

typedef struct road {
    uint32_t num_lanes;
    uint32_t length;
    bool loop;
    car_t *cars;
    uint32_t num_cars;
    //pair of interections
} road_t;


void road_tick(road_t *);
void build_sensor_view(car_t *car, road_t *road, sensor_view_t *view);
bool collision_check(road_t *, car_t *);
