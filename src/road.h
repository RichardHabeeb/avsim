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
