#pragma once

#include <stdint.h>


typedef struct road {
    uint32_t num_lanes;
    uint32_t length;
    bool loop;
    //pair of interections
    //list of cars
} road_t;


