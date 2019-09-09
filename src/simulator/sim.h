#pragma once

#include <stdint.h>
#include <stdbool.h>

#include "src/roads/loop.h"
#include "src/vehicles/simple_car.h"


typedef enum {
    SIM_QUIT,
    SIM_CONTINUE
} sim_action_t;

typedef struct model {
    road_t *roads;
    uint32_t num_roads;
    car_t *cars;
    uint32_t num_cars;
} model_t;

typedef struct sim {
    model_t model;
    bool paused;    
} sim_t;
