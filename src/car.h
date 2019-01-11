#pragma once
#include <stddef.h>
#include <stdint.h>

typedef struct car {
    uint32_t pos;
    uint32_t length;
    uint32_t lane;
    uint32_t spd;
    int32_t acc;
    uint32_t max_spd;
    uint32_t max_acc;
    bool r_blinker;
    bool l_blinker;
    uint32_t front_sensor_range;
    uint32_t side_sensor_range;
} car_t;

void car_tick(car_t *);
