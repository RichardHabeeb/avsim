#pragma once
#include <stddef.h>
#include <stdint.h>


typedef struct car {
    uint32_t pos;
    uint32_t lane;
    uint32_t spd;
    int32_t acc;
    uint32_t max_spd;
    uint32_t max_acc;
    bool r_blinker;
    bool l_blinker;
} car_t;

void car_tick(car_t *);
