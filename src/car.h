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
    uint32_t rear_sensor_range;
    uint32_t side_sensor_range;

    /* Used to build lists of cars in a sensor range */
    struct car *sensor_list_next;
} car_t;


typedef struct sensor_view {
    uint32_t l;
    uint32_t r;
    uint32_t f;
    uint32_t b;
} sensor_view_t;

void car_tick(car_t *);
