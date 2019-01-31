#pragma once
#include <stddef.h>
#include <stdint.h>

typedef struct car {
    uint32_t pos;
    uint32_t length;
    uint32_t lane;
    uint32_t spd;
    uint32_t top_spd;
    int32_t acc;
    int32_t top_acc;
    int32_t top_dec;
    uint32_t lane_change_remaining_ticks;
    bool r_blinker;
    bool l_blinker;
    uint32_t front_sensor_range;
    uint32_t rear_sensor_range;
    uint32_t side_sensor_range;

    /* Used to build lists of cars in a sensor range */
    struct car *sensor_list_next;

    /* Used for visualization */
    bool selected;
} car_t;


typedef struct sensor_view {
    uint32_t left;
    uint32_t right;
    uint32_t front;
    uint32_t back;
} sensor_view_t;


typedef struct sensor_reading_car {
    uint32_t pos;
    uint32_t len;
    uint32_t lane;
    uint32_t spd;
    uint32_t lane_change_remaining_ticks;
    bool r_blinker;
    bool l_blinker;
} sensor_reading_car_t;

typedef enum sensor_reading_type {
    SENSOR_READING_CAR,
} sensor_reading_type_t; 


typedef struct sensor_reading {
    sensor_reading_type_t type;
    union {
        sensor_reading_car_t car;
    } data;
} sensor_reading_t;



typedef enum plan_type {/* bitmask, for multiple plans */
    PLAN_NONE = 0x00,
    PLAN_CHANGE_SPD = 0x01,
    PLAN_CHANGE_LANE = 0x02,
} plan_type_t;

typedef struct plan_action {
    uint32_t target_spd;
    uint32_t target_lane;
} plan_action_t;


void car_tick(car_t *, car_t * nearby_cars);
