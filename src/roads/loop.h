#pragma once
#include <stdbool.h>
#include <stddef.h>

#include "src/vehicles/simple_car.h"


typedef struct path path_t;
typedef struct lane lane_t;
typedef struct junc junc_t;
typedef struct road road_t;

typedef enum lane_type {
    LANE_EXIT,
    LANE_ENTRANCE
} lane_type_t;

/* A possible path through the road/intersection w/o lane changes */
typedef struct path {
    lane_t *start;
    lane_t *end;
} path_t;

/* Entrance or exit lane for a junction between roads */
typedef struct lane {
    lane_type_t type;
    path_t **paths;
    uint32_t num_paths;
    lane_t *adj_lane;
    junc_t *parent_junc;
} lane_t;

/* Junction between two roads */
typedef struct junc {
    lane_t *lanes;
    uint32_t num_lanes;
    junc_t *adj_junc;
    road_t *parent_road;
} junc_t;

/* Model of a road or intersection */
typedef struct road {
    uint32_t num_lanes; //TODO remove
    uint32_t length; //TODO remove

    //TODO show cars on paths, change to **
    car_t *cars;
    uint32_t num_cars;

    junc_t *juncs;
    uint32_t num_juncs;

    path_t *paths;
    uint32_t num_paths;

    //TODO road type/params/protcols/signs/allowed lane changes

} road_t;


void road_tick(road_t *);
void build_sensor_view(car_t *car, road_t *road, sensor_view_t *view);
bool collision_check(road_t *, car_t *);
