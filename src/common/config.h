#pragma once

#include "src/common/ctypes.h"

#ifdef __cplusplus
extern "C" {
#endif

#define CFG_TICK_SLP_US (1000*10)
#define CFG_TICKS_PER_S (1000*1000 / CFG_TICK_SLP_US)
#define CFG_NUM_CARS (40)
#define CFG_SPACE_SCALE (1000)

/* RENDERER PARAMS */
#define CFG_WINDOW_SIZE_X (1200)
#define CFG_WINDOW_SIZE_Y (500)
#define CFG_WORLD_SIZE_X  (CFG_WINDOW_SIZE_X*2)
#define CFG_WORLD_SIZE_Y  (CFG_WINDOW_SIZE_Y*2)


/* CAR PARAMS */
#define CFG_CAR_MIN_LEN_M (4)
#define CFG_CAR_MAX_LEN_M (6)
#define CFG_CAR_MIN_TOP_SPD_MS (15)
#define CFG_CAR_MAX_TOP_SPD_MS (40)
#define CFG_CAR_MIN_SPD_MS (0)
#define CFG_CAR_MAX_SPD_MS (CFG_CAR_MAX_TOP_SPD_MS)
#define CFG_CAR_FRONT_RANGE_M (50)
#define CFG_CAR_REAR_RANGE_M (30)
#define CFG_CAR_SIDE_RANGE_LANES (2)
#define CFG_CAR_TOP_ACC (10)
#define CFG_CAR_TOP_DEC (-20)
#define CFG_CAR_LANE_CHANGE_S (1)
#define CFG_CAR_WIDTH_M (3)

/* SINGLE ROAD SCENARIO SETTINGS */
#define CFG_SINGLE_ROAD
#ifdef CFG_SINGLE_ROAD
#define CFG_SINGLE_NUM_LANES 6
#define CFG_SINGLE_LEN_M 300
#define CFG_SINGLE_LANE_HEIGHT_M 5
#endif /* CFG_SINGLE_ROAD */



typedef struct {
    pixels_t window_width;
    pixels_t window_height;

    meters_t world_width;
    meters_t world_height;

    nanoseconds_t tick_duration;

    size_t max_num_cars;
} config_t;

static const config_t default_cfg = {
    .window_width = {1200L},
    .window_height = {500L},
    .world_width = {5000L},
    .world_height = {5000L},
    .tick_duration = {1000L*1000L*10L},
};



#ifdef __cplusplus
} /* extern C */
#endif
