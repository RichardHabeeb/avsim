#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>

#include "src/common/util.h"
#include "src/common/config.h"
#include "src/vehicles/simple_car.h"



static void apply_dynamics(car_t *car) {
    car->spd += car->acc/CFG_TICKS_PER_S;
    if(car->spd > car->top_spd) {
        car->spd = car->top_spd;
    }

    car->pos += car->spd/CFG_TICKS_PER_S;

    if(car->lane_change_remaining_ticks == 1) {
        car->lane += car->r_blinker ? 1 : -1;
        car->lane_change_remaining_ticks = 0;
        car->r_blinker = false;
        car->l_blinker = false;
    } else if(car->lane_change_remaining_ticks > 1) {
        car->lane_change_remaining_ticks--;
    }
}

static void speed_control_loop(car_t *car, uint32_t target_speed) {
    /* This could be improved */
    car->acc = (car->spd > target_speed) ? car->top_dec : ((car->spd == target_speed) ? 0 : car->top_acc);
}


static uint32_t build_sensor_reading_list(car_t *nearby_cars, sensor_reading_t *readings) {
    uint32_t readings_len = 0;

    while(nearby_cars != NULL) {
        readings[readings_len].type = SENSOR_READING_CAR;

        memset(&readings[readings_len], 0, sizeof(sensor_reading_t));
        readings[readings_len].data.car.pos = nearby_cars->pos;
        readings[readings_len].data.car.len = nearby_cars->length;
        readings[readings_len].data.car.lane = nearby_cars->lane;
        readings[readings_len].data.car.spd = nearby_cars->spd;
        readings[readings_len].data.car.r_blinker = nearby_cars->r_blinker;
        readings[readings_len].data.car.l_blinker = nearby_cars->l_blinker;

        readings_len++;
        nearby_cars = nearby_cars->sensor_list_next;
    }
    return readings_len;
}


plan_type_t driver_control(
        const car_t * car, 
        const sensor_reading_t * readings,
        uint32_t num_readings,
        plan_action_t * action) 
{
    if(car->planner != NULL) {
        return car->planner(car, readings, num_readings, action);
    }
    else return PLAN_NONE;
}


void car_tick(car_t *car, car_t *nearby_cars) {
    static sensor_reading_t readings[CFG_NUM_CARS];
    plan_action_t action;
    
    uint32_t readings_len = build_sensor_reading_list(nearby_cars, readings);

    plan_type_t plan = driver_control(car, readings, readings_len, &action);

    if(plan == PLAN_NONE) {
        car->acc = 0;
    }

    if(plan & PLAN_CHANGE_SPD) {
        speed_control_loop(car, action.target_spd);
    }

    if(plan & PLAN_CHANGE_LANE) {
        car->lane_change_remaining_ticks = CFG_CAR_LANE_CHANGE_S*CFG_TICKS_PER_S;

        car->l_blinker = car->lane > action.target_lane;
        car->r_blinker = car->lane < action.target_lane;
    }



    apply_dynamics(car);
}
