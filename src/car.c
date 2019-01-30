#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include <util.h>
#include <config.h>
#include <car.h>

#include <stdio.h>


static void apply_dynamics(car_t *car) {
    //TODO realism
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
    //TODO make this better with PID or something
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
    //TODO relocate to a more modular location
    //TODO add road map/geometry to driver function
    uint32_t i;
    plan_type_t ret = PLAN_NONE;
    bool left_lane_free = true;
    bool right_lane_free = true;

    
    /* Look for slower cars/obstructions in front of us */
    uint32_t target_spd = car->top_spd;

    for(i = 0; i < num_readings; i++) {
        /* We only know about cars now */
        if(readings[i].type != SENSOR_READING_CAR) continue;

        const sensor_reading_car_t * nearby_car = &readings[i].data.car;

        /* Search our lane */
        if(nearby_car->lane == car->lane) {
            
            int32_t pos_diff = sub_mod(nearby_car->pos, nearby_car->len + car->pos, CFG_SINGLE_LEN_M*CFG_SPACE_SCALE);

            /* From Mobileye 2017 Paper */
            int32_t d_min = 
                car->spd/CFG_TICKS_PER_S + 
                CFG_CAR_TOP_ACC*CFG_SPACE_SCALE/(2*CFG_TICKS_PER_S*CFG_TICKS_PER_S) +
                (int32_t)((car->spd + CFG_CAR_TOP_ACC*CFG_SPACE_SCALE/CFG_TICKS_PER_S)*
                (car->spd + CFG_CAR_TOP_ACC*CFG_SPACE_SCALE/CFG_TICKS_PER_S))/
                (-CFG_CAR_TOP_DEC*CFG_SPACE_SCALE) - /* here I set min-brake to 1/2 * max-brake */
                (int32_t)nearby_car->spd*nearby_car->spd/(-2*CFG_CAR_TOP_DEC*CFG_SPACE_SCALE);

            if(     target_spd > nearby_car->spd/2 &&
                    pos_diff < car->front_sensor_range && 
                    pos_diff < d_min*2) 
            {
                if(pos_diff < d_min*3/2) {
                    target_spd = nearby_car->spd/2; /* slow way down to get out */
                } else {
                    target_spd = min(target_spd, nearby_car->spd);
                }
            }

        } else if(nearby_car->lane == car->lane-1) {
            left_lane_free = false; //TODO calculate safe space
        } else if(nearby_car->lane == car->lane+1) {
            right_lane_free = false;
        }
    }


    if(target_spd < car->top_spd && car->lane_change_remaining_ticks == 0) {

        if(car->lane > 0 && left_lane_free) {
            target_spd = car->top_spd;
            ret |= PLAN_CHANGE_LANE;
            action->target_lane = car->lane-1;
        } else if(car->lane < CFG_SINGLE_NUM_LANES-1 && right_lane_free) {
            target_spd = car->top_spd;
            ret |= PLAN_CHANGE_LANE;
            action->target_lane = car->lane+1;
        }
    }

    ret |= PLAN_CHANGE_SPD;
    action->target_spd = target_spd; 
    
    return ret;
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
