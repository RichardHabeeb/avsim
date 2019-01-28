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


plan_type_t driver_control(car_t * car, sensor_reading_t *readings, uint32_t num_readings, plan_action_t * action) {
    //TODO relocate to a more modular location
    plan_type_t ret = PLAN_NONE;
    
    /* Look for slower cars/obstructions in front of us */
    uint32_t target_spd = car->top_spd;

    for(uint32_t i = 0; i < num_readings; i++) {
        if( readings[i].type == SENSOR_READING_CAR &&
            readings[i].data.car.lane == car->lane) 
        {
            
            int32_t spd_diff = car->spd - readings[i].data.car.spd;
             //TODO add road map/geometry to driver function
            int32_t next_tick_predict_pos = (readings[i].data.car.pos + 
                (readings[i].data.car.spd + CFG_CAR_TOP_DEC*CFG_SPACE_SCALE/CFG_TICKS_PER_S)/CFG_TICKS_PER_S)%(CFG_SINGLE_LEN_M*CFG_SPACE_SCALE);
            
            int32_t safety_zone = sub_mod(next_tick_predict_pos, readings[i].data.car.len + car->pos, CFG_SINGLE_LEN_M*CFG_SPACE_SCALE);
            
            int32_t pos_diff = sub_mod(readings[i].data.car.pos, readings[i].data.car.len + car->pos, CFG_SINGLE_LEN_M*CFG_SPACE_SCALE);

            //printf("Car in front %i %i\n", spd_diff, pos_diff);
            if(spd_diff > 0 && pos_diff < car->front_sensor_range) {
                target_spd = readings[i].data.car.spd;
            }

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
        car->r_blinker = false;
        car->l_blinker = false;
    }

    if(plan & PLAN_CHANGE_SPD) {
        speed_control_loop(car, action.target_spd);
    }

    if(plan & PLAN_CHANGE_LANE) {

    }

    apply_dynamics(car);
}
