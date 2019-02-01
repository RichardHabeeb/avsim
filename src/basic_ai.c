#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

#include <config.h>
#include <util.h>
#include <basic_ai.h>
#include <car.h>



plan_type_t basic_ai_planner(
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

        /* Search our lane or changing lane cars */
        if( nearby_car->lane == car->lane || 
            (nearby_car->lane+1 == car->lane && nearby_car->r_blinker) ||
            (nearby_car->lane == car->lane+1 && nearby_car->l_blinker)) 
        {
            
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
                    pos_diff < car->front_sensor_range && /* This needs to be revised somehow */
                    pos_diff < d_min*2) 
            {
                if(pos_diff < d_min*3/2) {
                    target_spd = nearby_car->spd/2; /* slow way down to get out */
                } else {
                    target_spd = min(target_spd, nearby_car->spd);
                }
            }

        }
        
        if(         nearby_car->lane+1 == car->lane || 
                    (nearby_car->lane == car->lane && nearby_car->l_blinker) ||
                    (nearby_car->lane+2 == car->lane && nearby_car->r_blinker)) 
        {
            left_lane_free = false; //TODO calculate safe space
        } else if(  nearby_car->lane == car->lane+1 || 
                    (nearby_car->lane == car->lane && nearby_car->r_blinker) ||
                    (nearby_car->lane == car->lane+2 && nearby_car->l_blinker)) 
        {
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
