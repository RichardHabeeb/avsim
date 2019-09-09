#pragma once

#include <stdint.h>

#include "src/vehicles/simple_car.h"

plan_type_t basic_ai_planner(const car_t *, const sensor_reading_t *, uint32_t num_readings, plan_action_t *);
