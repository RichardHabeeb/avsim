#pragma once

#include "src/common/types.h"
#include "src/common/ctypes.h"
#include "src/vehicles/vehicle.h"
#include "src/vehicles/two_wheel_damn.h"


namespace avsim {
namespace vehicles {

class TwoWheel : public Vehicle {
public:

    void tick() override;

    meters_t wheelBase() const { return _wheel_base; }
    void wheelBase(meters_t v) { _wheel_base = v; }

    radians_t steerAngle() const { return _steer_angle; }
    void steerAngle(radians_t v) { _steer_angle = v; }

protected:
    meters_t _wheel_base;
    radians_t _steer_angle;
    TwoWheelDamn _controller;
};

}
} /* avsim */
