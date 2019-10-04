#pragma once

#include "src/common/types.h"
#include "src/common/ctypes.h"
#include "src/vehicles/vehicle.h"
#include "src/vehicles/damn.h"

namespace avsim {
namespace vehicles {


class TwoWheel :
    public Vehicle,
    public Damn<common::Trajectory>
{
public:
    TwoWheel() : Vehicle(), Damn() {}

    TwoWheel(const TwoWheel& other) :
        Vehicle(other),
        Damn(other),
        _wheel_base(other._wheel_base),
        _steer_angle(other._steer_angle)
    {}


    void tick() override;
    void updateFrame();
    virtual common::Trajectory holdVote();

    meters_t wheelBase() const { return _wheel_base; }
    void wheelBase(meters_t v) { _wheel_base = v; }

    radians_t steerAngle() const { return _steer_angle; }
    void steerAngle(radians_t v) { _steer_angle = v; }

    common::Trajectory predictTrajectory(
        size_t n_ticks,
        radians_t steer_angle,
        meters_t jerk);


protected:
    meters_t _wheel_base;
    radians_t _steer_angle;
};

} /* vehicles */
} /* avsim */
