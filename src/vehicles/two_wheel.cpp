#include <math.h>

#include "src/common/types.h"
#include "src/common/ctypes.h"
#include "src/vehicles/two_wheel.h"

namespace avsim {
namespace vehicles {

void TwoWheel::tick() {
    common::PointMeters location(midpoint());

    common::PointMeters orientation(
        {std::cos(rotation().v)},
        {std::sin(rotation().v)});

    common::PointMeters turn_orientation(
        {std::cos(rotation().v + _steer_angle.v)},
        {std::sin(rotation().v + _steer_angle.v)});


    meters_t half_base = {_wheel_base.v / 2.0};

    common::PointMeters front_wheel = location +
        (orientation * half_base);

    common::PointMeters rear_wheel = location -
        (orientation * half_base);

    //TODO dt!!
    meters_t d = {velocity().v * 0.1};

    front_wheel += turn_orientation * d;
    rear_wheel += orientation * d;

    location =
        (front_wheel + rear_wheel) / meters_t({2.0});

    midpoint({.x=location.x(), .y=location.y()});
    rotation({std::atan2(
        front_wheel.y().v - rear_wheel.y().v,
        front_wheel.x().v - rear_wheel.x().v
    )});
    //TODO rotation change
    //TODO update velocty, acc, jerk

}

} /* vehicles */
} /* avsim */
