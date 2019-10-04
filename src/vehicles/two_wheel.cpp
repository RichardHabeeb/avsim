#include <math.h>
#include <iostream>

#include "src/common/types.h"
#include "src/common/ctypes.h"
#include "src/vehicles/two_wheel.h"

namespace avsim {
namespace vehicles {

void TwoWheel::updateFrame() {
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

    double t = tickDuration().v / 1000000000.0;
    meters_t d = {velocity().v * t};

    front_wheel += turn_orientation * d;
    rear_wheel += orientation * d;

    location =
        (front_wheel + rear_wheel) / meters_t({2.0});

    midpoint({.x=location.x(), .y=location.y()});
    rotation({std::atan2(
        front_wheel.y().v - rear_wheel.y().v,
        front_wheel.x().v - rear_wheel.x().v
    )});

    velocity({velocity().v + acceleration().v * t});
    acceleration({acceleration().v + jerk().v * t});
}

void TwoWheel::tick() {
    updateFrame();
    controlTraj(holdVote());
}


common::Trajectory TwoWheel::predictTrajectory(
    size_t n_ticks,
    radians_t steer_angle,
    meters_t jerk)
{
    TwoWheel tmp(*this);
    tmp.tickDuration({tmp.tickDuration().v * 50});
    tmp.steerAngle(steer_angle);
    tmp.jerk(jerk);

    common::Trajectory ret(n_ticks+1);
    ret.points[0] = tmp.midpoint();

    for(size_t i = 0; i < n_ticks; ++i) {
        tmp.updateFrame();
        ret.points[i+1] = tmp.midpoint();
    }

    return ret;
}


common::Trajectory TwoWheel::holdVote() {
    Ballot<common::Trajectory> ballot;

    ballot.options.push_back(predictTrajectory(
        5, { steerAngle().v + 0 }, jerk()));
    ballot.options.push_back(predictTrajectory(
        5, { steerAngle().v + M_PI/4 }, jerk()));
    ballot.options.push_back(predictTrajectory(
        5, { steerAngle().v - M_PI/4 }, jerk()));

    std::vector<int> totals(ballot.options.size(), 0);
    size_t best = 0;

    for(auto it = behaviors.begin();
        it != behaviors.end(); ++it)
    {
        auto result = (*it)->vote(ballot);

        for(size_t i = 0;
            i < result.options.size() &&
            i < ballot.options.size(); ++i)
        {
            totals[i] += result.options[i];
            std::cout << totals[i] << " ";
            best = (totals[i] > totals[best]) ? i : best;
        }
        std::cout << "\n";
    }

    if(best == 1) {
        steerAngle({ steerAngle().v + M_PI/64 });
    }
    if(best == 2) {
        steerAngle({ steerAngle().v - M_PI/64 });
    }

    return ballot.options[best];
}


} /* vehicles */
} /* avsim */
