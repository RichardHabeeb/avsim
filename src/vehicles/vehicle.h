#pragma once

#include <memory>
#include "src/common/types.h"
#include "src/common/ctypes.h"

namespace avsim {
namespace vehicles {

class Vehicle :
    public common::Tickable<void>,
    public common::RectMeters
{
public:

    Vehicle() :
        common::Tickable<void>(),
        common::RectMeters(),
        _velocity({0}),
        _acceleration({0}),
        _jerk({0})
    {}
    Vehicle(const Vehicle &other) :
        common::Tickable<void>(other),
        common::RectMeters(other),
        _rotation(other._rotation),
        _velocity(other._velocity),
        _max_velocity(other._max_velocity),
        _acceleration(other._acceleration),
        _max_acceleration(other._max_acceleration),
        _jerk(other._jerk),
        _max_jerk(other._max_jerk),
        _target_traj(other._target_traj),
        _control_traj(other._control_traj)
    {}

    virtual ~Vehicle() {}


    /* alias of width */
    meters_t length() const { return _rect.width; }
    void length(meters_t v) { _rect.width = v; }

    radians_t rotation() const { return _rotation; }
    void rotation(radians_t v) { _rotation = v; }

    // TODO saturate values
    meters_t velocity() const { return _velocity; }
    void velocity(meters_t v) { _velocity = v; }

    meters_t acceleration() const { return _acceleration; }
    void acceleration(meters_t v) { _acceleration = v; }

    meters_t jerk() const { return _jerk; }
    void jerk(meters_t v) { _jerk = v; }

    common::Trajectory targetTraj() const { return _target_traj; }
    void targetTraj(common::Trajectory v) { _target_traj = v; }

    common::Trajectory controlTraj() const { return _control_traj; }
    void controlTraj(common::Trajectory v) { _control_traj = v; }

    virtual void tick() = 0;
protected:
    radians_t _rotation;
    meters_t _velocity;
    meters_t _max_velocity;
    meters_t _acceleration;
    meters_t _max_acceleration;
    meters_t _jerk;
    meters_t _max_jerk;

    /* Target trajectory output by the deliberative planner */
    common::Trajectory _target_traj;
    common::Trajectory _control_traj;
};

} /* vehicles */
} /* avsim */
