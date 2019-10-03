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
        _velocity({0}),
        _acceleration({0}),
        _jerk({0})
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

    std::shared_ptr<common::Trajectory> targetTraj() const { return _target_traj; }
    void targetTraj(std::shared_ptr<common::Trajectory> v) { _target_traj = v; }

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
    std::shared_ptr<common::Trajectory> _target_traj;
};

} /* vehicles */
} /* avsim */
