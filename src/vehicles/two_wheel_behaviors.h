#pragma once

#include "src/common/types.h"
#include "src/vehicles/two_wheel.h"

namespace avsim {
namespace vehicles {
namespace behaviors {

class TurnTowardsTarget :
    public DamnBehavior<common::Trajectory>
{
public:
    TurnTowardsTarget(
        std::shared_ptr<TwoWheel> v)
        : _vehicle(v)
    {}


    virtual Vote vote(Ballot<common::Trajectory> & ballot)
    {
        Vote ret(ballot.options.size());

        for(size_t i = 0; i < ballot.options.size(); ++i) {
            //TODO compare trajectories
            ret.options[i] = 0;
        }
        return ret;
    }
private:
    std::shared_ptr<TwoWheel> _vehicle;
};


} /* behaviors */
} /* vehicles */
} /* avsim */
