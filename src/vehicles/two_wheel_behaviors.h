#pragma once

#include <memory>
#include <iostream>

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

        using Seg = std::pair<
            common::PointMeters, common::PointMeters>;

        Seg nearest_seg(
            _vehicle->targetTraj().points[0],
            _vehicle->targetTraj().points[1]);
        //TODO calculate this
//        for(auto it = _target_traj.points.begin();
//            it != _target_traj.points.end(); ++it) {
//
//        }


        for(size_t i = 0; i < ballot.options.size(); ++i) {

            size_t intersect_j = 0;
            auto t = ballot.options[i];
            ret.options[i] = 0;

            for(size_t j = 1;
                j < t.points.size(); ++j)
            {
                if(common::PointMeters::checkSegmentIntersect(
                    nearest_seg,
                    Seg(t.points[j], t.points[j-1])))
                {
                    ret.options[i] += 1;
                    std::cout << "vote!\n";
                } else {

                }
            }

        }
        return ret;
    }
private:
    std::shared_ptr<TwoWheel> _vehicle;
};


} /* behaviors */
} /* vehicles */
} /* avsim */
