#pragma once
#include <vector>

#include "src/common/geometry.h"
#include "src/roads/road.h"

extern "C" {
#include "src/vehicles/simple_car.h"
}

namespace avsim {
namespace simulation {


class Sim {
public:
    using RoadSegmentCollection = 
        std::vector<std::shared_ptr<roads::RoadSegment>>;
    using IntersectionCollection =
        std::vector<std::shared_ptr<roads::Intersection>>;
    using CarCollection = 
        std::vector<std:shared_ptr<car_t>>;


    enum Action {
        SimQuit,
        SimContinue,
    };

    Sim() : _paused(false) {}
    ~Sim() {}

    void paused(bool p) { _paused = p; }
    bool paused() const { return _paused; }

    RoadSegmentCollection roads;
    IntersectionCollection intersections;
    CarCollection cars;

private:
    bool _paused;
    rect_meters_t _dim;
};

} /* simulation */
} /* avsim */
