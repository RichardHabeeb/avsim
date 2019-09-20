#pragma once
#include <vector>
#include <memory>

#include "src/common/types.h"
#include "src/common/ctypes.h"
#include "src/roads/segment.h"

extern "C" {
#include "src/vehicles/simple_car.h"
}

namespace avsim {
namespace simulation {



class Sim : public common::Tickable<void> {
public:
    using RoadSegmentCollection = 
        std::vector<std::shared_ptr<roads::RoadSegment>>;
    using IntersectionCollection =
        std::vector<std::shared_ptr<roads::Intersection>>;
    using CarCollection = 
        std::vector<std::shared_ptr<car_t>>;

    enum Collision {
        NoCollision,
        FoundCollision,
    };

    enum Action {
        Quit,
        Continue,
    };

    RoadSegmentCollection roads;
    IntersectionCollection intersections;
    CarCollection cars;

    Sim() : _paused(false) {}
    ~Sim() {}

    void paused(bool p) { _paused = p; }
    bool paused() const { return _paused; }

    Collision collisionCheck() { return NoCollision; }
    void tick();

private:
    bool _paused;
    rect_meters_t _dim;
};

} /* simulation */
} /* avsim */
