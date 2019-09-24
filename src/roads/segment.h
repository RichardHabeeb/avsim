#pragma once
#include <vector>
#include <memory>

#include "src/common/types.h"
#include "src/common/ctypes.h"

namespace avsim {
namespace roads {

class Lane {
public:
    using LaneCollection =
        std::vector<std::shared_ptr<Lane>>;

    LaneCollection sources;
    LaneCollection sinks;
};

class RoadSegment :
    public common::Tickable<void>,
    public common::RectMeters
{
public:
    Lane::LaneCollection forward_lanes;
    Lane::LaneCollection opposite_lanes;

    RoadSegment() = default;
    ~RoadSegment() {};

    /* alias of width */
    meters_t length() const { return _rect.width; }
    void length(meters_t v) { _rect.width = v; }

    radians_t rotation() const { return _rotation; }
    void rotation(radians_t v) { _rotation = v; }

    size_t lanes() const {
        return forward_lanes.size() + opposite_lanes.size();
    }

    void lanes(size_t forward, size_t opposite);

    void tick() {}

protected:

    meters_t _velocity_max;
    radians_t _rotation;
};

class Intersection :
    public common::Tickable<void>,
    public common::RectMeters
{
public:
    using RoadSegmentCollection =
        std::vector<std::shared_ptr<RoadSegment>>;

    RoadSegmentCollection roads;

    void tick() {}
};


} /* roads */
} /* avsim */

