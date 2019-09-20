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

class RoadSegment : public common::Tickable<void> {
public:
    Lane::LaneCollection forward_lanes;
    Lane::LaneCollection opposite_lanes;

    RoadSegment() = default;
    ~RoadSegment() {};

    meters_t height() const { return _dim.height; }
    void height(meters_t v) { _dim.height = v; }

    meters_t width() const { return _dim.width; }
    void width(meters_t v) { _dim.width = v; }

    /* alias of width */
    meters_t length() const { return _dim.width; }
    void length(meters_t v) { _dim.width = v; }

    point_meters_t midpoint() const { return _dim.midpoint; }
    void midpoint(point_meters_t &v) { _dim.midpoint = v; }

    meters_t x() const { return _dim.midpoint.x; }
    void x(meters_t v) { _dim.midpoint.x = v; }

    meters_t y() const { return _dim.midpoint.y; }
    void y(meters_t v) { _dim.midpoint.y = v; }
    

    rect_meters_t dim() const { return _dim; }
    void dim(rect_meters_t &v) { _dim = v; }

    radians_t rotation() const { return _rotation; }
    void rotation(radians_t v) { _rotation = v; }

    size_t lanes() const { 
        return forward_lanes.size() + opposite_lanes.size();
    }

    void lanes(size_t forward, size_t opposite);

    void tick() {}

protected:
    rect_meters_t _dim;

    meters_t _velocity_max;
    radians_t _rotation;
};

class Intersection : public common::Tickable<void> {
public:
    using RoadSegmentCollection =
        std::vector<std::shared_ptr<RoadSegment>>;
    
    RoadSegmentCollection roads;

    void tick() {}
};


} /* roads */
} /* avsim */

