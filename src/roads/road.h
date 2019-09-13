#pragma once
#include <vector>

#include "src/common/geometry.h"

namespace avsim {
namespace roads {

class Lane {
public:
    using LaneCollection =
        std::vector<std::shared_ptr<Lane>>;

    LaneCollection sources;
    LaneCollection sinks;
}

class RoadSegment {
public:
    RoadSegment() = default;
    ~RoadSegment() {};

    meters_t length() const { return _dim.length; }
    void length(meters_t v) { _dim.length = v; }

    meters_t width() const { return _dim.width; }
    void width(meters_t v) { _dim.width = v; }

    point_meters_t midpoint() const { return _midpoint; }
    void midpoint(point_meters_t &v) { _dim.midpoint = v; }

    rect_meters_t dim() const { return _dim; }
    void dim(rect_meters_t &v) { _dim = v; }

    radians_t rotation() const { return _rotation; }
    void rotation(radians_t v) { _rotation = v; }


    Lane::LaneCollection forward;
    Lane::LaneCollection opposite;

protected:
    rect_meters_t _dim;

    meters_t _velocity_max;
    radians_t rotation;
}

class Intersection {
public:
    using RoadSegmentCollection =
        std::vector<std::shared_ptr<RoadSegment>>;
    
    RoadSegmentCollection roads;
}



