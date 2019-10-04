#pragma once


#include <vector>
#include <iostream>
#include <type_traits>
#include <algorithm>
#include "src/common/ctypes.h"
#include "src/common/config.h"

namespace avsim {
namespace common {


template <typename T>
class Tickable {
public:

    ~Tickable() {}
    Tickable() : _duration(default_cfg.tick_duration) {}
    virtual T tick() = 0;

    nanoseconds_t tickDuration() const{
        return _duration;
    }
    void tickDuration(nanoseconds_t v) { _duration = v; }
private:
    nanoseconds_t _duration;
};


template<typename PointType>
class Point {
public:
    static_assert(std::is_same<
        decltype(PointType::x),
        decltype(PointType::y)>::value);

     using NumericType = decltype(PointType::x);

    ~Point() {}
    Point() : _p({0}) {}
    Point(NumericType x, NumericType y)
        : _p({.x = x, .y = y}) {}
    Point(const Point &p) : _p(p._p) {}
    Point(const PointType& p) : _p(p) {}
    //Point(const Point&& p) : _p(p._p) {}

    NumericType x() const { return _p.x; }
    NumericType y() const { return _p.y; }
    void x(NumericType v) { _p.x = v; }
    void y(NumericType v) { _p.y = v; }


    Point& operator=(const Point& other) {
        _p = other._p;
        return *this;
    }

    Point& operator=(const PointType& other) {
        _p = other;
        return *this;
    }

    Point& operator+=(const Point& other) {
        _p.x.v += other.x().v;
        _p.y.v += other.y().v;
        return *this;
    }

    Point& operator-=(const Point& other) {
        _p.x.v -= other.x().v;
        _p.y.v -= other.y().v;
        return *this;
    }

    Point operator*=(NumericType scalar) {
        _p.x.v *= scalar.v;
        _p.y.v *= scalar.v;
        return *this;
    }

    Point operator/=(NumericType scalar) {
        _p.x.v /= scalar.v;
        _p.y.v /= scalar.v;
        return *this;
    }

    Point operator+(const Point& other) {
        Point tmp(*this);
        tmp += other;
        return tmp;
    }

    Point operator-(const Point& other) {
        Point tmp(*this);
        tmp -= other;
        return tmp;
    }

    Point operator*(NumericType scalar) {
        Point tmp(*this);
        tmp *= scalar;
        return tmp;
    }

    Point operator/(NumericType scalar) {
        Point tmp(*this);
        tmp /= scalar;
        return tmp;
    }


    static bool checkSegmentIntersect(
        const std::pair<Point, Point> &a,
        const std::pair<Point, Point> &b)
    {
        /* Find the four orientations needed
         * for general and special cases */
        auto o1 = checkOrientation(a.first, a.second, b.first);
        auto o2 = checkOrientation(a.first, a.second, b.second);
        auto o3 = checkOrientation(b.first, b.second, a.first);
        auto o4 = checkOrientation(b.first, b.second, a.second);

        return (
            /* general */
            (o1 != o2 && o3 != o4) ||
            /* special */
            (o1 == Colinear &&
                checkColinearOnSegment(b.first, a)) ||
            (o2 == Colinear &&
                checkColinearOnSegment(b.second, a)) ||
            (o3 == Colinear &&
                checkColinearOnSegment(a.first, b)) ||
            (o4 == Colinear &&
                checkColinearOnSegment(a.second, b)));
    }

    static bool checkColinearOnSegment(
        Point q,
        const std::pair<Point,Point> & seg)
    {

        return (
            q._p.x.v <= std::max(
                seg.first._p.x.v, seg.second._p.x.v) &&
            q._p.x.v >= std::min(
                seg.first._p.x.v, seg.second._p.x.v) &&
            q._p.y.v <= std::max(
                seg.first._p.y.v, seg.second._p.y.v) &&
            q._p.y.v >= std::min(
                seg.first._p.y.v, seg.second._p.y.v));
    }

    enum Orientation{
        Colinear,
        Clockwise,
        CounterClockwise
    };
    static Orientation checkOrientation(
        const Point &p,
        const Point &q,
        const Point &r)
    {
        int val = (q._p.y.v - p._p.y.v) *
                  (r._p.x.v - q._p.x.v)
                  -
                  (q._p.x.v - p._p.x.v) *
                  (r._p.y.v - q._p.y.v);

        if (val == 0) return Colinear;

        return (val > 0)? Clockwise : CounterClockwise;
    }

private:
    PointType _p;
};

using PointPixels = Point<point_pixels_t>;
using PointMeters = Point<point_meters_t>;



template<class RectType>
class Rect {
public:
/*
    static_assert(std::is_same<
        decltype(RectType::width),
        decltype(RectType::height)>::value);
    static_assert(std::is_same<
        decltype(RectType::midpoint::x),
        decltype(RectType::midpoint::y)>::value);
    static_assert(std::is_same<
        decltype(RectType::midpoint::x),
        decltype(RectType::width)>::value);
 */
    using NumericType = decltype(RectType::width);
    using PointType = decltype(RectType::midpoint);

    ~Rect() {};
    Rect() : _rect({0}) {}
    Rect(PointType p, NumericType w, NumericType h)
        : _rect({.midpoint=p, .width=w, .height=h}) {}

    Rect(
        NumericType x, NumericType y,
        NumericType w, NumericType h)
        : _rect({
            .midpoint={.x=x, .y=y},
            .width=w,
            .height=h})
        {}

    Rect(const Rect &r) : _rect(r._rect) {}

    NumericType x() const { return _rect.midpoint.x; }
    NumericType y() const { return _rect.midpoint.y; }
    NumericType width() const { return _rect.width; }
    NumericType height() const { return _rect.height; }
    PointType midpoint() const { return _rect.midpoint; }

    void x(NumericType v) { _rect.midpoint.x = v; }
    void y(NumericType v) { _rect.midpoint.y = v; }
    void width(NumericType v) { _rect.width = v; }
    void height(NumericType v) { _rect.height = v; }
    void midpoint(PointType v) { _rect.midpoint = v; }


    NumericType top() const {
        return { _rect.midpoint.y.v - _rect.height.v/2 };
    }
    void top(NumericType v) {
        _rect.midpoint.y.v = v.v + _rect.height.v/2;
    }

    NumericType left() const {
        return { _rect.midpoint.x.v - _rect.width.v/2 };
    }
    void left(NumericType v) {
        _rect.midpoint.x.v = v.v + _rect.width.v/2;
    }

    NumericType right() const {
        return { _rect.midpoint.x.v + _rect.width.v/2 };
    }

    NumericType bottom() const {
        return { _rect.midpoint.y.v + _rect.height.v/2 };
    }



protected:
    RectType _rect;
};


using RectPixels = Rect<rect_pixels_t>;
using RectMeters = Rect<rect_meters_t>;


class Trajectory {
public:
    using PointCollection = std::vector<PointMeters>;

    ~Trajectory() {}

    Trajectory() {}
    Trajectory(size_t s) : points(s) {}
    Trajectory(const Trajectory &) = default;
    Trajectory(Trajectory &&) = default;
    Trajectory & operator=(Trajectory && v) = default;
    Trajectory & operator=(const Trajectory & v) = default;



    PointCollection points;
};


} /* common */
} /* avsim */
