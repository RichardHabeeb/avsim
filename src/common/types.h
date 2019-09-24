#pragma once

#include <type_traits>
#include "src/common/ctypes.h"

namespace avsim {
namespace common {


template <typename T>
class Tickable {
public:
    virtual T tick() = 0;
};


template<typename PointType>
class Point {
public:
    static_assert(std::is_same<
        decltype(PointType::x),
        decltype(PointType::y)>::value);

     using NumericType = decltype(PointType::x);

    Point(NumericType x, NumericType y)
        : _p({.x = x, .y = y}) {}
    Point(const Point &p) : _p(p._p) {}
    ~Point() {}

    NumericType x() const { return _p.x; }
    NumericType y() const { return _p.y; }
    void x(NumericType v) { _p.x = v; }
    void y(NumericType v) { _p.y = v; }

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
    ~Rect() {}

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



protected:
    RectType _rect;
};


using RectPixels = Rect<rect_pixels_t>;
using RectMeters = Rect<rect_meters_t>;

} /* common */
} /* avsim */
