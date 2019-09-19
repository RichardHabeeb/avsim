#pragma once


#include "src/common/ctypes.h"

namespace avsim {
namespace common {


template<typename T>
class Point {
    

protected:
    T _point;
};

template<typename RectType>
class Rect {
    using PointType = decltype(RectType::midpoint);
    using SizeType = decltype(RectType::width);

    Rect(PointType p, SizeType w, SizeType h) {};

protected:
    RectType _rect;
};

} /* common */
} /* avsim */
