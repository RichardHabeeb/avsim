#pragma once

#include <type_traits>

namespace avsim {
namespace common {

template <typename Numeric>
Numeric clamp(const Numeric& v, const Numeric& lo, const Numeric& hi) {
    static_assert(std::is_arithmetic<Numeric>::value);
    //assert(!(hi < lo));
    return (v < lo) ? lo : (hi < v) ? hi : v;
}



} /* common */
} /* avsim */
