#pragma once

#include "src/common/types.h"
#include "src/vehicles/damn.h"

namespace avsim {
namespace vehicles {

class TwoWheelDamn : public Damn<common::Trajectory> {
public:
    ~TwoWheelDamn() {}

    virtual common::Trajectory tick();
};



} /* vehicles */
} /* avsim */
