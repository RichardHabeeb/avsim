#pragma once

#include "src/common/types.h"
#include "src/common/ctypes.h"
#include "src/vehicles/vehicle.h"


namespace avsim {
namespace vehicles {

class TwoWheel : public Vehicle {
public:

    void tick() override;

protected:
    meters_t _wheel_base;
    radians_t _steer_angle;
};

}
} /* avsim */
