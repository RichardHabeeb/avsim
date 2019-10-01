#include "src/simulation/sim.h"


namespace avsim {
namespace simulation {

void Sim::tick() {
    if(_paused) return;

    for(auto it = roads.begin();
        it != roads.end(); ++it)
    {
        (*it)->tick();
    }
    for(auto it = intersections.begin();
        it != intersections.end(); ++it)
    {
        (*it)->tick();
    }
    for(auto it = cars.begin();
        it != cars.end(); ++it)
    {
        (*it)->tick();
    }
}



} /* simulation */
} /* avsim */

