
extern "C" {
#include "src/simulator/sim.h"
}

namespace avsim {
namespace visualization {

class Visualization {
public:
	enum Error {
		InternalError,
        NoError,
	};

	~Visualization() {};
	virtual Error setup(sim_t *sim)  = 0;
	virtual Error draw(sim_t *sim) = 0;
};

} /* visualization */
} /* avsim */
