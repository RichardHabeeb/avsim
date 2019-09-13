#include "src/simulation/sim.h"

namespace avsim {
namespace visualization {

class Visualization {
public:
	enum Error {
		InternalError,
        NoError,
	};

	~Visualization() {};
	virtual Error setup(simulation::Sim &sim)  = 0;
	virtual Error draw(simulation::Sim &sim) = 0;
};

} /* visualization */
} /* avsim */
