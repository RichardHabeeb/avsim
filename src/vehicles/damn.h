#pragma once

#include <vector>
#include <memory>
#include "src/common/types.h"

namespace avsim {
namespace vehicles {



class Vote {
public:
    Vote(size_t s) : options(s) {}
    ~Vote() {}

    std::vector<int> options;
};

template<typename OptionType>
class Ballot {
public:
    Ballot(size_t s) : options(s) {}
    ~Ballot() {}

    std::vector<OptionType> options;
};

template<typename OptionType>
class DamnBehavior {
public:
    virtual Vote vote(Ballot<OptionType> &) = 0;
    virtual ~DamnBehavior() {};

    double weight() const { return _weight; }
    void weight(double v) { _weight = v; }
protected:
    double _weight;
};

template<typename OptionType>
class Damn : public common::Tickable<OptionType> {
public:
    using BehaviorCollection =
        std::vector<std::shared_ptr<DamnBehavior<OptionType>>>;

    ~Damn() {}
    virtual OptionType tick() = 0;

    BehaviorCollection behaviors;
};



} /* vehicles */
} /* avsim */
