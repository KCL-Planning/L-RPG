#ifndef MYPOP_HEURISTICS_HEURISTIC_INTERFACE
#define MYPOP_HEURISTICS_HEURISTIC_INTERFACE

#include <vector>

namespace MyPOP {

class GroundedAtom;
class State;

namespace HEURISTICS {

class HeuristicInterface
{
public:
	virtual ~HeuristicInterface();
	virtual void setHeuristicForState(MyPOP::State& state, const std::vector<const GroundedAtom*>& goal_facts, bool find_helpful_actions, bool allow_new_goals_to_be_added) = 0;
};

};

};

#endif
