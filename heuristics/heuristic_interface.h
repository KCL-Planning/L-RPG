#ifndef MYPOP_HEURISTICS_HEURISTIC_INTERFACE
#define MYPOP_HEURISTICS_HEURISTIC_INTERFACE

#include <vector>
#include <map>

namespace MyPOP {

class GroundedAtom;
class State;
class TermManager;
class Object;

namespace HEURISTICS {

class HeuristicInterface
{
public:
	virtual ~HeuristicInterface();
	virtual void setHeuristicForState(MyPOP::State& state, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager, bool find_helpful_actions, bool allow_new_goals_to_be_added) = 0;
	virtual void getFunctionalSymmetricSets(std::multimap<const Object*, const Object*>& symmetrical_groups, const State& state, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager);
};

};

};

#endif
