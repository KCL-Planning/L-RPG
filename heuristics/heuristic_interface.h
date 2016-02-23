#ifndef MYPOP_HEURISTICS_HEURISTIC_INTERFACE
#define MYPOP_HEURISTICS_HEURISTIC_INTERFACE

#include <vector>
#include <map>

namespace MyPOP {

class GroundedAtom;
class State;
class TermManager;
class Object;

namespace REACHABILITY {
class AchievingTransition;
};

namespace HEURISTICS {

class VariableDomain;
	
class HeuristicInterface
{
public:
	virtual ~HeuristicInterface();
	virtual void setHeuristicForState(MyPOP::State& state, const std::vector<const GroundedAtom*>& initial_facts, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager, bool find_helpful_actions, bool allow_new_goals_to_be_added) = 0;
	virtual void getFunctionalSymmetricSets(std::multimap<const Object*, const Object*>& symmetrical_groups, const State& state, const std::vector<const GroundedAtom*>& initial_facts, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager) const;
	
	const std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >& getHelpfulActions() const { return helpful_actions_; }
	
	void deleteHelpfulActions();
	
protected:
	
	std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > > helpful_actions_;
};

};

};

#endif
