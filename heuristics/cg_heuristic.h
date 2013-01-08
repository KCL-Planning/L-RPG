#ifndef MYPOP_HEURISTICS_CAUSAL_GRAPH
#define MYPOP_HEURISTICS_CAUSAL_GRAPH

#include <vector>

//#include "fc_planner.h"
#include "heuristic_interface.h"

namespace MyPOP {

class ActionManager;
class GroundedAtom;
class GroundedAction;
class PredicateManager;
	
namespace SAS_Plus {
class LiftedDTG;
class MultiValuedValue;
class CausalGraph;
};
	
namespace HEURISTICS {

class Fact;
class LCGSearchNode;
class VariableDomain;

class CompareLCGSearchNodes {
public:
	bool operator()(const LCGSearchNode* p1, const LCGSearchNode* p2);
};

/**
 * A struct which contains all the information of how we reached a certain node in the lifted DTG.
 */
class LCGSearchNode
{
public:
	LCGSearchNode(const std::vector<const GroundedAtom*>& assignments, const SAS_Plus::MultiValuedValue& node, std::vector<const GroundedAction*>& plan);
	
	LCGSearchNode(const std::vector<const GroundedAtom*>& assignments, const SAS_Plus::MultiValuedValue& node);
	
	LCGSearchNode(const LCGSearchNode& other);
	
	~LCGSearchNode();
	
	const std::vector<const GroundedAtom*>& getAssignments() const { return *assignments_; }
	
	const SAS_Plus::MultiValuedValue& getNode() const { return *node_; }
	
	const std::vector<const GroundedAction*>& getPlan() const { return *plan_; }
	
private:
	
	// The assignments to the facts of the node.
	const std::vector<const GroundedAtom*>* assignments_;
	
	// The node that has been reached.
	const SAS_Plus::MultiValuedValue* node_;
	
	// The plan found till now.
	std::vector<const GroundedAction*>* plan_;
};

class LiftedCausalGraphHeuristic : public HeuristicInterface
{
public:
	LiftedCausalGraphHeuristic(const std::vector<SAS_Plus::LiftedDTG*>& lifted_dtgs, const ActionManager& action_manager, const PredicateManager& predicate_manager, const std::vector< const GroundedAtom* >& goal_facts);
	
	void setHeuristicForState(MyPOP::State& state, const std::vector<const GroundedAtom*>& goal_facts, bool find_helpful_actions, bool allow_new_goals_to_be_added);
	
private:
	
	unsigned int getHeuristic(const State& state, const std::vector< const GroundedAtom* >& bounded_goal_facts);
	
	const LCGSearchNode* getCost(const MyPOP::State& state, const std::vector< std::pair< const MyPOP::SAS_Plus::MultiValuedValue*, std::vector< const MyPOP::GroundedAtom* >* > >& from_nodes, const std::vector< std::pair< const MyPOP::SAS_Plus::MultiValuedValue*, std::vector< const HEURISTICS::Fact* >* > >& to_nodes) const;
	
	const std::vector<SAS_Plus::LiftedDTG*>* lifted_dtgs_;
	
	const PredicateManager* predicate_manager_;
	
	const SAS_Plus::MultiValuedValue* findNode(const HEURISTICS::Fact& fact) const;
	
	void getNodes(std::vector<std::pair<const SAS_Plus::MultiValuedValue*, std::vector<const GroundedAtom*>* > >& assignments, const SAS_Plus::LiftedDTG& lifted_dtg, const HEURISTICS::VariableDomain& invariable_domain, const State& state) const;

	void findMappings(std::vector<std::vector<const GroundedAtom*>* >& found_mappings, const std::vector<const GroundedAtom*>& current_mappings, const SAS_Plus::MultiValuedValue& node, const HEURISTICS::VariableDomain& invariable_domain, const State& state) const;
	
	SAS_Plus::CausalGraph* causal_graph_;
	
};

};
	
};

#endif //MYPOP_HEURISTICS_CAUSAL_GRAPH
