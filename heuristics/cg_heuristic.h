#ifndef MYPOP_HEURISTICS_CAUSAL_GRAPH
#define MYPOP_HEURISTICS_CAUSAL_GRAPH

#include <vector>
#include <map>
#include <ostream>

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
	LCGSearchNode(std::vector<const HEURISTICS::Fact*>& assignments, const SAS_Plus::MultiValuedValue& node, std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >& assignments_to_lower_variables_, unsigned int cost = 0);
	
	LCGSearchNode(const LCGSearchNode& starting_node, std::vector<const HEURISTICS::Fact*>& assignments, const SAS_Plus::MultiValuedValue& node, std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >& assignments_to_lower_variables_, unsigned int cost = 0);
	
	LCGSearchNode(const LCGSearchNode& other);
	
	LCGSearchNode& createDeepCopy() const;
	
	~LCGSearchNode();
	
	const std::vector<const HEURISTICS::Fact*>& getAssignments() const { return *assignments_; }
	
	const SAS_Plus::MultiValuedValue& getNode() const { return *node_; }
	
	const std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >& getAssignmentsToLowerVariables() const { return *assignments_to_lower_variables_; }
	
	const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& getAssignmentsToLowerVariables(const SAS_Plus::LiftedDTG& lifted_dtg) const;
	
	unsigned int getCost() const { return cost_; }
	
	const LCGSearchNode& getStartingNode() const { return *starting_node_; }
	
private:
	
	const LCGSearchNode* starting_node_;
	
	// The assignments to the facts of the node.
	//const std::vector<const HEURISTICS::Fact*>* assignments_;
	std::vector<const HEURISTICS::Fact*>* assignments_;
	
	// The node that has been reached.
	const SAS_Plus::MultiValuedValue* node_;
	
	// All the assignments made to the lower-level variables.
	std::map<const SAS_Plus::LiftedDTG*, std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >* >* assignments_to_lower_variables_;
	
	unsigned int cost_;
	
	friend std::ostream& operator<<(std::ostream& os, const LCGSearchNode& search_node);
};

std::ostream& operator<<(std::ostream& os, const LCGSearchNode& search_node);

class LiftedCausalGraphHeuristic : public HeuristicInterface
{
public:
	LiftedCausalGraphHeuristic(const std::vector<SAS_Plus::LiftedDTG*>& lifted_dtgs, const ActionManager& action_manager, const PredicateManager& predicate_manager, const std::vector< const GroundedAtom* >& goal_facts);
	
	virtual ~LiftedCausalGraphHeuristic();
	
	void setHeuristicForState(MyPOP::State& state, const std::vector<const GroundedAtom*>& goal_facts, bool find_helpful_actions, bool allow_new_goals_to_be_added);
	
private:
	
	unsigned int getHeuristic(const State& state, const std::vector< const GroundedAtom* >& bounded_goal_facts);
	
	const LCGSearchNode* getCost(const State& state, const std::vector<const SAS_Plus::LiftedDTG*>& lifted_dtgs, const HEURISTICS::Fact& goal, const LCGSearchNode* current_search_node);
	
	const LCGSearchNode* getCost(const State& state, const SAS_Plus::LiftedDTG& lifted_dtg, const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& from_nodes, const std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& to_nodes);
	
	const std::vector<SAS_Plus::LiftedDTG*>* lifted_dtgs_;
	
	const PredicateManager* predicate_manager_;
	
	const SAS_Plus::MultiValuedValue* findNode(const HEURISTICS::Fact& fact, const std::vector<const SAS_Plus::LiftedDTG*>& possible_lifted_dtgs) const;
	
	void getNodes(std::vector<std::pair<const SAS_Plus::MultiValuedValue*, const std::vector<const HEURISTICS::Fact*>* > >& assignments, const SAS_Plus::LiftedDTG& lifted_dtg, const HEURISTICS::VariableDomain& invariable_domain, const State& state) const;

	void findMappings(std::vector<std::vector<const HEURISTICS::Fact*>* >& found_mappings, const std::vector<const HEURISTICS::Fact*>& current_mappings, const SAS_Plus::MultiValuedValue& node, const HEURISTICS::VariableDomain& invariable_domain, const State& state) const;
	
	SAS_Plus::CausalGraph* causal_graph_;
	
	// Cached solutions.
	// We can use the cache of a solution iff:
	// The start end end nodes are the same and the invariables match too.
	std::map<const SAS_Plus::MultiValuedValue*, std::vector<std::pair<const HEURISTICS::Fact*, LCGSearchNode*> >* > cache_;
	//LCGSearchNode
	
};

};
	
};

#endif //MYPOP_HEURISTICS_CAUSAL_GRAPH
