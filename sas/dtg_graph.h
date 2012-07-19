#ifndef SAS_PLUS_DTG_GRAPH_H
#define SAS_PLUS_DTG_GRAPH_H

#include <vector>
#include <iostream>
#include <map>
#include <set>

#include "dtg_node.h"
#include "../plan_bindings.h"
#include "../manager.h"

namespace MyPOP {

class Atom;
class TypeManager;
class Predicate;
class Object;
class TermManager;
class BindingsPropagator;
	
namespace SAS_Plus {

class RecursiveFunctionManager;


class BoundedAtom;
class DomainTransitionGraphNode;
class DomainTransitionGraphManager;
class PropertySpace;
class Property;
class PropertyState;
	
/**
 * A domain transition graph(DTG) captures the transitions objects of a certain type can make
 * within the planning problem. A DTG is constructed by analysing the domain to see if a combination
 * of predicates are balanced. That is to say, given the initial state and a set of balanced predicates,
 * the number of these predicates in any reachable state will never increase or decrease.
 * From this we can contruct a graph showing the transitions between the propositions in the set
 * we can make. Given a set of objects which are part of this DTG we can use this to calculate
 * heuristics (like Fast-Downward) or use it to find landmarks (like LAMA).
 */
class DomainTransitionGraph : public ManageableObject
{
public:
	DomainTransitionGraph(const MyPOP::SAS_Plus::DomainTransitionGraphManager& dtg_manager, const MyPOP::TypeManager& type_manager, const MyPOP::ActionManager& action_manager, Bindings& bindings, const std::vector< const MyPOP::Atom* >& initial_facts);
	
	~DomainTransitionGraph();

	/**
	 * Add a predicate as one of the set which makes a balanced set. The position is the term
	 * of the predicate which is reserved for the objects linked to this DTG. This function can
	 * only be called once.
	 * @param predicate One of the predicates which makes it a balanced set.
	 * @param position The position marks the term which is reserved for objects linked to this DTG.
	 * @param craete_node Create a lifted DTG an attach it to this DTG.
	 */
	void addBalancedSet(const PropertySpace& property_space, bool create_nodes);
	
	/**
	 * Get the predicates which are present in this DTG.
	 */
	const std::vector<const Property*>& getPredicates() const { return predicates_; }
	
	/**
	 * Check the initial state for all objects which are part of this DTG and add them.
	 */
	void addObjects();
	
	/**
	 * Remove objects from the domain of the invariants.
	 */
	void removeObjects(const std::set<const Object*>& objects);

	/**
	 * Get all the objects whos transitions are described by this DTG.
	 */
	const std::vector<const Object*>& getObjects() const { return objects_; }

	/**
	 * Add a node to this DTG.
	 * @param dtg_node The DTG node to add to this DTG.
	 * @param added_nodes If this vector is not NULL then all nodes added by this function to the DTG will be added
	 * to this vector as well.
	 */
	bool addNode(DomainTransitionGraphNode& dtg_node, std::vector<DomainTransitionGraphNode*>* added_nodes = NULL);

	/**
	 * Get all nodes already added to this DTG.
	 */
	const std::vector<DomainTransitionGraphNode*>& getNodes() const { return nodes_; }

	/**
	 * Check if two nodes are mutex.
	 */
	bool areMutex(const DomainTransitionGraphNode& dtg_node1, const DomainTransitionGraphNode& dtg_node2) const;

	/**
	 * Get all nodes which have the given predicate or NULL if no nodes are found.
	 * @param predicate The predicate all nodes searched for are based on.
	 */
	void getNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& dtg_nodes, const Predicate& predicate, unsigned int index) const;
	void getNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& found_dtg_nodes, const std::vector<const Atom*>& initial_facts, const Bindings& bindings) const;
	
//	void getNodes(std::vector<const DomainTransitionGraphNode*>& results, const std::vector<const BoundedAtom*>& to_find) const;
	

	/**
	 * Get this DTG's bindings.
	 */
	Bindings& getBindings() const { return *bindings_; }
	
	/**
	 * Return the DTG manager.
	 */
	const DomainTransitionGraphManager& getDTGManager() const { return *dtg_manager_; }
	
	/**
	 * Remove a node from the DTG node.
	 * @param dtg_node The DTG node to remove.
	 */
	void removeNode(const DomainTransitionGraphNode& dtg_node);
	
	/**
	 * Find all the nodes which can be unified with the given atom and its bindings.
	 * @param dtg_nodes All nodes which can be unified are added to this list.
	 * @param step_id The step id which has been used to bind the atom's variables.
	 * @param atom The bounded atom.
	 * @param bindings The bindings which are used to bind the atom's bindings.
	 * @param index The index at which the variable should be invariable in the found DTG node. If this variable
	 * is equal to ALL_INVARIABLE_INDEXES this constraint isn't checked.
	 */
	void getNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& dtg_nodes, MyPOP::StepID step_id, const MyPOP::Atom& atom, const MyPOP::Bindings& bindings, InvariableIndex index = ALL_INVARIABLE_INDEXES) const;

	/**
	 * Should only be called the first time transitions are to be established.
	 */
	void establishTransitions();
	
	/**
	 * Separate the objects into groups based on membership of a set of recursive functions.
	 */
	void separateObjects(const RecursiveFunctionManager& recursive_function_manager);
	
	void removeUnconnectedNodes();
	
	void solveSubsets();

	friend std::ostream& operator<<(std::ostream& os, const DomainTransitionGraph& dtg);
private:
	
	bool containsDoubleVariableDomains(const DomainTransitionGraphNode& dtg_node) const;

	
	/**
	 * Create a new DTG node with the given atom and add bind t to this DTG's bindings. The node is not added though!
	 * @param atom The atom to create the lifted DTG node from.
	 */
	DomainTransitionGraphNode* createDTGNode(const Atom& atom, unsigned int index, const Property* property);
	
	bool containsPropertySpace(const PropertySpace& property_space) const;
	
	const DomainTransitionGraphManager* dtg_manager_;
	
	/**
	 * Every DTG is linked to a single - or multiple - property spaces. A property space dictates which states are
	 * captured by this DTG.
	 */
	std::vector<const PropertySpace*> property_spaces_;

	// When we split DTG nodes up we have a need for new atoms for every node. To manage the
	// terms we add them to this term manager (and remove them as well when needed.
	TermManager* dtg_term_manager_;
	
	const ActionManager* action_manager_;

	// To propagate changes made to the DTGs we keep track of all bindings between them and propagate changes
	// as necessary.
	//DTGBindings* bindings_;
	Bindings* bindings_;
	
	const std::vector<const Atom*>* initial_facts_;

	// The nodes of this DTG.
	std::vector<DomainTransitionGraphNode*> nodes_;

	// The objects which share this DTG.
	std::vector<const Object*> objects_;
	
	// Set of objects which correspond to membership of recursive functions.
	std::vector<std::vector<const Object*>* > objects_sets_;

	// To create a DTG a set of predicates are combined to construct a 'balanced set', i.e.
	// taken all the effects of all actions involving these predicates there will always be
	// a single value true in any given state for the above objects. The int is the parameter
	// number of the predicate reserved for the objects linked to this DTG. Between any transition
	// the object on the given position will always be the same; e.g. (at PACKAGE ?loc) -> (in PACKAGE ?truck).
	// Read: Exhibiting Knowledge in Planning Problems to Minimize State Encoding Length
	// by Stefan Edelkamp and Malte Helmert.
	std::vector<const Property*> predicates_;

	// Most specific type of the invariable object.
	const Type* type_;
};

std::ostream& operator<<(std::ostream& os, const DomainTransitionGraph& dtg);

};

};

#endif // SAS_PLUS_DTG_GRAPH_H
