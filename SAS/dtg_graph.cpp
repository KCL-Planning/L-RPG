#include "dtg_graph.h"

#include <sys/time.h>
#include <algorithm>

#include "dtg_manager.h"
#include "dtg_node.h"
#include "transition.h"
#include "property_space.h"

#include "../VALfiles/TimSupport.h"
#include "../type_manager.h"
#include "../predicate_manager.h"
#include "../action_manager.h"
#include "../term_manager.h"
#include "../formula.h"
#include "../parser_utils.h"
#include "../plan_bindings.h"
#include "../bindings_propagator.h"
#include "../plan.h"

namespace MyPOP {

namespace SAS_Plus {

DTGBindings::DTGBindings(const TermManager& term_manager, const BindingsPropagator& propagator)
	: Bindings(term_manager, propagator)
{

}

DTGBindings::DTGBindings(const Bindings& other)
	: Bindings(other)
{

}

// TODO: Place holders don't add predicate index information to the DTG...
bool DTGBindings::canUnifyDTGNodes(const MyPOP::SAS_Plus::DomainTransitionGraphNode& node1, const MyPOP::SAS_Plus::DomainTransitionGraphNode& node2) const
{
//	std::cout << "Can unify: " << node1 << " and " << node2 << "?" << std::endl;
	for (std::vector<BoundedAtom*>::const_iterator ci = node1.getAtoms().begin(); ci != node1.getAtoms().end(); ci++)
	{
		BoundedAtom* bounded_atom1 = *ci;
		
		bool canUnify = false;
		for (std::vector<BoundedAtom*>::const_iterator ci = node2.getAtoms().begin(); ci != node2.getAtoms().end(); ci++)
		{
			BoundedAtom* bounded_atom2 = *ci;
			if (node1.getDTG().getBindings().canUnify(bounded_atom1->getAtom(), bounded_atom1->getId(), bounded_atom2->getAtom(), bounded_atom2->getId(), &node2.getDTG().getBindings()) &&
			    node1.getIndex(*bounded_atom1) == node2.getIndex(*bounded_atom2))
			{
				canUnify = true;
				break;
			}
		}

		// If one of the atoms cannot be unified, return false;
		if (!canUnify)
		{
			return false;
		}
	}

	// Make sure none of the atoms are mutually exclusive.
	if (node1.getDTG().areMutex(node1, node2))
	{
		return false;
	}

	return true;
}

std::ostream& operator<<(std::ostream& os, const PropertyState& property_state)
{
	os << "property state: ";
	for (std::vector<Property*>::const_iterator ci = property_state.getProperties().begin(); ci != property_state.getProperties().end(); ci++)
	{
		os << (*ci)->getPredicate() << "(" << (*ci)->getIndex() << "), ";
	}
	os << std::endl;
	return os;
}


///DomainTransitionGraph::DomainTransitionGraph(const DomainTransitionGraphManager& dtg_manager, PropertySpace& property_space, const TypeManager& type_manager, const ActionManager& action_manager, const PredicateManager& predicate_manager, const DTGBindings& bindings, const std::vector<const Atom*>& initial_facts)
DomainTransitionGraph::DomainTransitionGraph(const DomainTransitionGraphManager& dtg_manager, const TypeManager& type_manager, const ActionManager& action_manager, const PredicateManager& predicate_manager, const DTGBindings& bindings, const std::vector<const Atom*>& initial_facts)
	: dtg_manager_(&dtg_manager), dtg_term_manager_(new TermManager(type_manager)), action_manager_(&action_manager), predicate_manager_(&predicate_manager), bindings_(new DTGBindings(bindings)), initial_facts_(&initial_facts), type_(NULL)
{

}

DomainTransitionGraph::~DomainTransitionGraph()
{
	// Delete all the domain transition graph nodes.
	for (std::vector<DomainTransitionGraphNode*>::iterator i = nodes_.begin(); i != nodes_.end(); i++)
	{
		delete *i;
	}

	delete bindings_;
	delete dtg_term_manager_;
}

bool DomainTransitionGraph::addNode(DomainTransitionGraphNode& dtg_node, std::vector<DomainTransitionGraphNode*>* added_nodes)
{
	assert (&dtg_node.getDTG() == this);
	// Make sure we don't add a node twice to a DTG!
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		if (*ci == &dtg_node)
		{
			std::cout << "[ERROR] Trying to add the node: " << dtg_node << " but it already exists!" << *this << std::endl;
			assert(false);
		}
	}
	
	// Check if a node already exists in the DTG who's variable domains overlap with dtg_node. If this is the case, for
	// example consider the following DTG:
	// (at { truck1, truck2 } {s1, s2} ) and the DTG node to add: (at { truck1 } { s1, s3 } ) we can see that two nodes
	// can now describe the assignment (at truck1 s1) which is not desirable. If we find such a situation we redeem it 
	// by splitting the domains in such a case that no such situation can occur.
	std::vector<DomainTransitionGraphNode*> nodes_to_unify;
	nodes_to_unify.push_back(&dtg_node);
	
	std::vector<DomainTransitionGraphNode*> nodes_copy = nodes_;
	bool could_unify = false;
	while (nodes_to_unify.size() > 0)
	{
		DomainTransitionGraphNode* node_to_unify = nodes_to_unify.back();
		nodes_to_unify.erase(nodes_to_unify.end() - 1);
		for (std::vector<DomainTransitionGraphNode*>::iterator i = nodes_copy.begin(); i != nodes_copy.end(); i++)
		{
			DomainTransitionGraphNode* existing_dtg_node = *i;

			// If all the atoms overlap with an existing node, merge!
			if (bindings_->canUnifyDTGNodes(*existing_dtg_node, *node_to_unify))
			{
				could_unify = true;
				break;
			}
		}
	}

	if (!could_unify)
	{
		nodes_.push_back(&dtg_node);
		if (added_nodes != NULL)
		{
			added_nodes->push_back(&dtg_node);
		}
		return true;
	}
//	std::cout << "[DomainTransitionGraph::addNode] Result: " << *this << std::endl;
	return false;
}

// Get all nodes which have the given predicate.
void DomainTransitionGraph::getNodes(std::vector<DomainTransitionGraphNode*>& dtg_nodes, const Predicate& predicate, unsigned int index) const
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		DomainTransitionGraphNode* node = *ci;
		for (std::vector<BoundedAtom*>::const_iterator ci = node->getAtoms().begin(); ci != node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			if (bounded_atom->getAtom().getPredicate() == predicate && node->getIndex(*bounded_atom) == index)
			{
				dtg_nodes.push_back(node);
				break;
			}
		}
	}
}

bool DomainTransitionGraph::areMutex(const DomainTransitionGraphNode& dtg_node1, const DomainTransitionGraphNode& dtg_node2) const
{
//	std::cout << "Check if are mutex: " << dtg_node1 << " and " << dtg_node2 << std::endl;

	for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node1.getAtoms().begin(); ci != dtg_node1.getAtoms().end(); ci++)
	{
		BoundedAtom* bounded_atom1 = *ci;
//		InvariableIndex index1 = dtg_node1.getIndex(*bounded_atom1);

		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node2.getAtoms().begin(); ci != dtg_node2.getAtoms().end(); ci++)
		{
			BoundedAtom* bounded_atom2 = *ci;
//			InvariableIndex index2 = dtg_node2.getIndex(*bounded_atom2);

			// Check if these are mutal exclusive.
			///if (areMutex(bounded_atom1->getAtom().getPredicate(), index1, bounded_atom2->getAtom().getPredicate(), index2))
			if (bounded_atom1->isMutexWith(*bounded_atom2))
			{
				return true;
			}
		}
	}

	return false;
}

void DomainTransitionGraph::addBalancedSet(const PropertySpace& property_space, bool create_nodes)
{
	std::cout << "[DomainTransitionGraph::addPredicate]; Create node? " << create_nodes << std::endl;
	
	assert (nodes_.size() == 0);
	
	property_spaces_.push_back(&property_space);
	
	/**
	 * Adding a balanced set, we need to update the type of the invariable to the most specific subtype.
	 */
	bool type_changed = false;
///	for (std::vector<PropertyState*>::const_iterator ci = predicates_to_add.begin(); ci != predicates_to_add.end(); ci++)
	for (std::vector<const PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
	{
		const PropertyState* property_state = *ci;
		
///		property_space_->addPropertyState(*property_state);
		
		for (std::vector<Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
		{
			const Property* property = *ci;
			// If there is no invariable, we do not need to check this, obviously :).
			if (property->getIndex() == NO_INVARIABLE_INDEX)
			{
				continue;
			}
			
			const Type* type = property->getPredicate().getTypes()[property->getIndex()];
			std::cout << "* " << property->getPredicate() << "_" << property->getIndex() << "(" << *type << ");" << std::endl;
			
			// If no type has been assigned to the invariable objects, do it now.
			if (type_ == NULL)
			{
				type_ = type;
				type_changed = true;
			}

			// If the type of this predicate is more specific than the existing one, update it.
			else if (type->isSubtypeOf(*type_))
			{
				type_ = type;
				type_changed = true;
			}
		}
	}

	/**
	 * After detecting the most specific type, update all the types of the invariables.
	 */
	///for (std::vector<PropertyState*>::const_iterator ci = predicates_to_add.begin(); ci != predicates_to_add.end(); ci++)
	for (std::vector<const PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
	{
		const PropertyState* property_state = *ci;
		
		for (std::vector<Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
		{
			Property* property = *ci;
			
			if (property->getIndex() == NO_INVARIABLE_INDEX)
			{
				continue;
			}
			
			const Type* type = property->getPredicate().getTypes()[property->getIndex()];

			// Check if the predicate needs to be updated.
			if (type != type_)
			{
				std::vector<const Type*> predicate_types = property->getPredicate().getTypes();
				predicate_types[property->getIndex()] = type_;
				const Predicate* new_predicate = predicate_manager_->getPredicate(property->getPredicate().getName(), predicate_types);

				if (new_predicate == NULL)
				{
					std::cout << "Predicate: " << property->getPredicate().getName() << " of types: ";
					for (std::vector<const Type*>::const_iterator ci = predicate_types.begin(); ci != predicate_types.end(); ci++)
					{
						std::cout << **ci << std::endl;
					}
					std::cout << std::endl;
					assert (false);
				}
				
				std::cout << "Update predicate: " << property->getPredicate() << std::endl;

				property->setPredicate(*new_predicate);
				
				std::cout << "Result: " << property->getPredicate() << std::endl;
			}
			
			/**
			 * Add the updated predicate to the list of predicates of this DTG.
			 */
			bool exists = false;
			for (std::vector<const Property*>::const_iterator ci = predicates_.begin(); ci != predicates_.end(); ci++)
			{
				if (*ci == property)
				{
					exists = true;
					break;
				}
			}
			
			if (!exists)
			{
				predicates_.push_back(property);
			}
		}
	}
	
	///updateMutexRelations(predicates_to_add);

	if (create_nodes)
	{
		/**
		 * Create a separate DTG node for each property state.
		 */
///		for (std::vector<PropertyState*>::const_iterator ci = predicates_to_add.begin(); ci != predicates_to_add.end(); ci++)
		for (std::vector<const PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
		{
			const PropertyState* property_state = *ci;
			
			DomainTransitionGraphNode* dtg_node = NULL;

			for (std::vector<Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ++ci)
			{
				const Property* property = *ci;
				const Predicate& predicate = property->getPredicate();
				unsigned int index = property->getIndex();
				
				std::cout << "Create a node with predicate: " << predicate << std::endl;
				
				// We create a node which we will add to the DTG. This node is a lifted SAS+ variable which includes
				// all possible nodes in the DTG with the given predicate. Later we will be able to split this node
				// up into multiple nodes and create a more refined DTG.
				std::vector<const Term*>* terms = new std::vector<const Term*>();
				const std::vector<const Type*> types = predicate.getTypes();
		
				// This is a little messy. To manage the lifted DTG nodes we use a binding manager. Initially we add
				// all possible objects to the variables of the atom so this node could represent any possible grounding
				// of the given atom. As we do more domain analysis we will be able to prune these domains and eventually
				// split some nodes and make the DTG more refined and informative.
				unsigned int counter = 0;
				
				// We assign every DTG node an unique ID. Because the IDS 0 and 1 are taken by the initial and goal step, 
				// respectively. The ids of the DTGs will start at 2. This ID is only unique within this DTG.
				// Note: Because TIM does not always gets the type right, we will add the most general type available and
				// prune the domains once we start adding transitions between the different DTG nodes and pick the most
				// specific ones as the definite type.
				for (std::vector<const Type*>::const_iterator ci = types.begin(); ci != types.end(); ci++)
				{
					const Type* type = *ci;
		
					std::ostringstream oss;
					oss << predicates_.size() << "_" << type->getName() << ++counter;
					std::string name = oss.str();
					Variable* variable = new Variable(*type, name);
					terms->push_back(variable);
					
					// Add the variable to the term manager so we can remove them once finished.
					dtg_term_manager_->addManagableObject(variable);
				}
		
				Atom* atom = new Atom(predicate, *terms, false);
				
				if (dtg_node == NULL)
				{
					dtg_node = createDTGNode(*atom, index, property);
				}
				else
				{
					StepID unique_nr = bindings_->createVariableDomains(*atom);
					dtg_node->addAtom(new BoundedAtom(unique_nr, *atom, property), index);
				}
			}
			addNode(*dtg_node);
		}
	}
}

bool DomainTransitionGraph::containsPropertySpace(const PropertySpace& property_space) const
{
	for (std::vector<const PropertySpace*>::const_iterator ci = property_spaces_.begin(); ci != property_spaces_.end(); ci++)
	{
		const PropertySpace* ps = *ci;
		
		if (ps == &property_space)
		{
			return true;
		}
	}
	
	return false;
}

void DomainTransitionGraph::addObjects()
{
	objects_.clear();
	
	// TODO: Add objects per predicate space. So if there are multiple predicate spaces the range of objects will be determined
	// for each of them independently (because they are optional preconditions...).
	
	const std::vector<const Atom*>& initial_facts = dtg_manager_->getInitialFacts();
	std::set<const Object*> domain;
	// Check which nodes from the initial state are part of this DTG.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator dtg_node_ci = nodes_.begin(); dtg_node_ci != nodes_.end(); dtg_node_ci++)
	{
		DomainTransitionGraphNode* dtg_node = *dtg_node_ci;
///		std::set<const Object*> domain;
		bool domain_initialised = false;
		
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			const Atom& dtg_node_atom = (*ci)->getAtom();
			StepID dtg_node_id = (*ci)->getId();
			
			std::set<const Object*> tmp_domain;
			
			for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
			{
				const Atom* initial_fact = *ci;
				if (bindings_->canUnify(*initial_fact, Step::INITIAL_STEP, dtg_node_atom, dtg_node_id))
				{
					// Add this object to the DTGs objects! :)
//					std::cout << "!!! ";
//					initial_fact->print(std::cout);
//					std::cout << " can be unified with this DTG! :D" << std::endl;
					
//					tmp_domain.insert(initial_fact->getTerms()[dtg_node->getIndex(*bounded_atom)]->asObject());
					const std::vector<const Object*> initial_fact_domain = initial_fact->getTerms()[dtg_node->getIndex(*bounded_atom)]->getDomain(Step::INITIAL_STEP, *bindings_);
					tmp_domain.insert(initial_fact_domain.begin(), initial_fact_domain.end());
				}
			}
			
//			if (!domain_initialised)
			{
				domain_initialised = true;
				domain.insert(tmp_domain.begin(), tmp_domain.end());
			}
/*			else
			{
				std::set<const Object*> intersection;
				std::set_intersection(domain.begin(), domain.end(), tmp_domain.begin(), tmp_domain.end(), std::inserter(intersection, intersection.begin()));
				
				domain.clear();
				domain.insert(intersection.begin(), intersection.end());
			}
			*/
		}
		
///		objects_.insert(objects_.begin(), domain.begin(), domain.end());
	}
	objects_.insert(objects_.begin(), domain.begin(), domain.end());
/*
	// Update the transitions so they reflect this.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		DomainTransitionGraphNode* dtg_node = *ci;
		
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			BoundedAtom* bounded_atom = *ci;
			
			// TEST
			if (dtg_node->getIndex(*bounded_atom) == NO_INVARIABLE_INDEX) continue;
			
			bounded_atom->getAtom().getTerms()[dtg_node->getIndex(*bounded_atom)]->makeDomainEqualTo(bounded_atom->getId(), objects_, *bindings_);
//			VariableDomain& vd = bindings_->getNonConstVariableDomain(bounded_atom->getId(), *bounded_atom->getAtom().getTerms()[dtg_node->getIndex(*bounded_atom)]->asVariable());
//			vd.setObjects(objects_);
		}
	}
*/
}

void DomainTransitionGraph::removeObjects(const std::set<const Object*>& objects)
{
	for (std::vector<const Object*>::reverse_iterator ri = objects_.rbegin(); ri != objects_.rend(); ri++)
	{
		if (objects.count(*ri) != 0)
		{
			objects_.erase(ri.base() - 1);
		}
	}
}

bool DomainTransitionGraph::isValidPredicateIndex(const Predicate& predicate, unsigned int index) const
{
	for (std::vector<const Property*>::const_iterator ci = predicates_.begin(); ci != predicates_.end(); ci++)
	{
		const Property* property = *ci;
		if (property->getPredicate().canSubstitute(predicate) && property->getIndex() == index)
		{
			return true;
		}
	}
	return false;
}

DomainTransitionGraphNode* DomainTransitionGraph::createDTGNode(const Atom& atom, unsigned int index, const Property* property)
{
	StepID unique_nr = bindings_->createVariableDomains(atom);

	static unsigned int unique_id = 0;
	
	DomainTransitionGraphNode* dtg_node = new DomainTransitionGraphNode(*this, unique_id++);
	dtg_node->addAtom(new BoundedAtom(unique_nr, atom, property), index);
	return dtg_node;
}

void DomainTransitionGraph::removeNode(const DomainTransitionGraphNode& dtg_node)
{
	std::vector<DomainTransitionGraphNode*>::iterator node_to_remove = nodes_.end();
	for (std::vector<DomainTransitionGraphNode*>::iterator i = nodes_.begin(); i != nodes_.end(); i++)
	{
		if (*i == &dtg_node)
		{
			node_to_remove = i;
		}
		
		// Remove all transitions to this node.
		std::vector<const Transition*>& transitions = (*i)->getTransitionsNonConst();
		std::vector<const Transition*>::iterator the_end = std::remove_if(transitions.begin(), transitions.end(), std::bind2nd(Utilities::TransitionToNodeEquals(), &dtg_node));
		transitions.erase(the_end, transitions.end());
	}
	
	if (node_to_remove != nodes_.end())
	{
		nodes_.erase(node_to_remove);
	}
}

void DomainTransitionGraph::getNodes(std::vector<const SAS_Plus::DomainTransitionGraphNode*>& dtg_nodes, StepID step_id, const Atom& atom, const Bindings& bindings, unsigned int index) const
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
/*		std::cout << "[DomainTransitionGraph::getNodes] Compare: ";
		dtg_node->print(std::cout);
		std::cout << " v.s. ";
		atom.print(std::cout, bindings, step_id);
		std::cout << std::endl;
*/
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			
			if (bindings_->canUnify(bounded_atom->getAtom(), bounded_atom->getId(), atom, step_id, &bindings) &&
				(index == std::numeric_limits<unsigned int>::max() || 
				dtg_node->getIndex(*bounded_atom) == index))
			{
				dtg_nodes.push_back(dtg_node);
				break;
			}
		}
	}
}

void DomainTransitionGraph::getNodes(std::vector<const DomainTransitionGraphNode*>& found_dtg_nodes, const std::vector<const Atom*>& initial_facts, const Bindings& bindings) const
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
/*		std::cout << "[DomainTransitionGraph::getNodes] Compare: ";
		dtg_node->getAtom().print(std::cout, *bindings_, dtg_node->getId());
		std::cout << " v.s. ";
		atom.print(std::cout, bindings, step_id);
		std::cout << std::endl;*/
		bool can_unify_dtg_node = true;
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			
			bool can_unify_atom = false;
			for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
			{
				const Atom* atom = *ci;
				if (bindings_->canUnify(bounded_atom->getAtom(), bounded_atom->getId(), *atom, Step::INITIAL_STEP, &bindings))
				{
					can_unify_atom = true;
					break;
				}
			}
			
			if (!can_unify_atom)
			{
				can_unify_dtg_node = false;
				break;
			}
		}
		
		if (can_unify_dtg_node)
		{
			found_dtg_nodes.push_back(dtg_node);
		}
	}
}

/*void DomainTransitionGraph::mergePredicates(const DomainTransitionGraph& other)
{
	// Make this predicate mutex to all other predicates.
	for (std::map<IndexedProperty, std::set<IndexedProperty>* >::const_iterator ci = other.mutex_map_.begin(); ci != other.mutex_map_.end(); ci++)
	{
		IndexedProperty index_predicate = (*ci).first;
		std::set<IndexedProperty>* mutexes = (*ci).second;
		
		// Not part of the current mutex map, copy it.
		if (mutex_map_.find(index_predicate) == mutex_map_.end())
		{
			mutex_map_[index_predicate] = mutexes;
		}
		// Already part, merge the two.
		else
		{
			mutex_map_[index_predicate]->insert(mutexes->begin(), mutexes->end());
		}
	}
	
	unsigned int middle = predicates_.size();
	
	// Merge the predicates.
	std::copy(other.predicates_.begin(), other.predicates_.end(), std::back_inserter(predicates_));
	std::inplace_merge(predicates_.begin(), predicates_.begin() + middle, predicates_.end());
	predicates_.erase(std::unique(predicates_.begin(), predicates_.end()), predicates_.end());
}*/

void DomainTransitionGraph::identifySubGraphs(std::vector<DomainTransitionGraph*>& subgraphs) const
{
	struct timeval start_time;
	gettimeofday(&start_time, NULL);
	
	/**
	 * The process of identifying subgraphs is as follows:
	 * For all nodes:
	 * - Mark all end points of the transitions starting at that node.
	 * Then for every node until the graph stabilises:
	 * - Copy the reachable nodes from all end points of the transitions.
	 * 
	 * Put all nodes in the same DTG if the set of reachable nodes (including
	 * the node itself) is equal.
	 */
	boost::dynamic_bitset<>* reachable_set[nodes_.size()];
	for (unsigned int i = 0; i < nodes_.size(); i++)
	{
		reachable_set[i] = new boost::dynamic_bitset<>(nodes_.size());
		
//		std::cout << "[" << i << "] \t";
//		nodes_[i]->print(std::cout);
//		std::cout << std::endl;
	}
	
	struct timeval end_time;
	gettimeofday(&end_time, NULL);
	double time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
	std::cerr << " * Initialise subgraph structures: " << time_spend << " seconds" << std::endl;

	gettimeofday(&start_time, NULL);
//	std::cout << "Update link transitions: " << std::endl;
	// Store the relations between the various bit sets.
	std::vector<boost::dynamic_bitset<>*> linked_by_transitions[nodes_.size()];
	for (unsigned int i = 0; i < nodes_.size(); i++)
	{
		/**
		 * Mark all nodes directly reachable through the transition.
		 */
		const DomainTransitionGraphNode* dtg_node = nodes_[i];
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			
			// Figure out at what index the end node is.
			const DomainTransitionGraphNode& to_node = transition->getToNode();
			for (unsigned int j = 0; j < nodes_.size(); j++)
			{
				if (nodes_[j] == &to_node)
				{
					(*reachable_set[i])[j] = true;
					linked_by_transitions[i].push_back(reachable_set[j]);
					break;
				}
			}
		}
		
		/**
		 * Including itself.
		 */
		(*reachable_set[i])[i] = true;
		
//		std::cout << "[" << i << "] " << *reachable_set[i] << std::endl;
	}
	gettimeofday(&end_time, NULL);
	time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
	std::cerr << " * Setting the initial transitions: " << time_spend << " seconds" << std::endl;

	gettimeofday(&start_time, NULL);
//	std::cout << "Update link transitions: " << std::endl;
	
	
	/**
	 * Propagate this information.
	 */
//	std::cout << "Start propagating! " << std::endl;
	bool set_changed = true;
	while (set_changed)
	{
		set_changed = false;
//		std::cout << "Start cycle!" << std::endl;
		
		for (unsigned int i = 0; i < nodes_.size(); i++)
		{
//			std::cout << "[" << i << "] ";
//			nodes_[i]->print(std::cout);
//			std::cout << *reachable_set[i] << std::endl;
			boost::dynamic_bitset<>* reachable_nodes = reachable_set[i];

			/**
			* Mark all nodes reachable who are also reachable by the nodes reachable through the transitions.
			*/
			for (std::vector<boost::dynamic_bitset<>* >::const_iterator ci = linked_by_transitions[i].begin(); ci != linked_by_transitions[i].end(); ci++)
			{
				const boost::dynamic_bitset<>* to_node_reachables = *ci;
//				std::cout << *reachable_nodes << " v.s. " << *to_node_reachables << std::endl;
				if (!to_node_reachables->is_subset_of(*reachable_nodes))
				{
					(*reachable_nodes) |= *to_node_reachables;
					set_changed = true;
				}
			}
//			std::cout << "After update: " << *reachable_nodes << std::endl;
		}
	}
	
	gettimeofday(&end_time, NULL);
	time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
	std::cerr << " * Propagating: " << time_spend << " seconds" << std::endl;

	gettimeofday(&start_time, NULL);
//	std::cout << "Update link transitions: " << std::endl;
	
	/**
	 * Group nodes who share the same reachability set.
	 */
	std::map<boost::dynamic_bitset<>, std::vector<DomainTransitionGraphNode*>* > grouped_dtg_nodes;
	for (unsigned int i = 0; i < nodes_.size(); i++)
	{
		boost::dynamic_bitset<>* reachable_nodes = reachable_set[i];
		
		if (grouped_dtg_nodes.find(*reachable_nodes) != grouped_dtg_nodes.end())
		{
			continue;
		}
		
		std::vector<DomainTransitionGraphNode*>* new_group = new std::vector<DomainTransitionGraphNode*>();
		
		for (unsigned int i = 0; i < nodes_.size(); i++)
		{
			if ((*reachable_nodes)[i] == true)
			{
				new_group->push_back(nodes_[i]);
			}
		}
	}
	
	gettimeofday(&end_time, NULL);
	time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
	std::cerr << " * Group together: " << time_spend << " seconds" << std::endl;

	gettimeofday(&start_time, NULL);
//	std::cout << "Update link transitions: " << std::endl;
	
	double time_spend_dtgs = 0;
	double time_spend_dtg_nodes = 0;
	double time_spend_transitions = 0;
	
	/**
	 * Construct the DTGs.
	 */
	for (std::map<boost::dynamic_bitset<>, std::vector<DomainTransitionGraphNode*>* >::const_iterator ci = grouped_dtg_nodes.begin(); ci != grouped_dtg_nodes.end(); ci++)
	{
		std::vector<DomainTransitionGraphNode*>* grouped_dtg_nodes = (*ci).second;
		
		struct timeval dtg_construct_start;
		gettimeofday(&dtg_construct_start, NULL);
//		std::cout << "Update link transitions: " << std::endl;
		///DomainTransitionGraph* new_dtg = new DomainTransitionGraph(*dtg_manager_, *property_space_, dtg_term_manager_->getTypeManager(), *action_manager_, *predicate_manager_, *bindings_, *initial_facts_);
		DomainTransitionGraph* new_dtg = new DomainTransitionGraph(*dtg_manager_, dtg_term_manager_->getTypeManager(), *action_manager_, *predicate_manager_, *bindings_, *initial_facts_);
		struct timeval dtg_construct_end;
		gettimeofday(&dtg_construct_end, NULL);
		time_spend_dtgs += dtg_construct_end.tv_sec - dtg_construct_start.tv_sec + (dtg_construct_end.tv_usec - dtg_construct_start.tv_usec) / 1000000.0;
		
		/**
		 * Copy all aspects of this DTG, except for the DTG nodes.
		 */
		new_dtg->objects_ = objects_;
		new_dtg->predicates_ = predicates_;
///		new_dtg->mutex_map_ = mutex_map_;
		new_dtg->type_ = type_;
		new_dtg->property_spaces_ = property_spaces_;
		
		struct timeval add_dtg_nodes_start;
		gettimeofday(&add_dtg_nodes_start, NULL);
//		std::cout << "Update link transitions: " << std::endl;
		
		// Add the DTG nodes.
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = grouped_dtg_nodes->begin(); ci != grouped_dtg_nodes->end(); ci++)
		{
			const DomainTransitionGraphNode* original_node = *ci;
			DomainTransitionGraphNode* new_dtg_node = new DomainTransitionGraphNode(*original_node, *new_dtg);
			new_dtg->addNode(*new_dtg_node);
		}

		struct timeval add_dtg_nodes_end;
		gettimeofday(&add_dtg_nodes_end, NULL);
		time_spend_dtg_nodes += add_dtg_nodes_end.tv_sec - add_dtg_nodes_start.tv_sec + (add_dtg_nodes_end.tv_usec - add_dtg_nodes_start.tv_usec) / 1000000.0;

		struct timeval transitions_start;
		gettimeofday(&transitions_start, NULL);
		new_dtg->reestablishTransitions();
		struct timeval transitions_end;
		gettimeofday(&transitions_end, NULL);
		time_spend_transitions += transitions_end.tv_sec - transitions_start.tv_sec + (transitions_end.tv_usec - transitions_start.tv_usec) / 1000000.0;
		subgraphs.push_back(new_dtg);
	}
	
	gettimeofday(&end_time, NULL);
	time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
	std::cerr << " * Construct the DTGs: " << time_spend << " seconds" << std::endl;
	std::cerr << " ** DTG constructor: " << time_spend_dtgs << " seconds" << std::endl;
	std::cerr << " ** DTG Node constructor: " << time_spend_dtg_nodes << " seconds" << std::endl;
	std::cerr << " ** Transitions: " << time_spend_transitions << " seconds" << std::endl;
}

void DomainTransitionGraph::reestablishTransitions()
{
	std::cout << "=== Reestablish transitions for the DTG === " << std::endl << *this << std::endl;
	/**
	 * Only consider those transitions which were already part of the DTG node can be added.
	 */
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		DomainTransitionGraphNode* from_node = *ci;
		from_node->removeTransitions(false);
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
		{
			DomainTransitionGraphNode* to_node = *ci;
			
			// Find all possible transitions between these two.
			std::vector<const Action*> possible_transitions;
			from_node->getPossibleActions(possible_transitions, *to_node);
			
/*			std::cout << "Transitions from ";
			from_node->print(std::cout);
			std::cout << " to ";
			to_node->print(std::cout);
			std::cout << " have the following possible actions: ";
*/
			// Otherwise try all these transitiosn.
			for (std::vector<const Action*>::const_iterator ci = possible_transitions.begin(); ci != possible_transitions.end(); ci++)
			{
				const Action* action = *ci;
///				std::cout << *action << ", ";
				std::vector<BoundedAtom>* enabler_dummy = new std::vector<BoundedAtom>();

				Transition* transition = Transition::createTransition(*enabler_dummy, *action, *from_node, *to_node, *initial_facts_);
				if (transition != NULL)
				{
					from_node->addTransition(*transition, false);
				}
			}
			
//			std::cout << std::endl;
		}
	}
	
	std::cout << "=== Result: ===" << std::endl << *this << std::endl;
}

void DomainTransitionGraph::establishTransitions()
{
	std::cout << "Establish transitions for: " << *this << std::endl;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		//assert ((*ci)->getTransitions().empty());
		(*ci)->removeTransitions(true);
	}
	
	// Go through the list of all possible transitions and add them when we can.
	for (std::vector<Action*>::const_iterator ci = action_manager_->getManagableObjects().begin(); ci != action_manager_->getManagableObjects().end(); ci++)
	{
		const Action* action = *ci;

		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
		{
			DomainTransitionGraphNode* from_node = *ci;
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
			{
				DomainTransitionGraphNode* to_node = *ci;
				std::vector<BoundedAtom>* enabler_dummy = new std::vector<BoundedAtom>();

				Transition* transition = Transition::createTransition(*enabler_dummy, *action, *from_node, *to_node, *initial_facts_);
				if (transition != NULL)
				{
					from_node->addTransition(*transition, true);
				}
			}
		}
	}
	
	std::cout << "=== Result: ===" << std::endl << *this << std::endl;
}


void DomainTransitionGraph::splitNodes(const std::map<DomainTransitionGraph*, std::vector<DomainTransitionGraph*>* >& split_graphs)
{
	std::cout << "[DomainTransitionGraph::splitNodes] Process DTG: " << *this << std::endl;
	for (std::map<DomainTransitionGraph*, std::vector<DomainTransitionGraph*>* >::const_iterator ci = split_graphs.begin(); ci != split_graphs.end(); ci++)
	{
		DomainTransitionGraph* splitted_dtg = (*ci).first;
		std::vector<DomainTransitionGraph*>* results_of_split = (*ci).second;
		
		std::cout << "Process splitted DTG: " << *splitted_dtg << std::endl;
		std::cout << "Splitted into: ";
		for (std::vector<DomainTransitionGraph*>::const_iterator ci = results_of_split->begin(); ci != results_of_split->end(); ci++)
		{
			std::cout << **ci << std::endl;
		}
		
		std::vector<DomainTransitionGraphNode*> nodes_to_add;
		std::vector<DomainTransitionGraphNode*> nodes_to_remove;
		
		/**
		 * Propagate the effects of the splitted DTG to all nodes contained in this DTG.
		 */
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
		{
			DomainTransitionGraphNode* dtg_node = *ci;
			
			/**
			 * Store which variables are affected. Stored as: VariableDomain -> { <#atom, #variable> }.
			 */
			std::map<std::pair<const Term*, StepID>, std::vector<std::pair<InvariableIndex, InvariableIndex> >* > affected_variables;
			
			/**
			 * Only those nodes need to be modified if they are somehow dependend on the values of the splitted graph. With other words,
			 * unless there exists a transition with a precondition linked to the splitted graph, we need not split.
			 */
			for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
			{
				const Transition* transition = *ci;

				const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
//				std::vector<std::pair<const Atom*, InvariableIndex> > preconditions;
//				transition->getAllPreconditions(preconditions);

				for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
				{
					const Atom* precondition = (*ci).first;

					/**
					* Ignore the precondition if it is part of the DTG node. We are only interested preconditions held
					* in other DTG nodes, because we cannot split a DTG node because of a value it contains.
					* TODO: Check correctness...
					*/
					bool precondition_is_contained_by_dtg_node = false;
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition->getPreconditions().begin(); ci != transition->getPreconditions().end(); ci++)
					{
						if (bindings_->canUnify(*precondition, transition->getStep()->getStepId(), *(*ci).first, transition->getStep()->getStepId()))
						{
							precondition_is_contained_by_dtg_node = true;
							break;
						}
					}
					
					if (precondition_is_contained_by_dtg_node)
					{
						continue;
					}
					
					/**
					 * Check if this precondition is captured by the given splitted DTG.
					 */
					std::vector<const DomainTransitionGraphNode*> matched_dtg_nodes;
					splitted_dtg->getNodes(matched_dtg_nodes, transition->getStep()->getStepId(), *precondition, *bindings_);
					
					/**
					 * If no nodes were found, than the splitted node has no effect on this node.
					 */
					if (matched_dtg_nodes.size() == 0)
					{
						continue;
					}
					
					/**
					 * If a node was found, then we need to update the variable which corresponds to the splitted DTG's invariable.
					 */
					///const VariableDomain* affected_variable_domain = NULL;
					const Term* affected_term = NULL;
					for (std::vector<BoundedAtom*>::const_iterator ci = matched_dtg_nodes[0]->getAtoms().begin(); ci != matched_dtg_nodes[0]->getAtoms().end(); ci++)
					{
						if (bindings_->canUnify(*precondition, transition->getStep()->getStepId(), (*ci)->getAtom(), (*ci)->getId(), &splitted_dtg->getBindings()))
						{
							affected_term = precondition->getTerms()[matched_dtg_nodes[0]->getIndex(**ci)];
							///std::cout << "Variable domain to split: " << *affected_variable_domain << std::endl;
							break;
						}
					}
					
					/**
					 * Store the affected variables, but only if it hasn't been processed yet.
					 */
					if (affected_term != NULL && affected_variables.count(std::make_pair(affected_term, transition->getStep()->getStepId())))
					{
						std::vector<std::pair<InvariableIndex, InvariableIndex> >* affected_properties = new std::vector<std::pair<InvariableIndex, InvariableIndex> >();
						std::cout << "Affected <atoms, variables> for ";
						dtg_node->print(std::cout);
						std::cout << ": ";
						for (unsigned int atom_nr = 0; atom_nr < dtg_node->getAtoms().size(); atom_nr++)
						{
							const BoundedAtom* bounded_atom = dtg_node->getAtoms()[atom_nr];
							//for (std::vector<const Term*>::const_iterator ci = bounded_atom->getTerms().begin(); ci != bounded_atom->getTerms().end(); ci++)
							for (unsigned int variable_nr = 0; variable_nr < bounded_atom->getAtom().getTerms().size(); variable_nr++)
							{
								const Term* term = bounded_atom->getAtom().getTerms()[variable_nr];
								if (term->isTheSameAs(bounded_atom->getId(), *affected_term, transition->getStep()->getStepId(), *bindings_))
								{
									std::cout << "<" << atom_nr << ", " << variable_nr << "> ";
									affected_properties->push_back(std::make_pair(atom_nr, variable_nr));
								}
							}
						}
						
						if (affected_properties->size() > 0)
						{
							affected_variables[std::make_pair(affected_term, transition->getStep()->getStepId())] = affected_properties;
						}
						else
						{
							delete affected_properties;
						}
						
						std::cout << std::endl;
					}
				}
			}
			
			if (affected_variables.size() == 0)
			{
				continue;
			}
			
			nodes_to_remove.push_back(dtg_node);
			
			/**
			 * Start splitting the nodes! :)
			 * We have X variables which are affected with their respective domains. The result_of_split contains all the
			 * new domains for these variables. We explore all possible assignments add these as new nodes.
			 */
			unsigned int counter[affected_variables.size()];
			memset(&counter[0], 0, sizeof(unsigned int) * affected_variables.size());
			unsigned int active_counter = 0;
			
			while (true)
			{
				std::cout << "Counter: {";
				for (unsigned int i = 0; i < affected_variables.size(); i++)
				{
					std::cout << counter[i] << ", ";
				}
				std::cout << "}" << std::endl;
				DomainTransitionGraphNode* new_node = new DomainTransitionGraphNode(*dtg_node, false);
				
				unsigned int i = 0;
				for (std::map<std::pair<const Term*, StepID>, std::vector<std::pair<InvariableIndex, InvariableIndex> >* >::const_iterator ci = affected_variables.begin(); ci != affected_variables.end(); ci++)
				{
					std::vector<std::pair<InvariableIndex, InvariableIndex> >* affected_pair = (*ci).second;
					
					// Assign to all these variables the counter[i]th values of results_of_split.
					for (std::vector<std::pair<InvariableIndex, InvariableIndex> >::const_iterator ci = affected_pair->begin(); ci != affected_pair->end(); ci++)
					{
						BoundedAtom* bounded_atom = new_node->getAtoms()[(*ci).first];
						bounded_atom->getAtom().getTerms()[(*ci).second]->makeDomainEqualTo(bounded_atom->getId(), (*results_of_split)[counter[i]]->getObjects(), *bindings_);
					}
					
					i++;
				}
				
				std::cout << "New node! " << *new_node << std::endl;
				//addNode(*new_node);
				nodes_to_add.push_back(new_node);
				
				/**
				 * Update counter.
				 * Check if we have reached the maximum of the current conter.
				 */
				if (counter[active_counter] == results_of_split->size() - 1)
				{
					// Reset all counters and carry the bit over.
					if (active_counter != affected_variables.size() - 1)
					{
						++active_counter;
						memset(&counter[0], 0, sizeof(unsigned int) * affected_variables.size());
					}
					else
					{
						// We have reached the maximum of the last bit, we are done!
						break;
					}
				}
				
				// Update the active counter.
				++counter[active_counter];
			}
		}
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_to_remove.begin(); ci != nodes_to_remove.end(); ci++)
		{
			removeNode(**ci);
		}
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_to_add.begin(); ci != nodes_to_add.end(); ci++)
		{
			addNode(**ci);
		}
	}
}

void DomainTransitionGraph::groundTerm(std::vector<DomainTransitionGraphNode*>& affected_nodes, std::vector<DomainTransitionGraphNode*>& grounded_nodes, const MyPOP::Term& term_to_ground, StepID term_id)
{
	assert (false);
/*	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		DomainTransitionGraphNode* dtg_node = *ci;
		
		if (dtg_node->groundTerm(grounded_nodes, term_to_ground, step_id))
		{
			affected_nodes.push_back(dtg_node);
		}
	}*/
}

bool DomainTransitionGraph::isSupported(unsigned int id, const MyPOP::Atom& atom, const MyPOP::Bindings& bindings) const
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		if ((*ci)->isSupported(id, atom, bindings))
		{
			return true;
		}
	}
	
	return false;
}

void DomainTransitionGraph::removeUnsupportedTransitions()
{
	for (std::vector<DomainTransitionGraphNode*>::reverse_iterator ci = nodes_.rbegin(); ci != nodes_.rend(); ci++)
	{
		(*ci)->removeUnsupportedTransitions();
		
		// If one of the variable domains is empty, remove the node.
		if ((*ci)->containsEmptyVariableDomain())
		{
			std::cout << "Remove the node: ";
			(*ci)->print(std::cout);
			std::cout << std::endl;
			removeNode(**ci);
		}
	}
}

void DomainTransitionGraph::merge(const MyPOP::SAS_Plus::DomainTransitionGraph& other)
{
	property_spaces_.insert(property_spaces_.end(), other.property_spaces_.begin(), other.property_spaces_.end());
}


std::ostream& operator<<(std::ostream& os, const DomainTransitionGraph& dtg)
{
	os << "{ ";
	for (std::vector<const Object*>::const_iterator ci = dtg.objects_.begin(); ci != dtg.objects_.end(); ci++)
	{
		os << **ci;
		if (ci + 1 != dtg.objects_.end())
		{
			os << ", ";
		}
	}
	os << " }" << std::endl;
	
	os << "[ ";
	for (std::vector<const Property*>::const_iterator ci = dtg.predicates_.begin(); ci != dtg.predicates_.end(); ci++)
	{
		os << (*ci)->getPredicate() << "{" << (*ci)->getIndex() << "} ";
	}
	os << "]" << std::endl;

	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg.nodes_.begin(); ci != dtg.nodes_.end(); ci++)
	{
		os << **ci;
		os << std::endl;
	}

	//os << *dtg.bindings_;
	return os;
}

};

};
