#include "dtg_graph.h"

#include <sys/time.h>
#include <algorithm>

#include "dtg_manager.h"
#include "dtg_node.h"
#include "transition.h"
#include "property_space.h"
#include "recursive_function.h"

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

//#define MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS

namespace MyPOP {

namespace SAS_Plus {

DomainTransitionGraph::DomainTransitionGraph(const DomainTransitionGraphManager& dtg_manager, const TypeManager& type_manager, const ActionManager& action_manager, const PredicateManager& predicate_manager, Bindings& bindings, const std::vector<const Atom*>& initial_facts)
	: dtg_manager_(&dtg_manager), dtg_term_manager_(new TermManager(type_manager)), action_manager_(&action_manager), predicate_manager_(&predicate_manager), bindings_(&bindings), initial_facts_(&initial_facts), type_(NULL)
{

}

DomainTransitionGraph::~DomainTransitionGraph()
{
	// Delete all the domain transition graph nodes.
	for (std::vector<DomainTransitionGraphNode*>::iterator i = nodes_.begin(); i != nodes_.end(); i++)
	{
		delete *i;
	}
	
	for (std::vector<const PropertySpace*>::const_iterator ci = property_spaces_.begin(); ci != property_spaces_.end(); ci++)
	{
		delete *ci;
	}

	delete dtg_term_manager_;
}

bool DomainTransitionGraph::addNode(DomainTransitionGraphNode& dtg_node, std::vector<DomainTransitionGraphNode*>* added_nodes)
{
	assert (&dtg_node.getDTG() == this);

	nodes_.push_back(&dtg_node);
	if (added_nodes != NULL)
	{
		added_nodes->push_back(&dtg_node);
	}
	return true;
}

// Get all nodes which have the given predicate.
void DomainTransitionGraph::getNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& dtg_nodes, const Predicate& predicate, unsigned int index) const
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		DomainTransitionGraphNode* node = *ci;
		for (std::vector<BoundedAtom*>::const_iterator ci = node->getAtoms().begin(); ci != node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			if (bounded_atom->getAtom().getPredicate() == predicate && node->getIndex(*bounded_atom) == index)
			{
				dtg_nodes.push_back(std::make_pair(node, bounded_atom));
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
			if (bounded_atom1->isMutexWith(*bounded_atom2, *bindings_))
			{
				return true;
			}
		}
	}

	return false;
}

void DomainTransitionGraph::addBalancedSet(const PropertySpace& property_space, bool create_nodes)
{
//	std::cout << "[DomainTransitionGraph::addPredicate]; Create node? " << create_nodes << std::endl;
	
	assert (nodes_.size() == 0);
	
	property_spaces_.push_back(&property_space);
	
	/**
	 * Adding a balanced set, we need to update the type of the invariable to the most specific subtype.
	 */
//	bool type_changed = false;
	for (std::vector<const PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
	{
		const PropertyState* property_state = *ci;
		
		for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
		{
			const Property* property = *ci;
			// If there is no invariable, we do not need to check this, obviously :).
			if (property->getIndex() == NO_INVARIABLE_INDEX)
			{
				continue;
			}
			
			const Type* type = property->getPredicate().getTypes()[property->getIndex()];
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "* " << property->getPredicate() << "_" << property->getIndex() << "(" << *type << ");" << std::endl;
#endif

			// If no type has been assigned to the invariable objects, do it now.
			if (type_ == NULL)
			{
				type_ = type;
//				type_changed = true;
			}

			// If the type of this predicate is more specific than the existing one, update it.
			else if (type->isSubtypeOf(*type_))
			{
				type_ = type;
//				type_changed = true;
			}
		}
	}

	/**
	 * After detecting the most specific type, update all the types of the invariables.
	 */
	for (std::vector<const PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
	{
		const PropertyState* property_state = *ci;
		
		for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
		{
			Property* property = const_cast<Property*>(*ci);
			
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
				
//				std::cout << "Update predicate: " << property->getPredicate() << std::endl;

				property->setPredicate(*new_predicate);
				
//				std::cout << "Result: " << property->getPredicate() << std::endl;
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
	
	if (create_nodes)
	{
		/**
		 * Create a separate DTG node for each property state.
		 */
		for (std::vector<const PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
		{
			const PropertyState* property_state = *ci;
			
			DomainTransitionGraphNode* dtg_node = NULL;

			for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ++ci)
			{
				const Property* property = *ci;
				const Predicate& predicate = property->getPredicate();
				unsigned int index = property->getIndex();
				
//				std::cout << "Create a node with predicate: " << predicate << std::endl;
				
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
					BoundedAtom& bounded_atom = BoundedAtom::createBoundedAtom(*atom, *property, *bindings_);
					dtg_node->addAtom(bounded_atom, index);
//					StepID unique_nr = bindings_->createVariableDomains(*atom);
//					dtg_node->addAtom(new BoundedAtom(unique_nr, *atom, property), index);
				}
			}
			
			if (!addNode(*dtg_node))
			{
				delete dtg_node;
			}
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
	
	// Check which nodes from the initial state are part of this DTG.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator dtg_node_ci = nodes_.begin(); dtg_node_ci != nodes_.end(); dtg_node_ci++)
	{
		DomainTransitionGraphNode* dtg_node = *dtg_node_ci;

		const BoundedAtom* invariable_bounded_atom = NULL;
		
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			
			InvariableIndex index = dtg_node->getIndex(*bounded_atom);
			if (index == NO_INVARIABLE_INDEX)
			{
				continue;
			}
			
			for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
			{
				if (containsPropertySpace((*ci)->getPropertyState().getPropertySpace()))
				{
					invariable_bounded_atom = bounded_atom;
					break;
				}
			}
			
			if (invariable_bounded_atom != NULL)
			{
				break;
			}
			
/*			if (containsPropertySpace(bounded_atom->getProperty()->getPropertyState().getPropertySpace()))
			{
				invariable_bounded_atom = bounded_atom;
				break;
			}
*/
		}
		
		if (invariable_bounded_atom == NULL)
		{
			assert (false);
			continue;
		}
		
		/**
		 * Keep track not only of the possible objects for the invariable term but also for all the other related terms.
		 */
		std::map<const std::vector<const Object*>*, std::vector<const Object*>* > term_mappings;
		std::vector<std::vector<const Object*>* > to_remove;
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			const Atom& dtg_node_atom = bounded_atom->getAtom();
			StepID dtg_node_id = bounded_atom->getId();
			
			for (std::vector<const Term*>::const_iterator ci = dtg_node_atom.getTerms().begin(); ci != dtg_node_atom.getTerms().end(); ci++)
			{
				const Term* term = *ci;
				
				const std::vector<const Object*>& domain = term->getDomain(dtg_node_id, *bindings_);
				if (term_mappings.count(&domain) == 0)
				{
					std::vector<const Object*>* term_domain = new std::vector<const Object*>();
					to_remove.push_back(term_domain);
					term_domain->insert(term_domain->end(), domain.begin(), domain.end());
					term_mappings[&domain] = term_domain;
				}
			}
		}
		
		/**
		 * First find the set of intitial facts which can be merged with the atoms which refer to an invariable.
		 */
		for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
		{
			const Atom* initial_fact = *ci;
			if (bindings_->canUnify(*initial_fact, Step::INITIAL_STEP, invariable_bounded_atom->getAtom(), invariable_bounded_atom->getId()))
			{
				// Initialise the term domains.
				std::map<const std::vector<const Object*>*, std::vector<const Object*>* > new_term_mappings(term_mappings);
				
				for (unsigned int i = 0; i < invariable_bounded_atom->getAtom().getArity(); i++)
				{
					const std::vector<const Object*>& invariable_domain = invariable_bounded_atom->getAtom().getTerms()[i]->getDomain(invariable_bounded_atom->getId(), *bindings_);
					std::vector<const Object*>* mapping = new_term_mappings[&invariable_domain];
					std::vector<const Object*>* new_mapping = new std::vector<const Object*>(*mapping);
					to_remove.push_back(new_mapping);
					const std::vector<const Object*>& initial_fact_domain = initial_fact->getTerms()[i]->getDomain(Step::INITIAL_STEP, *bindings_);
					new_mapping->clear();
					new_mapping->insert(new_mapping->end(), initial_fact_domain.begin(), initial_fact_domain.end());
					new_term_mappings[&invariable_domain] = new_mapping;
				}

				// Check if these bindings will hold.
				if (dtg_node->validateTermMappings(dtg_node->getAtoms().begin(), dtg_node->getAtoms().end(), initial_facts, new_term_mappings))
				{
					const std::vector<const Object*>& domain = initial_fact->getTerms()[dtg_node->getIndex(*invariable_bounded_atom)]->getDomain(Step::INITIAL_STEP, *bindings_);
					for (std::vector<const Object*>::const_iterator ci = domain.begin(); ci != domain.end(); ci++)
					{
						const Object* object = *ci;
						
						// Make sure the object isn't already present.
						bool is_present = false;
						for (std::vector<const Object*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
						{
							if (*ci == object)
							{
								is_present = true;
								break;
							}
						}
						
						if (!is_present)
						{
							objects_.push_back(object);
						}
					}
				}
			}
		}
		
		for (std::vector<std::vector<const Object*>* >::const_iterator ci = to_remove.begin(); ci != to_remove.end(); ci++)
		{
			delete *ci;
		}
	}
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

DomainTransitionGraphNode* DomainTransitionGraph::createDTGNode(const Atom& atom, unsigned int index, const Property* property)
{
	DomainTransitionGraphNode* dtg_node = new DomainTransitionGraphNode(*this);
	
	BoundedAtom* new_bounded_atom = NULL;
	
	if (property == NULL)
		new_bounded_atom = &BoundedAtom::createBoundedAtom(atom, *bindings_);
	else
		new_bounded_atom = &BoundedAtom::createBoundedAtom(atom, *property, *bindings_);
	
	dtg_node->addAtom(*new_bounded_atom, index);
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
		for (std::vector<const Transition*>::reverse_iterator ri = transitions.rbegin(); ri != transitions.rend(); ri++)
		{
			const Transition* transition = *ri;
			if (&transition->getToNode() == &dtg_node)
			{
				transitions.erase(ri.base() - 1);
				delete transition;
			}
		}
	}
	
	if (node_to_remove != nodes_.end())
	{
		nodes_.erase(node_to_remove);
		delete &dtg_node;
	}
}

void DomainTransitionGraph::getNodes(std::vector<std::pair<const SAS_Plus::DomainTransitionGraphNode*, const BoundedAtom*> >& dtg_nodes, StepID step_id, const Atom& atom, const Bindings& bindings, InvariableIndex index) const
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;

		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			
			bool contains_index = (index == ALL_INVARIABLE_INDEXES);
			
			if (!contains_index)
			{
				for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
				{
					const Property* property = *ci;
					if (property->getIndex() == index)
					{
						contains_index = true;
						break;
					}
				}
			}
			
			if (!contains_index) continue;

			if (bindings_->canUnify(bounded_atom->getAtom(), bounded_atom->getId(), atom, step_id, &bindings))
			{
				dtg_nodes.push_back(std::make_pair(dtg_node, bounded_atom));
				break;
			}
		}
	}
}

void DomainTransitionGraph::getNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& found_dtg_nodes, const std::vector<const Atom*>& initial_facts, const Bindings& bindings) const
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
/*		std::cout << "[DomainTransitionGraph::getNodes] Compare: ";
		dtg_node->getAtom().print(std::cout, *bindings_, dtg_node->getId());
		std::cout << " v.s. ";
		atom.print(std::cout, bindings, step_id);
		std::cout << std::endl;*/
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
				found_dtg_nodes.push_back(std::make_pair(dtg_node, bounded_atom));
			}
		}
	}
}
/*
void DomainTransitionGraph::getNodes(std::vector<const DomainTransitionGraphNode*>& results, const std::vector<const BoundedAtom*>& to_find) const
{
	// Find all DTG nodes which contains all the bounded atoms provided.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		if (dtg_node->canMap(to_find))
		{
			results.push_back(dtg_node);
		}
	}
}
*/
void DomainTransitionGraph::establishTransitions()
{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "Establish transitions for: (" << bindings_->getNr() << ") " << *this << std::endl;
#endif
	
/*	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		
		assert ((*ci)->getTransitions().empty);
		(*ci)->removeTransitions(true);
	}*/
	
	std::vector<DomainTransitionGraphNode*> new_nodes;
	
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
				
				DomainTransitionGraphNode* new_from_node = new DomainTransitionGraphNode(*from_node);
				DomainTransitionGraphNode* new_to_node = new DomainTransitionGraphNode(*to_node);
				
				Transition* new_transition = Transition::createTransition(*action, *new_from_node, *new_to_node);
				
				if (new_transition != NULL)
				{
					new_from_node->addTransition(*new_transition);
					new_nodes.push_back(new_from_node);
					new_nodes.push_back(new_to_node);
				}
				else
				{
					delete new_from_node;
					delete new_to_node;
				}
			}
		}
	}
	
	// Free up the memory as we create new nodes for the transitions so these are no longer necessary.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		delete *ci;
	}
	nodes_.clear();

	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = new_nodes.begin(); ci != new_nodes.end(); ci++)
	{
		addNode(**ci);
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "=== Result: === (" << bindings_->getNr() << ") " << std::endl << *this << std::endl;
#endif
}

void DomainTransitionGraph::removeUnconnectedNodes()
{
	std::set<const DomainTransitionGraphNode*> marked_dtg_nodes;
	
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		// Check if this node is a superset of other.
		DomainTransitionGraphNode* dtg_node = *ci;
		
		if (!dtg_node->getTransitions().empty())
		{
			marked_dtg_nodes.insert(dtg_node);
		}
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			marked_dtg_nodes.insert(&transition->getToNode());
		}
	}
	
	
	for (std::vector<DomainTransitionGraphNode*>::reverse_iterator ri = nodes_.rbegin(); ri != nodes_.rend(); ri++)
	{
		DomainTransitionGraphNode* dtg_node = *ri;
		if (marked_dtg_nodes.count(dtg_node) == 0)
		{
			nodes_.erase(ri.base() - 1);
			delete dtg_node;
		}
	}
}

void DomainTransitionGraph::solveSubsets()
{
	std::map<DomainTransitionGraphNode*, std::vector<std::pair<DomainTransitionGraphNode*, unsigned int*> >* > sub_to_super_nodes;
	for (std::vector<DomainTransitionGraphNode*>::reverse_iterator ri = nodes_.rbegin(); ri != nodes_.rend(); ri++)
	{
		// Check if this node is a superset of other.
		DomainTransitionGraphNode* dtg_node = *ri;
		
		// Test for depots...
		// TODO: Should be removed in time...
		{
			bool contains_similar_variable_domain = dtg_node->containsDoubleVariableDomains();

			if (!contains_similar_variable_domain)
			{
				for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
				{
					const Transition* transition = *ci;
					
					if (transition->getToNode().containsDoubleVariableDomains())
					{
						contains_similar_variable_domain = true;
						break;
					}
				}
			}
			
			if (contains_similar_variable_domain)
			{
				nodes_.erase(ri.base() - 1);
				delete dtg_node;
				continue;
			}
		}

		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci2 = nodes_.begin(); ci2 != nodes_.end(); ci2++)
		{
			// Check if this node is a subset of the other.
			DomainTransitionGraphNode* other_dtg_node = *ci2;
			if (other_dtg_node == dtg_node) continue;
			
			if (dtg_node->getAtoms().size() != other_dtg_node->getAtoms().size()) continue;
			
			// Try to find a mapping from one set of atoms to the other.
			unsigned int* mapping = dtg_node->getMapping(*other_dtg_node);
			if (mapping == NULL) continue;
		
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "[solveSubsets] " << *dtg_node << " can be replaced by " << *other_dtg_node << std::endl;
#endif
			// dtg_node is a sub set of other_dtg_node. We can delete dtg_node and replace it with other_dtg_node.
			std::vector<std::pair<DomainTransitionGraphNode*, unsigned int* > >* sub_to_super_mappings = NULL;
			std::map<DomainTransitionGraphNode*, std::vector<std::pair<DomainTransitionGraphNode*, unsigned int*> >* >::const_iterator mapped_i = sub_to_super_nodes.find(dtg_node);
			if (mapped_i == sub_to_super_nodes.end())
			{
				sub_to_super_mappings = new std::vector<std::pair<DomainTransitionGraphNode*, unsigned int* > >();
				sub_to_super_nodes[dtg_node] = sub_to_super_mappings;
			}
			else
			{
				sub_to_super_mappings = (*mapped_i).second;
			}
			
			sub_to_super_mappings->push_back(std::make_pair(other_dtg_node, mapping));
		}
	}
	
	for (std::map<DomainTransitionGraphNode*, std::vector<std::pair<DomainTransitionGraphNode*, unsigned int*> >* >::const_iterator ci = sub_to_super_nodes.begin(); ci != sub_to_super_nodes.end(); ci++)
	{
		DomainTransitionGraphNode* from_node_to_replace = (*ci).first;
		
		for (std::vector<std::pair<DomainTransitionGraphNode*, unsigned int*> >::const_iterator ci2 = (*ci).second->begin(); ci2 != (*ci).second->end(); ci2++)
		{
			DomainTransitionGraphNode* super_from_node = (*ci2).first;
			unsigned int* from_mapping = (*ci2).second;
			
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "[DomainTransitionGraph::solveSubsets] Try to replace " << *from_node_to_replace << " with " << *super_from_node << std::endl;
#endif
		
			// Map the transition to the new nodes.
			for (std::vector<const Transition*>::const_iterator ci = from_node_to_replace->getTransitions().begin(); ci != from_node_to_replace->getTransitions().end(); ci++)
			{
				const Transition* transition = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
				std::cout << "[DomainTransitionGraph::solveSubsets] Process the transition: " << *transition << "." << std::endl;
#endif
				std::map<DomainTransitionGraphNode*, std::vector<std::pair<DomainTransitionGraphNode*, unsigned int*> >* >::const_iterator to_mapping_i = sub_to_super_nodes.find(&transition->getToNode());
				// Check if the to node has been replaced by other node(s).
				if (to_mapping_i != sub_to_super_nodes.end())
				{
					for (std::vector<std::pair<DomainTransitionGraphNode*, unsigned int*> >::const_iterator ci = (*to_mapping_i).second->begin(); ci != (*to_mapping_i).second->end(); ci++)
					{
						DomainTransitionGraphNode* super_to_node = (*ci).first;
						unsigned int* to_mapping = (*ci).second;
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
						std::cout << "Super set of the to node: " << *super_to_node << std::endl;
#endif
						Transition* new_transition = transition->migrateTransition(*super_from_node, *super_to_node, from_mapping, to_mapping);
						if (new_transition == NULL)
						{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
							std::cout << "[DomainTransitionGraph::solveSubsets] Could not replace the original transition..." << std::endl;
#endif
							continue;
						}
						super_from_node->addTransition(*new_transition);
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
						std::cout << "[DomainTransitionGraph::solveSubsets] Use the super node: New transition: " << *new_transition << "." << std::endl;
#endif
					}
				}
				
				// The to node is not replaced.
				else
				{
					unsigned int to_mapping[transition->getToNode().getAtoms().size()];
					for (unsigned int i = 0; i < transition->getToNode().getAtoms().size(); i++)
					{
						to_mapping[i] = i;
					}
				
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
					std::cout << "[DomainTransitionGraph::solveSubsets] Possible to node: " << transition->getToNode() << "." << std::endl;
#endif
					// TODO: The latter is the correct version. But it might be that the super set does not cover all the subsets, because it might 
					// be partly grounded.
					//Transition* new_transition = transition->migrateTransition(*sub_from_node, transition->getToNode(), from_mapping, to_mapping);
					Transition* new_transition = transition->migrateTransition(*super_from_node, transition->getToNode(), from_mapping, to_mapping);
					if (new_transition == NULL)
					{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
						std::cout << "[DomainTransitionGraph::solveSubsets] Could not replace the original transition..." << std::endl;
#endif
						continue;
					}
					super_from_node->addTransition(*new_transition);
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
					std::cout << "[DomainTransitionGraph::solveSubsets] Use org node: New transition: " << *new_transition << "." << std::endl;
#endif
				}
			}
		}
		// Remove all the transitions from the super node so it will be marked for removal.
		from_node_to_replace->removeTransitions();
	}

	// Free up used memory.
	for (std::map<DomainTransitionGraphNode*, std::vector<std::pair<DomainTransitionGraphNode*, unsigned int*> >* >::const_iterator ci = sub_to_super_nodes.begin(); ci != sub_to_super_nodes.end(); ci++)
	{
		for (std::vector<std::pair<DomainTransitionGraphNode*, unsigned int*> >::const_iterator ci2 = (*ci).second->begin(); ci2 != (*ci).second->end(); ci2++)
		{
			delete[] (*ci2).second;
		}
		delete (*ci).second;
	}
}

void DomainTransitionGraph::separateObjects(const RecursiveFunctionManager& recursive_function_manager)
{
	for (std::vector<std::vector<const Object*>* >::iterator i = objects_sets_.begin(); i != objects_sets_.end(); i++)
	{
		delete *i;
	}
	objects_sets_.clear();
	
	std::map<const Object*, boost::dynamic_bitset<> > evaluation_results;
	recursive_function_manager.evaluateObjects(evaluation_results, objects_);
	std::set<const Object*> closed_list;
	
	while (closed_list.size() != objects_.size())
	{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
		std::cout << "Start new group" << std::endl;
#endif
		std::vector<const Object*>* current_objects = new std::vector<const Object*>();
		boost::dynamic_bitset<>* current_bit_set = NULL;
		for (std::vector<const Object*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
		{
			const Object* object = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "Process object: " << *object << std::endl;
#endif
			
			if (closed_list.count(object) != 0)
			{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
				std::cout << "[closed list!]" << std::endl;
#endif
				continue;
			}
			
			boost::dynamic_bitset<>& bit_set = evaluation_results[object];
			
			if (current_bit_set == NULL)
			{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
				std::cout << "Start new bitset: " << bit_set << std::endl;
#endif
				current_bit_set = &bit_set;
				current_objects->push_back(object);
			}
			else if (bit_set == *current_bit_set)
			{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
				std::cout << "Add to current bitset" << std::endl;
#endif
				current_objects->push_back(object);
			}
			
			closed_list.insert(object);
		}

#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
		std::cout << "Grouped objects: ";
		for (std::vector<const Object*>::const_iterator ci = current_objects->begin(); ci != current_objects->end(); ci++)
		{
			const Object* object = *ci;
			std::cout << *object;
			if (ci != current_objects->end() - 1)
			{
				std::cout << ", ";
			}
		}
		std::cout << std::endl;
#endif
		objects_sets_.push_back(current_objects);
	}
}

std::ostream& operator<<(std::ostream& os, const DomainTransitionGraph& dtg)
{
	os << "{ ";
	for (std::vector<const Object*>::const_iterator ci2 = dtg.objects_.begin(); ci2 != dtg.objects_.end(); ci2++)
	{
		const Object* object = *ci2;
		os << *object;
		
		if (ci2 + 1 != dtg.objects_.end())
		{
			os << ", ";
		}
	}
	os << "}";
	
	os << "< ";
	for (std::vector<std::vector<const Object*>* >::const_iterator ci = dtg.objects_sets_.begin(); ci != dtg.objects_sets_.end(); ci++)
	{
		std::vector<const Object*>* objects = *ci;
		
		os << "{ ";
		for (std::vector<const Object*>::const_iterator ci2 = objects->begin(); ci2 != objects->end(); ci2++)
		{
			const Object* object = *ci2;
			os << *object;
			
			if (ci2 + 1 != objects->end())
			{
				os << ", ";
			}
		}
		os << "}";
		if (ci + 1 != dtg.objects_sets_.end())
		{
			os << ", ";
		}
	}
	os << " >" << std::endl;
	
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
