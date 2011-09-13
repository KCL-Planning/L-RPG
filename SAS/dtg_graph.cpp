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

///#define MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS

namespace MyPOP {

namespace SAS_Plus {

/*DTGBindings::DTGBindings(const TermManager& term_manager, const BindingsPropagator& propagator)
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
			    node1.getIndex(*bounded_atom1) == node2.getIndex(*bounded_atom2) &&
			    bounded_atom1->getAtom().isNegative() == bounded_atom2->getAtom().isNegative())
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

bool DTGBindings::canUnifyBoundedAtoms(const BoundedAtom& bounded_atom1, const BoundedAtom& bounded_atom2) const
{
	return canUnify(bounded_atom1.getAtom(), bounded_atom1.getId(), bounded_atom2.getAtom(), bounded_atom2.getId());
}*/

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

	delete bindings_;
	delete dtg_term_manager_;
}

bool DomainTransitionGraph::addNode(DomainTransitionGraphNode& dtg_node, std::vector<DomainTransitionGraphNode*>* added_nodes)
{
/*	assert (&dtg_node.getDTG() == this);
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
*/
	assert (&dtg_node.getDTG() == this);
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
					dtg_node->addAtom(&bounded_atom, index);
//					StepID unique_nr = bindings_->createVariableDomains(*atom);
//					dtg_node->addAtom(new BoundedAtom(unique_nr, *atom, property), index);
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
//	StepID unique_nr = bindings_->createVariableDomains(atom);

	static unsigned int unique_id = 0;
	
	DomainTransitionGraphNode* dtg_node = new DomainTransitionGraphNode(*this, unique_id++);
	
	BoundedAtom* new_bounded_atom = NULL;
	
	if (property == NULL)
		new_bounded_atom = &BoundedAtom::createBoundedAtom(atom, *bindings_);
	else
		new_bounded_atom = &BoundedAtom::createBoundedAtom(atom, *property, *bindings_);
	
	dtg_node->addAtom(new_bounded_atom, index);
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

void DomainTransitionGraph::getNodes(std::vector<std::pair<const SAS_Plus::DomainTransitionGraphNode*, const BoundedAtom*> >& dtg_nodes, StepID step_id, const Atom& atom, const Bindings& bindings, InvariableIndex index) const
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;

		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;

//			std::cout << "[DomainTransitionGraph::getNodes] Compare: ";
//			bounded_atom->print(std::cout, dtg_node->getDTG().getBindings());
//			std::cout << "(" << dtg_node->getIndex(*bounded_atom) << ") v.s. ";
//			atom.print(std::cout, bindings, step_id);
//			std::cout << std::endl;
			
			if (bindings_->canUnify(bounded_atom->getAtom(), bounded_atom->getId(), atom, step_id, &bindings) &&
				(index == ALL_INVARIABLE_INDEXES || 
				dtg_node->getIndex(*bounded_atom) == index))
			{
///				std::cout << "SUCCES!!!" << std::endl;
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
		
//		std::cout << "*** The DTG node: ";
//		nodes_[i]->print(std::cout);
//		std::cout << " has the bitset: " << *reachable_nodes << std::endl;
		
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
		
		grouped_dtg_nodes[*reachable_nodes] = new_group;
	}
	
	gettimeofday(&end_time, NULL);
	time_spend = end_time.tv_sec - start_time.tv_sec + (end_time.tv_usec - start_time.tv_usec) / 1000000.0;
	std::cerr << " * Group together: " << time_spend << " seconds" << std::endl;

	gettimeofday(&start_time, NULL);
	
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

		DomainTransitionGraph* new_dtg = new DomainTransitionGraph(*dtg_manager_, dtg_term_manager_->getTypeManager(), *action_manager_, *predicate_manager_, *bindings_, *initial_facts_);
		struct timeval dtg_construct_end;
		gettimeofday(&dtg_construct_end, NULL);
		time_spend_dtgs += dtg_construct_end.tv_sec - dtg_construct_start.tv_sec + (dtg_construct_end.tv_usec - dtg_construct_start.tv_usec) / 1000000.0;
		
		/**
		 * Copy all aspects of this DTG, except for the DTG nodes.
		 */
		new_dtg->objects_ = objects_;
		new_dtg->predicates_ = predicates_;
		new_dtg->type_ = type_;
		new_dtg->property_spaces_ = property_spaces_;
		
		struct timeval add_dtg_nodes_start;
		gettimeofday(&add_dtg_nodes_start, NULL);
		
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
		
//		std::cout << "New sub DTG: " << *new_dtg << std::endl;
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
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "=== ReestablishTransitions: === (" << bindings_->getNr() << ") " << std::endl << *this << std::endl;
#endif
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

			// Otherwise try all these transitiosn.
			for (std::vector<const Action*>::const_iterator ci = possible_transitions.begin(); ci != possible_transitions.end(); ci++)
			{
				const Action* action = *ci;
				Transition* transition = Transition::createTransition(*action, *from_node, *to_node, *initial_facts_);
				if (transition != NULL)
				{
					from_node->addTransition(*transition, false);
				}
			}
		}
	}
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "=== Result: === (" << bindings_->getNr() << ") " << std::endl << *this << std::endl;
#endif
}

void DomainTransitionGraph::establishTransitions()
{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "Establish transitions for: (" << bindings_->getNr() << ") " << *this << std::endl;
#endif
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		(*ci)->removeTransitions(true);
	}
	
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
				
				if (from_node == to_node)
				{
					to_node = new DomainTransitionGraphNode(*to_node, false, false);
				}
				
				Transition* transition = Transition::createTransition(*action, *from_node, *to_node, *initial_facts_);
				if (transition != NULL)
				{
					from_node->addTransition(*transition, true);
					new_nodes.push_back(to_node);
				}
			}
		}
	}
	
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = new_nodes.begin(); ci != new_nodes.end(); ci++)
	{
		addNode(**ci);
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "=== Result: === (" << bindings_->getNr() << ") " << std::endl << *this << std::endl;
#endif
}

bool DomainTransitionGraph::splitNodes(const std::map<DomainTransitionGraph*, std::vector<DomainTransitionGraph*>* >& split_graphs)
{
	bool affected = false;
//	std::cout << "[DomainTransitionGraph::splitNodes] Process DTG: " << *this << std::endl;
	for (std::map<DomainTransitionGraph*, std::vector<DomainTransitionGraph*>* >::const_iterator ci = split_graphs.begin(); ci != split_graphs.end(); ci++)
	{
		DomainTransitionGraph* splitted_dtg = (*ci).first;
		std::vector<DomainTransitionGraph*>* results_of_split = (*ci).second;
		
//		std::cout << "Process splitted DTG: " << *splitted_dtg << std::endl;
//		std::cout << "Splitted into: ";
//		for (std::vector<DomainTransitionGraph*>::const_iterator ci = results_of_split->begin(); ci != results_of_split->end(); ci++)
//		{
//			std::cout << **ci << std::endl;
//		}
		
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
					std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > matched_dtg_nodes;
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
					const Term* affected_term = NULL;
					for (std::vector<BoundedAtom*>::const_iterator ci = matched_dtg_nodes[0].first->getAtoms().begin(); ci != matched_dtg_nodes[0].first->getAtoms().end(); ci++)
					{
						if (bindings_->canUnify(*precondition, transition->getStep()->getStepId(), (*ci)->getAtom(), (*ci)->getId(), &splitted_dtg->getBindings()))
						{
							affected_term = precondition->getTerms()[matched_dtg_nodes[0].first->getIndex(**ci)];
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
//						std::cout << "Affected <atoms, variables> for ";
//						dtg_node->print(std::cout);
//						std::cout << ": ";
						for (unsigned int atom_nr = 0; atom_nr < dtg_node->getAtoms().size(); atom_nr++)
						{
							const BoundedAtom* bounded_atom = dtg_node->getAtoms()[atom_nr];
							//for (std::vector<const Term*>::const_iterator ci = bounded_atom->getTerms().begin(); ci != bounded_atom->getTerms().end(); ci++)
							for (unsigned int variable_nr = 0; variable_nr < bounded_atom->getAtom().getTerms().size(); variable_nr++)
							{
								const Term* term = bounded_atom->getAtom().getTerms()[variable_nr];
								if (term->isTheSameAs(bounded_atom->getId(), *affected_term, transition->getStep()->getStepId(), *bindings_))
								{
//									std::cout << "<" << atom_nr << ", " << variable_nr << "> ";
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
						
//						std::cout << std::endl;
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
//				std::cout << "Counter: {";
//				for (unsigned int i = 0; i < affected_variables.size(); i++)
//				{
//					std::cout << counter[i] << ", ";
//				}
//				std::cout << "}" << std::endl;
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
				
//				std::cout << "New node! " << *new_node << std::endl;
				//addNode(*new_node);
				nodes_to_add.push_back(new_node);
				
				/**
				 * Update counter.
				 * Check if we have reached the maximum of the current counter.
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
		
		if (nodes_to_add.size() > 0)
		{
			affected = true;
		}
	}
	
	return affected;
}

void DomainTransitionGraph::solveSubsets()
{
	// Find a pairing of nodes of which one is a subset of the other.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		DomainTransitionGraphNode* dtg_node = *ci;
		std::vector<DomainTransitionGraphNode*> subset_dtg_nodes;
		dtg_node->getSubsets(subset_dtg_nodes, nodes_);
		
		/**
		 * There are 3 types of subset relationships;
		 * 1) The nodes are identical - in this case we can ignore the subset as it means the node is exactly the same. If this is not the
		 * case than that is a bug, because those nodes should have been merged when we created the combined DTG.
		 * 2) The subset contains less facts but is otherwise identical. If this is the case than we copy all the transitions from the subset
		 * to this node.
		 * 3) The subset might have the same number of facts, but some of them are grounded. In this case we need to ground the superset and 
		 * apply the transitions to the subset and remove the superset.
		 */
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
		std::cout << "The subsets of : " << *dtg_node << " are: " << std::endl;
#endif
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = subset_dtg_nodes.begin(); ci != subset_dtg_nodes.end(); ci++)
		{
			DomainTransitionGraphNode* sub_set_dtg_node = *ci;
			
			// Case 1: ignore.
			if (sub_set_dtg_node == dtg_node) {
				continue;
			}
			
			// Case 2:
			bool is_equivalent_sub_set = true;
			
			// Case 3:
			bool is_equivalent_grounded_sub_set = false;
			for (std::vector<BoundedAtom*>::const_iterator ci = sub_set_dtg_node->getAtoms().begin(); ci != sub_set_dtg_node->getAtoms().end(); ci++) {
				const BoundedAtom* sub_set_fact = *ci;
				bool equivalent_fact_found = false;
				bool super_set_fact_found = false;
				
				for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++) {
					const BoundedAtom* fact = *ci;
					
					if (fact->isEquivalentTo(*sub_set_fact, *bindings_))
					{
						equivalent_fact_found = true;
						break;
					}
					else if (fact->isProperSuperSetOf(*sub_set_fact, *bindings_))
					{
						// Check if the properties align.
						if (sub_set_fact->getProperties().size() != fact->getProperties().size())
						{
							continue;
						}
						
						bool all_properties_found = true;
						for (std::vector<const Property*>::const_iterator ci = sub_set_fact->getProperties().begin(); ci != sub_set_fact->getProperties().end(); ci++)
						{
							bool found = false;
							const Property* property = *ci;
							for (std::vector<const Property*>::const_iterator ci = fact->getProperties().begin(); ci != fact->getProperties().end(); ci++)
							{
								if (*property == **ci)
								{
									found = true;
									break;
								}
							}
							
							if (!found)
							{
								all_properties_found = false;
								break;
							}
						}
						
						if (all_properties_found)
						{
							super_set_fact_found = true;
							break;
						}
					}
				}
				
				if (!equivalent_fact_found) {
					is_equivalent_sub_set = false;
				}
				
				if (super_set_fact_found) {
					is_equivalent_grounded_sub_set = true;
				}
				
				if (!equivalent_fact_found && !super_set_fact_found) {
					is_equivalent_grounded_sub_set = false;
					break;
				}
			}
			
			// Case 2:
			if (is_equivalent_sub_set)
			{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
				std::cout << "Proper subset: " << *sub_set_dtg_node << "." << std::endl;
#endif
				for (std::vector<const Transition*>::const_iterator ci = sub_set_dtg_node->getTransitions().begin(); ci != sub_set_dtg_node->getTransitions().end(); ci++)
				{
					dtg_node->addTransition(**ci, false);
				}
			}
			
			// Case 3:
			// Map the terms of the super set to those of the sub set. Then we iterate through all transitions from the super node
			// and construct the to nodes, mapping the terms to those of the sub set. The resulting set of facts are a new node to 
			// construct a transition to from the sub set.
			if (is_equivalent_grounded_sub_set && 
			    dtg_node->getAtoms().size() == sub_set_dtg_node->getAtoms().size()) // TEST Temporary contraint for depots.
			{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
				std::cout << "Proper grounded subset: " << *sub_set_dtg_node << "." << std::endl;
#endif
				
				// Super set term -> Sub set term.
				std::map<const std::vector<const Object*>*, const std::vector<const Object*>* > super_to_sub_mapping;
				
				// Find out which terms to ground.
				for (std::vector<BoundedAtom*>::const_iterator ci = sub_set_dtg_node->getAtoms().begin(); ci != sub_set_dtg_node->getAtoms().end(); ci++)
				{
					const BoundedAtom* sub_set_fact = *ci;
					
					const BoundedAtom* found_super_set = NULL;
					const BoundedAtom* found_equivalent = NULL;
					
					for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
					{
						const BoundedAtom* fact = *ci;
						
						bool properties_align = true;
						for (std::vector<const Property*>::const_iterator ci = sub_set_fact->getProperties().begin(); ci != sub_set_fact->getProperties().end(); ci++)
						{
							bool property_aligns = false;
							const Property* property = *ci;
							for (std::vector<const Property*>::const_iterator ci = sub_set_fact->getProperties().begin(); ci != sub_set_fact->getProperties().end(); ci++)
							{
								if (*property == **ci)
								{
									property_aligns = true;
									break;
								}
							}
							
							if (!property_aligns)
							{
								properties_align = false;
								break;
							}
						}
						
						if (!properties_align)
						{
							continue;
						}
						
						if (fact->isEquivalentTo(*sub_set_fact, *bindings_))
						{
							found_equivalent = fact;
						}
						
						else if (fact->isProperSuperSetOf(*sub_set_fact, *bindings_))
						{
							found_super_set = fact;
						}
					}
					
					if (found_equivalent != NULL)
						continue;
					
					// If we have not found an equivalent fact we know that we have found a super set.
					assert (found_super_set != NULL);
					
					// Check which term differs.
					for (unsigned int i = 0; i < sub_set_fact->getAtom().getArity(); i++)
					{
						const Term* sub_set_term = sub_set_fact->getAtom().getTerms()[i];
						const Term* super_set_term = found_super_set->getAtom().getTerms()[i];
						
						if (sub_set_term->isProperSubSetOf(sub_set_fact->getId(), *super_set_term, found_super_set->getId(), *bindings_))
						{
							super_to_sub_mapping[&super_set_term->getDomain(found_super_set->getId(), *bindings_)] = &sub_set_term->getDomain(sub_set_fact->getId(), *bindings_);
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
							std::cout << "Bind the fact: ";
							super_set_term->print(std::cout, *bindings_, found_super_set->getId());
							std::cout << " to ";
							sub_set_term->print(std::cout, *bindings_, sub_set_fact->getId());
							std::cout << "." << std::endl;
#endif
						}
					}
				}
				
				// Check all transitions and construct the to nodes based on the constructed mapping.
				for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
				{
					const Transition* transition = *ci;
					
					const DomainTransitionGraphNode& to_dtg_node = transition->getToNode();
					
					// Construct the new DTG node.
					DomainTransitionGraphNode* new_to_node = new DomainTransitionGraphNode(*this, 0);
					
					for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node.getAtoms().begin(); ci != to_dtg_node.getAtoms().end(); ci++)
					{
						const BoundedAtom* org_to_atom = *ci;
						
						std::vector<const Term*>* new_terms = new std::vector<const Term*>();
						for (std::vector<const Term*>::const_iterator ci = org_to_atom->getAtom().getTerms().begin(); ci != org_to_atom->getAtom().getTerms().end(); ci++)
						{
							const Term* org_term = *ci;
							Term* new_term = new Variable(*org_term->getType(), org_term->getName());
							new_terms->push_back(new_term);
						}
						
						const Atom* new_atom = new Atom(org_to_atom->getAtom().getPredicate(), *new_terms, org_to_atom->getAtom().isNegative());
						StepID new_step_id = bindings_->createVariableDomains(*new_atom);
						
						// Prune the domains of the newely created atom to reflect the mapping between the super and sub set.
						for (unsigned int i = 0; i < new_atom->getArity(); i++)
						{
							const Term* new_term = new_atom->getTerms()[i];
							const Term* org_term = org_to_atom->getAtom().getTerms()[i];
							
							std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >::const_iterator found_mapping = super_to_sub_mapping.find(&org_term->getDomain(org_to_atom->getId(), *bindings_));
							if (found_mapping == super_to_sub_mapping.end())
								continue;
							
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
							std::cout << "Modify domain from..." << std::endl;
							new_term->print(std::cout, *bindings_, new_step_id);
							std::cout << " to ...";
							
							const std::vector<const Object*>* new_objects = (*found_mapping).second;
							for (std::vector<const Object*>::const_iterator ci = new_objects->begin(); ci != new_objects->end(); ci++)
							{
								std::cout << **ci << ", ";
							}
							std::cout << std::endl;
#endif
							
							new_term->makeDomainEqualTo(new_step_id, *(*found_mapping).second, *bindings_);
							
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
							std::cout << "Result: ";
							new_term->print(std::cout, *bindings_, new_step_id);
							std::cout << "." << std::endl;
#endif
						}
						
						BoundedAtom* bounded_atom = new BoundedAtom(new_step_id, *new_atom, org_to_atom->getProperties());
						new_to_node->addAtom(bounded_atom, to_dtg_node.getIndex(*org_to_atom));
					}
					
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
					std::cout << " Newly created grounded to node: " << *new_to_node << "." << std::endl;
#endif

					// Check if this node actually exists, if this is the case we create a new transition.
					DomainTransitionGraphNode* existing_to_dtg_node = NULL;
					for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
					{
						DomainTransitionGraphNode* dtg_node = *ci;
						if (dtg_node->isEquivalentTo(*new_to_node))
						{
							existing_to_dtg_node = dtg_node;
							break;
						}
					}
					
					if (existing_to_dtg_node == NULL)
					{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
						std::cout << "Create a new DTG node: " << *new_to_node << std::endl;
#endif
						addNode(*new_to_node);
						
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
						std::cout << "Create a transition from: " << *sub_set_dtg_node << " to " << *new_to_node << std::endl;
#endif
						Transition* new_transition = Transition::createTransition(transition->getStep()->getAction(), *sub_set_dtg_node, *new_to_node, *initial_facts_);
						assert (new_transition != NULL);
						sub_set_dtg_node->addTransition(*new_transition, false);
					}
					else
					{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
						std::cout << "Create a transition from: " << *sub_set_dtg_node << " to " << *existing_to_dtg_node << std::endl;
#endif
						Transition* new_transition = Transition::createTransition(transition->getStep()->getAction(), *sub_set_dtg_node, *existing_to_dtg_node, *initial_facts_);
						assert (new_transition != NULL);
						sub_set_dtg_node->addTransition(*new_transition, false);
					}
				}
			}
		}
	}
}

void DomainTransitionGraph::splitSelfReferencingNodes()
{
	std::vector<DomainTransitionGraphNode*> nodes_to_add;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator nodes_ci = nodes_.begin(); nodes_ci != nodes_.end(); nodes_ci++)
	{
		DomainTransitionGraphNode* dtg_node = *nodes_ci;
		std::vector<std::pair<const Action*, DomainTransitionGraphNode*> > transitions_to_add;
		
		for (std::vector<const Transition*>::const_reverse_iterator ci = dtg_node->getTransitions().rbegin(); ci != dtg_node->getTransitions().rend(); ci++)
		{
			const Transition* transition = *ci;
			
			if (&transition->getToNode() != dtg_node) continue;
			
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "Found a self referencing transition!!! " << *transition << "." << std::endl;
#endif
			
			// If a transition references to the same DTG we need to split it into two!
			DomainTransitionGraphNode* clone_node = new DomainTransitionGraphNode(*dtg_node, *this);
			
			transitions_to_add.push_back(std::make_pair(&transition->getStep()->getAction(), clone_node));
			assert (clone_node->addTransition(transition->getStep()->getAction(), *dtg_node));
			
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "Created clone node: " << *clone_node << std::endl;
#endif
			
			nodes_to_add.push_back(clone_node);
			
			dtg_node->removeTransition(*transition);
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
		std::cout << "After adding clone transition: " << *dtg_node << std::endl;
		
		std::cout << "Add transitions from the original node to the clone node: " << std::endl;
#endif
		for (std::vector<std::pair<const Action*, DomainTransitionGraphNode*> >::const_iterator ci = transitions_to_add.begin(); ci != transitions_to_add.end(); ci++)
		{
			dtg_node->addTransition(*(*ci).first, *(*ci).second);
		}
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
		std::cout << "After adding all transitions: " << *dtg_node << std::endl;
#endif
	}
	
	nodes_.insert(nodes_.end(), nodes_to_add.begin(), nodes_to_add.end());
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

bool DomainTransitionGraph::removeUnsupportedTransitions()
{
	bool graph_affected = false;
	for (std::vector<DomainTransitionGraphNode*>::reverse_iterator ci = nodes_.rbegin(); ci != nodes_.rend(); ci++)
	{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
		std::cout << "Remove the unsupported transitions from the DTG node: ";
		(*ci)->print(std::cout);
		std::cout << std::endl;
#endif
		if ((*ci)->removeUnsupportedTransitions())
		{
			graph_affected = true;
		}
		
		// If one of the variable domains is empty, remove the node.
		if ((*ci)->containsEmptyVariableDomain())
		{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "Remove the node: ";
			(*ci)->print(std::cout);
			std::cout << std::endl;
#endif
			removeNode(**ci);
			graph_affected = true;
		}
	}
	
	return graph_affected;
}

void DomainTransitionGraph::merge(const MyPOP::SAS_Plus::DomainTransitionGraph& other)
{
	property_spaces_.insert(property_spaces_.end(), other.property_spaces_.begin(), other.property_spaces_.end());
	
	for (std::vector<const Property*>::const_iterator ci = other.predicates_.begin(); ci != other.predicates_.end(); ci++)
	{
		const Property* property_to_merge = *ci;
		bool exists = false;
		for (std::vector<const Property*>::const_iterator ci = predicates_.begin(); ci != predicates_.end(); ci++)
		{
			const Property* existing_property = *ci;
			if (property_to_merge == existing_property)
			{
				exists = true;
				break;
			}
		}
		
		if (!exists)
		{
			predicates_.push_back(property_to_merge);
		}
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

void DomainTransitionGraph::mergeInvariableDTGs()
{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "[DomainTransitionGraph::mergeInvariableDTGs] " << *this << std::endl;
#endif
	std::vector<DomainTransitionGraphNode*> nodes_to_remove;
	std::vector<DomainTransitionGraphNode*> nodes_to_add;
		
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		DomainTransitionGraphNode* from_dtg_node = *ci;
		
		for (std::vector<const Transition*>::const_iterator ci = from_dtg_node->getTransitions().begin(); ci != from_dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;

#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "* Transition: from " << std::endl;
			transition->getFromNode().print(std::cout);
			std::cout << std::endl << " to " << std::endl;
			transition->getToNode().print(std::cout);
			std::cout << std::endl << "[" << transition->getStep()->getAction() << "]" << std::endl;
#endif

			const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
			
			// Check which of the preconditions of this action refers to an external DTG.
			for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
			{
				const Atom* precondition = (*ci).first;
				InvariableIndex invariable = (*ci).second;

#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
				std::cout << " * * Process the precondition: ";
				precondition->print(std::cout, *bindings_, transition->getStep()->getStepId());
				std::cout << "(" << invariable << ")" << std::endl;
#endif

				/**
				 * If the precondition isn't linked to the invariable of this DTG node there are two scenarios:
				 * - The precondition is part of another DTG node and its invariable is linked to a node in the from_node. If this is the
				 * case then the precondition must be merged with this node.
				 * - If the precondition's invariable is not linked to this node we need to ground it.
				 */
				if (invariable == NO_INVARIABLE_INDEX)
				{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
					std::cout << " * * * The precondition isn't linked to the invariable. Check if the term is invariable in another DTG." << std::endl;
#endif
					// Check if the precondition is invariable in their respective DTG(s).
					std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > matching_dtg_nodes;
					dtg_manager_->getDTGNodes(matching_dtg_nodes, transition->getStep()->getStepId(), *precondition, *bindings_);
					
					///InvariableIndex precondition_invariable = NO_INVARIABLE_INDEX;
					///const Property* precondition_property = NULL;
					std::vector<std::pair<InvariableIndex, const Property*> > precondition_properties;
					bool merge_with_self = false;
					
					for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = matching_dtg_nodes.begin(); ci != matching_dtg_nodes.end(); ci++)
					{
						const DomainTransitionGraphNode* matching_dtg_node = (*ci).first;
						
/*						if (&matching_dtg_node->getDTG() == dtg)
						{
							std::cout << "Alert! Proposing a DTG to merge with itself!!!" << std::endl;
							continue;
						}*/
						
						// Figure out what the invariable is.
						for (std::vector<BoundedAtom*>::const_iterator ci = matching_dtg_node->getAtoms().begin(); ci != matching_dtg_node->getAtoms().end(); ci++)
						{
							const BoundedAtom* bounded_atom = *ci;
							if (bindings_->canUnify(*precondition, transition->getStep()->getStepId(), bounded_atom->getAtom(), bounded_atom->getId(), &matching_dtg_node->getDTG().getBindings()))
							{
								InvariableIndex matching_invariable_index = matching_dtg_node->getIndex(*bounded_atom);

#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
								std::cout << " * * * * Precondition is invariable in the DTG node: ";
								matching_dtg_node->print(std::cout);
								std::cout << "[" << matching_invariable_index << "]" << std::endl;
#endif
								
								// TEST
								if (matching_invariable_index == NO_INVARIABLE_INDEX) continue;
								
								assert (&matching_dtg_node->getDTG() != NULL);
								
								bool propose_merge_with_self = false;
								for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
								{
									const Property* property = *ci;
									
									if (containsPropertySpace(property->getPropertyState().getPropertySpace()))
									{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
										std::cout << " * * * * Alert! Proposing a DTG to merge with itself!!!" << std::endl;
#endif
										propose_merge_with_self = true;
										break;
									}
								}
								
								if (propose_merge_with_self)
								{
									continue;
								}
								
								for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
								{
									const Property* property = *ci;
									precondition_properties.push_back(std::make_pair(matching_invariable_index, property));

#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
									std::cout << " * * * * Candidate to bind: ";
									bounded_atom->print(std::cout, matching_dtg_node->getDTG().getBindings());
									std::cout << "[" << &property->getPropertyState().getPropertySpace() << "]" << std::endl;
									
									std::cout << " * * * * From DTG node: ";
									matching_dtg_node->print(std::cout);
									std::cout << " (pointer address=" << &matching_dtg_node->getDTG() << ")" << std::endl;
#endif
								}
/*
								if (containsPropertySpace(bounded_atom->getProperty()->getPropertyState().getPropertySpace()))
								{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
									std::cout << " * * * * Alert! Proposing a DTG to merge with itself!!!" << std::endl;
#endif
									// TODO: Fix this bit :).
//									merge_with_self = true;
//									precondition_properties.clear();

//									break;
									continue;
								}

								precondition_properties.push_back(std::make_pair(matching_invariable_index, bounded_atom->getProperty()));

#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
								std::cout << " * * * * Candidate to bind: ";
								bounded_atom->print(std::cout, matching_dtg_node->getDTG().getBindings());
								std::cout << "[" << &bounded_atom->getProperty()->getPropertyState().getPropertySpace() << "]" << std::endl;
								
								std::cout << " * * * * From DTG node: ";
								matching_dtg_node->print(std::cout);
								std::cout << " (pointer address=" << &matching_dtg_node->getDTG() << ")" << std::endl;
#endif
*/
							}
						}
						
						if (merge_with_self)
						{
							break;
						}
					}
					
					/**
					 * Not sure what to do if the same precondition is able to get two new atoms in the DTG node...
					 */
					unsigned int counter = 0;
					
					for (std::vector<std::pair<InvariableIndex, const Property*> >::const_iterator ci = precondition_properties.begin(); ci != precondition_properties.end(); ci++)
					{
						
						InvariableIndex precondition_invariable = (*ci).first;
						const Property* precondition_property = (*ci).second;
						/**
						 * Check if the variable in the precondition is present in the from node. If this is not
						 * the case then the value of this variable is irrelevant.
						 */
						bool need_to_merge = false;
						bool already_exists = false;
						for (std::vector< BoundedAtom*>::const_iterator ci = from_dtg_node->getAtoms().begin(); ci != from_dtg_node->getAtoms().end(); ci++)
						{
							const BoundedAtom* bounded_atom = *ci;
							
							for (std::vector<const Term*>::const_iterator ci = bounded_atom->getAtom().getTerms().begin(); ci != bounded_atom->getAtom().getTerms().end(); ci++)
							{
								const Term* term = *ci;
								
								if (term->isTheSameAs(bounded_atom->getId(), *precondition->getTerms()[precondition_invariable], transition->getStep()->getStepId(), *bindings_))
								{
									need_to_merge = true;
								}
								
								if (from_dtg_node->getDTG().getBindings().canUnify(bounded_atom->getAtom(), bounded_atom->getId(), *precondition, transition->getStep()->getStepId(), bindings_))
								{
									already_exists = true;
									break;
								}
							}
							
							// TEST
							if (already_exists) break;
						}
						
						if (need_to_merge && !already_exists)
						{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
							std::cout << " * * * Need to merge external invariable: ";
							precondition->print(std::cout, *bindings_, transition->getStep()->getStepId());
							std::cout << "(" << precondition_invariable << ") property space: " << &precondition_property->getPropertyState().getPropertySpace() << std::endl;
#endif
							assert (counter == 0);
							++counter;

							//StepID external_invariable_id = bindings_->createVariableDomains(*precondition);
							
							BoundedAtom& new_bounded_atom = BoundedAtom::createBoundedAtom(*precondition, *precondition_property, *bindings_);
							
							from_dtg_node->addAtom(&new_bounded_atom, precondition_invariable);
//							from_dtg_node->addAtom(new BoundedAtom(external_invariable_id, *precondition, precondition_property), precondition_invariable);
						}
					}
				}
			}
		}
	}
	establishTransitions();
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
