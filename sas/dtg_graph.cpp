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
	: dtg_manager_(&dtg_manager), property_space_(NULL), type_manager_(&type_manager), dtg_term_manager_(new TermManager(type_manager)), action_manager_(&action_manager), predicate_manager_(&predicate_manager), bindings_(&bindings), initial_facts_(&initial_facts), type_(NULL)
{

}

DomainTransitionGraph::~DomainTransitionGraph()
{
	// Delete all the domain transition graph nodes.
	for (std::vector<DomainTransitionGraphNode*>::iterator i = nodes_.begin(); i != nodes_.end(); i++)
	{
		delete *i;
	}
	
	delete property_space_;
	delete dtg_term_manager_;
}

DomainTransitionGraph* DomainTransitionGraph::merge(const DomainTransitionGraph& lhs, const DomainTransitionGraph& rhs)
{
	std::vector<const Object*> objects_intersection(std::min(lhs.objects_.size(), rhs.objects_.size()));
	std::vector<const Object*>::const_iterator end_intersection = std::set_intersection(lhs.objects_.begin(), lhs.objects_.end(), rhs.objects_.begin(), rhs.objects_.end(), objects_intersection.begin());
	unsigned int intersection_size = end_intersection - objects_intersection.begin();
	if (intersection_size != rhs.objects_.size() || intersection_size != lhs.objects_.size())
	{
		return NULL;
	}
	
	// Merge the property spaces.
	PropertySpace* merged_property_space = PropertySpace::merge(*lhs.property_space_, *rhs.property_space_);
	DomainTransitionGraph* merged_dtg = new DomainTransitionGraph(*lhs.dtg_manager_, *lhs.type_manager_, *lhs.action_manager_, *lhs.predicate_manager_, *lhs.bindings_, *lhs.initial_facts_);
	
	merged_dtg->addBalancedSet(*merged_property_space, true);
	merged_dtg->establishTransitions();
	//merged_dtg->updateObjects();
	
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "Merging " << std::endl;
	std::cout << lhs << std::endl;
	std::cout << " and " << std::endl;
	std::cout << rhs << std::endl;
	std::cout << "Result: " << std::endl;
	std::cout << *merged_dtg << std::endl;
#endif
	
	return merged_dtg;
}

void DomainTransitionGraph::ground(const std::vector<const Object*>& objects_not_to_ground, const std::vector<const Atom*>& initial_facts, const TermManager& term_manager)
{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "[DomainTransitionGraph::ground] " << std::endl << *this << std::endl;
#endif

	// Determine which objects are different due to static constraints.
	std::map<const Object*, std::vector<const Atom*>* > object_to_static_constraints_mapping;
	for (std::vector<const Object*>::const_iterator ci = term_manager.getAllObjects().begin(); ci != term_manager.getAllObjects().end(); ++ci)
	{
		const Object* object = *ci;
		std::vector<const Atom*>* static_constraints = new std::vector<const Atom*>();
		object_to_static_constraints_mapping[object] = static_constraints;
		for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ++ci)
		{
			const Atom* initial_fact = *ci;
			if (!initial_fact->getPredicate().isStatic())
			{
				continue;
			}
			
			for (std::vector<const Term*>::const_iterator ci = initial_fact->getTerms().begin(); ci != initial_fact->getTerms().end(); ++ci)
			{
				const Term* term = *ci;
				const std::vector<const Object*>& variable_domain = term->getDomain(Step::INITIAL_STEP, *bindings_);
				if (std::find(variable_domain.begin(), variable_domain.end(), object) != variable_domain.end())
				{
					static_constraints->push_back(initial_fact);
					break;
				}
			}
		}
	}
	
	// Next, compare all the static constraints of all the objects and merge those which share the same static contraints.
	std::multimap<const Object*, const Object*> equivalent_relationships;
	for (std::map<const Object*, std::vector<const Atom*>* >::const_iterator ci = object_to_static_constraints_mapping.begin(); ci != object_to_static_constraints_mapping.end(); ++ci)
	{
		const Object* object = (*ci).first;
		const std::vector<const Atom*>* static_facts = (*ci).second;
		
		for (std::map<const Object*, std::vector<const Atom*>* >::const_iterator ci = object_to_static_constraints_mapping.begin(); ci != object_to_static_constraints_mapping.end(); ++ci)
		{
			const Object* other_object = (*ci).first;
			const std::vector<const Atom*>* other_static_facts = (*ci).second;
			if (other_object == object || static_facts->size() != other_static_facts->size() || object->getType() != other_object->getType())
			{
				continue;
			}
			
			// Make sure that all the static facts are shared and identical.
			bool all_static_constraints_shared = true;
			for (std::vector<const Atom*>::const_iterator ci = static_facts->begin(); ci != static_facts->end(); ++ci)
			{
				const Atom* static_fact = *ci;
				bool shares_static_constraint = false;
				for (std::vector<const Atom*>::const_iterator ci = other_static_facts->begin(); ci != other_static_facts->end(); ++ci)
				{
					const Atom* other_static_fact = *ci;
					if (static_fact->getArity() != other_static_fact->getArity() ||
					    static_fact->getPredicate().getName() != other_static_fact->getPredicate().getName())
					{
						continue;
					}
					
					bool terms_match = true;
					for (unsigned int i = 0; i < static_fact->getArity(); ++i)
					{
						const Object* o1 = static_fact->getTerms()[i]->getDomain(Step::INITIAL_STEP, *bindings_)[0];
						const Object* o2 = other_static_fact->getTerms()[i]->getDomain(Step::INITIAL_STEP, *bindings_)[0];
						if (o1 == object && o2 == other_object)
						{
							continue;
						}
						
						if (o1 != o2)
						{
							terms_match = false;
							break;
						}
					}
					
					if (terms_match)
					{
						shares_static_constraint = true;
						break;
					}
				}
				
				if (!shares_static_constraint)
				{
					all_static_constraints_shared = false;
					break;
				}
			}
			
			if (all_static_constraints_shared)
			{
				equivalent_relationships.insert(std::make_pair(object, other_object));
			}
		}
	}
	
	// Break the nodes up along the equivalent object sets.
	std::map<DomainTransitionGraphNode*, const DomainTransitionGraphNode*> new_to_old_node_mapping;
	std::map<const DomainTransitionGraphNode*, std::vector<DomainTransitionGraphNode*>*> old_to_new_node_mapping;
	
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		old_to_new_node_mapping[dtg_node] = new std::vector<DomainTransitionGraphNode*>();
		
		// Check if this node needs to be split up.
		std::set<const std::vector<const Object*>* > all_variable_domains;
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ++ci)
		{
			BoundedAtom* fact = *ci;
			for (unsigned int i = 0; i < fact->getAtom().getArity(); ++i)
			{
				all_variable_domains.insert(&fact->getVariableDomain(i, *bindings_));
			}
		}
		
		// Split the variable domains up based on the equivalence relationships.
		std::map<const std::vector<const Object*>*, std::vector<const std::vector<const Object*>*>* > split_up_variable_domains;
		std::map<const std::vector<const Object*>*, unsigned int> counters;
		for (std::set<const std::vector<const Object*>* >::const_iterator ci = all_variable_domains.begin(); ci != all_variable_domains.end(); ++ci)
		{
			const std::vector<const Object*>* variable_domain = *ci;
			if (split_up_variable_domains.find(variable_domain) != split_up_variable_domains.end())
			{
				continue;
			}
			
			counters[variable_domain] = 0;
			std::vector<const std::vector<const Object*>* >* split_up_variable_domain = new std::vector<const std::vector<const Object*>* >();
			split_up_variable_domains[variable_domain] = split_up_variable_domain;
			std::set<const Object*> processed_objects;
			
			for (std::vector<const Object*>::const_iterator ci = variable_domain->begin(); ci != variable_domain->end(); ++ci)
			{
				const Object* object = *ci;
				if (processed_objects.find(object) != processed_objects.end())
				{
					continue;
				}
				
				std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator> equivalent_objects = equivalent_relationships.equal_range(object);
				
				std::vector<const Object*>* new_variable_domain = new std::vector<const Object*>();
				new_variable_domain->push_back(object);

				split_up_variable_domain->push_back(new_variable_domain);
				
				processed_objects.insert(object);
				for (std::multimap<const Object*, const Object*>::const_iterator ci = equivalent_objects.first; ci != equivalent_objects.second; ++ci)
				{
					processed_objects.insert((*ci).second);
					new_variable_domain->push_back((*ci).second);
				}
			}
		}
		
		// For every possible split of the variable domains we crate a new DTG node.
		bool done = false;
		while (!done)
		{
			done = true;
			DomainTransitionGraphNode* dtg_node_copy = new DomainTransitionGraphNode(*dtg_node);
			
			//for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node_copy->getAtoms().begin(); ci != dtg_node_copy->getAtoms().end(); ++ci)
			for (unsigned int i = 0; i < dtg_node_copy->getAtoms().size(); ++i)
			{
				BoundedAtom* org_fact = dtg_node->getAtoms()[i];
				BoundedAtom* copied_fact = dtg_node_copy->getAtoms()[i];
				
				for (unsigned int term_index = 0; term_index < org_fact->getAtom().getArity(); ++term_index)
				{
					const Term* org_term = org_fact->getAtom().getTerms()[term_index];
					const Term* copied_term = copied_fact->getAtom().getTerms()[term_index];
					
					const std::vector<const Object*>& variable_domain = org_term->getDomain(org_fact->getId(), *bindings_);
					const std::vector<const Object*>* to_map_to = (*split_up_variable_domains[&variable_domain])[counters[&variable_domain]];
					copied_term->makeDomainEqualTo(copied_fact->getId(), *to_map_to, *bindings_);
				}
			}
			
			old_to_new_node_mapping[dtg_node]->push_back(dtg_node_copy);
			new_to_old_node_mapping[dtg_node_copy] = dtg_node;
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "Split up dtg node: " << std::endl << *dtg_node_copy << std::endl;
#endif
			
			// Update the counters.
			for (std::map<const std::vector<const Object*>*, unsigned int>::const_iterator ci = counters.begin(); ci != counters.end(); ++ci)
			{
				const std::vector<const Object*>* variable_domain = (*ci).first;
				unsigned int counter = (*ci).second;
				if (counter + 1 == split_up_variable_domains[variable_domain]->size())
				{
					counters[variable_domain] = 0;
				}
				else
				{
					counters[variable_domain] = counter + 1;
					done = false;
					break;
				}
			}
		}
	}
	
	// Remove the old nodes and add the new nodes.
	nodes_.clear();
	for (std::map<DomainTransitionGraphNode*, const DomainTransitionGraphNode*>::const_iterator ci = new_to_old_node_mapping.begin(); ci != new_to_old_node_mapping.end(); ++ci)
	{
		DomainTransitionGraphNode* new_node = (*ci).first;
		nodes_.push_back(new_node);
		const DomainTransitionGraphNode* old_node = (*ci).second;
		
		// Reestablish all the transitions.
		for (std::vector<Transition*>::const_iterator ci = old_node->getTransitions().begin(); ci != old_node->getTransitions().end(); ++ci)
		{
			const Transition* transition = *ci;
			std::vector<DomainTransitionGraphNode*>* new_to_nodes = old_to_new_node_mapping[&transition->getToNode()];
			
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = new_to_nodes->begin(); ci != new_to_nodes->end(); ++ci)
			{
				Transition* new_transition = transition->migrateTransition(*new_node, **ci, initial_facts);
				if (new_transition != NULL)
				{
					if (!new_transition->finalise(initial_facts))
					{
						delete new_transition;
						continue;
					}
					
					new_node->addTransition(*new_transition);
				}
			}
		}
	}
	
	for (std::map<const DomainTransitionGraphNode*, std::vector<DomainTransitionGraphNode*>*>::const_iterator ci = old_to_new_node_mapping.begin(); ci != old_to_new_node_mapping.end(); ++ci)
	{
		delete (*ci).second;
	}
	
	std::map<const DomainTransitionGraphNode*, std::vector<DomainTransitionGraphNode*>* > lifted_to_grounded_dtg_node_mappings;
	std::map<DomainTransitionGraphNode*, const DomainTransitionGraphNode* > grounded_to_lifted_dtg_node_mappings;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		
		// Determine which variables to ground.
		std::vector<const std::vector<const Object*> *> variable_domains_to_ground;
		
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ++ci)
		{
			const BoundedAtom* fact = *ci;
			for (unsigned int i = 0; i < fact->getAtom().getArity(); ++i)
			{
				const std::vector<const Object*>& variable_domain = fact->getVariableDomain(i, *bindings_);
				
				// Check if this variable domain contains any objects which must be grounded.
				for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ++ci)
				{
					if (std::find(objects_not_to_ground.begin(), objects_not_to_ground.end(), *ci) == objects_not_to_ground.end())
					{
						variable_domains_to_ground.push_back(&variable_domain);
						break;
					}
				}
			}
		}
		std::sort(variable_domains_to_ground.begin(), variable_domains_to_ground.end());
		variable_domains_to_ground.erase(std::unique(variable_domains_to_ground.begin(), variable_domains_to_ground.end()), variable_domains_to_ground.end());
		
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
		std::cout << "Ground the following variable domains: " << std::endl;
		for (std::vector<const std::vector<const Object*> *>::const_iterator ci = variable_domains_to_ground.begin(); ci != variable_domains_to_ground.end(); ++ci)
		{
			std::cout << "- " << *ci << std::endl;
		}
#endif

		std::vector<DomainTransitionGraphNode*>* grounded_nodes = new std::vector<DomainTransitionGraphNode*>();
		
		std::map<const std::vector<const Object*>*, const Object*> bound_objects;
		dtg_node->groundTerms(*grounded_nodes, variable_domains_to_ground, bound_objects);
		
		// Make copies of every grounded node if they contain more than a single lifted domain with the same values.
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = grounded_nodes->begin(); ci != grounded_nodes->end(); ++ci)
		{
			const DomainTransitionGraphNode* dtg_node = *ci;
			
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "Grounded node: " << std::endl << *dtg_node << std::endl;
#endif
			
			for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ++ci)
			{
				
			}
		}
		
		lifted_to_grounded_dtg_node_mappings[dtg_node] = grounded_nodes;
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = grounded_nodes->begin(); ci != grounded_nodes->end(); ++ci)
		{
			grounded_to_lifted_dtg_node_mappings[*ci] = dtg_node;
		}
	}
	
	std::vector<DomainTransitionGraphNode*> old_nodes(nodes_);
	nodes_.clear();
	for (std::map<const DomainTransitionGraphNode*, std::vector<DomainTransitionGraphNode*>* >::const_iterator ci = lifted_to_grounded_dtg_node_mappings.begin(); ci != lifted_to_grounded_dtg_node_mappings.end(); ++ci)
	{
		//grounded_dtg->nodes_.insert(grounded_dtg->nodes_.end(), (*ci).second->begin(), (*ci).second->end());
		nodes_.insert(nodes_.end(), (*ci).second->begin(), (*ci).second->end());
	}
	
	// Reestablish all the transitions.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		DomainTransitionGraphNode* grounded_from_dtg_node = *ci;
		assert (grounded_to_lifted_dtg_node_mappings.find(grounded_from_dtg_node) != grounded_to_lifted_dtg_node_mappings.end());
		const DomainTransitionGraphNode* lifted_parent = grounded_to_lifted_dtg_node_mappings[grounded_from_dtg_node];
		assert (lifted_parent != NULL);
		
		for (std::vector<Transition*>::const_iterator ci = lifted_parent->getTransitions().begin(); ci != lifted_parent->getTransitions().end(); ++ci)
		{
			const Transition* org_transition = *ci;
			
			// Try to migrate the transition to all the grounded to nodes.
			const std::vector<DomainTransitionGraphNode*>* grounded_to_nodes = lifted_to_grounded_dtg_node_mappings[&org_transition->getToNode()];
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = grounded_to_nodes->begin(); ci != grounded_to_nodes->end(); ++ci)
			{
				DomainTransitionGraphNode* grounded_to_dtg_node = *ci;

				// Migrate the original transition to the cloned nodes.
				Transition* transition = org_transition->migrateTransition(*grounded_from_dtg_node, *grounded_to_dtg_node, initial_facts);
				if (transition != NULL)
				{
					if (!transition->finalise(initial_facts))
					{
						delete transition;
						continue;
					}
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
					std::cout << "Grounded transition: " << *transition << std::endl;
#endif
					grounded_from_dtg_node->addTransition(*transition);
				}
			}
		}
	}
	
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = old_nodes.begin(); ci != old_nodes.end(); ++ci)
	{
		delete *ci;
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "Grounded DTG: " << std::endl;
	std::cout << *this << std::endl;
#endif
}

bool DomainTransitionGraph::addNode(DomainTransitionGraphNode& dtg_node, std::vector<DomainTransitionGraphNode*>* added_nodes)
{
	assert (&dtg_node.getDTG() == this);
	
	for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node.getAtoms().begin(); ci != dtg_node.getAtoms().end(); ++ci)
	{
		const BoundedAtom* fact = *ci;
		if (fact->containsEmptyVariableDomain(*bindings_))
		{
			return false;
		}
	}

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
	
	if (property_space_ == NULL)
	{
		property_space_ = &property_space;
	}
	else
	{
		// NOTE: Memory leak.
		property_space_ = PropertySpace::merge(*property_space_, property_space);
	}
	
	/**
	 * Adding a balanced set, we need to update the type of the invariable to the most specific subtype.
	 */
//	bool type_changed = false;
	for (std::vector<PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
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
	for (std::vector<PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
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
		for (std::vector<PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
		{
			const PropertyState* property_state = *ci;
			
			DomainTransitionGraphNode* dtg_node = new DomainTransitionGraphNode(*this);

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
				BoundedAtom& bounded_atom = BoundedAtom::createBoundedAtom(*atom, *property, *bindings_);
				
				// Check if we need to prune the range of objects for the bounded atom.
				if (index != NO_INVARIABLE_INDEX)
				{
					bounded_atom.getAtom().getTerms()[index]->makeDomainEqualTo(bounded_atom.getId(), property_space.getObjects(), *bindings_);
				}
				dtg_node->addAtom(bounded_atom, index);
			}
			
			if (!addNode(*dtg_node))
			{
				delete dtg_node;
			}
		}
	}
	
	establishTransitions();
}

void DomainTransitionGraph::updateObjects(const PropertySpace& property_space)
{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "[DomainTransitionGraph::updateObjects]" << std::endl;
#endif
	objects_.clear();
	objects_.insert(objects_.end(), property_space.getObjects().begin(), property_space.getObjects().end());

/*
	// TODO: Add objects per predicate space. So if there are multiple predicate spaces the range of objects will be determined
	// for each of them independently (because they are optional preconditions...).
	const std::vector<const Atom*>& initial_facts = dtg_manager_->getInitialFacts();
	
	// Check which nodes from the initial state are part of this DTG.
	for (std::vector<DomainTransitionGraphNode*>::const_iterator dtg_node_ci = nodes_.begin(); dtg_node_ci != nodes_.end(); dtg_node_ci++)
	{
		DomainTransitionGraphNode* dtg_node = *dtg_node_ci;
		
		std::vector<const std::vector<const Object*>* > invariable_domains;
		dtg_node->getBalancedVariableDomains(invariable_domains);
		
		for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			
			// Check if this atom contains an invariable domain.
			bool invariable_domains_for_bounded_atom[bounded_atom->getAtom().getArity()];
			for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
			{
				invariable_domains_for_bounded_atom[i] = std::find(invariable_domains.begin(), invariable_domains.end(), &bounded_atom->getVariableDomain(i, *bindings_)) != invariable_domains.end();
			}
			
			for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ci++)
			{
				const Atom* initial_fact = *ci;
				if (bounded_atom->canUnifyWith(Step::INITIAL_STEP, *initial_fact, *bindings_))
				{
					for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
					{
						if (!invariable_domains_for_bounded_atom[i]) continue;
						
						const std::vector<const Object*>& initial_fact_vd = initial_fact->getTerms()[i]->getDomain(Step::INITIAL_STEP, *bindings_);
						objects_.insert(objects_.end(), initial_fact_vd.begin(), initial_fact_vd.end());
					}
				}
			}
		}
	}
*/
	// Remove duplicates.
	std::sort(objects_.begin(), objects_.end());
	objects_.erase(std::unique(objects_.begin(), objects_.end()), objects_.end());
	std::sort(objects_.begin(), objects_.end());
}

/*void DomainTransitionGraph::removeObjects(const std::set<const Object*>& objects)
{
	for (std::vector<const Object*>::reverse_iterator ri = objects_.rbegin(); ri != objects_.rend(); ri++)
	{
		if (objects.count(*ri) != 0)
		{
			objects_.erase(ri.base() - 1);
		}
	}
}*/

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
		std::vector<Transition*>& transitions = (*i)->getTransitionsNonConst();
		for (std::vector<Transition*>::reverse_iterator ri = transitions.rbegin(); ri != transitions.rend(); ri++)
		{
			Transition* transition = *ri;
			if (&transition->getToNode() == &dtg_node)
			{
				transitions.erase(ri.base() - 1);
				delete transition;
			}
		}
	}
	
	if (node_to_remove != nodes_.end())
	{
		delete *node_to_remove;
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
		
		for (std::vector<Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
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

void DomainTransitionGraph::findTransitionsWithEndNode(std::vector< MyPOP::SAS_Plus::Transition* >& found_transitions, const MyPOP::SAS_Plus::DomainTransitionGraphNode& end_node) const
{
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		for (std::vector<Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			if (&(*ci)->getToNode() == &end_node)
			{
				found_transitions.push_back(*ci);
			}
		}
	}
}

void DomainTransitionGraph::split(const std::vector<const Atom*>& initial_facts)
{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cerr << "[DomainTransitionGraph::split] " << std::endl << *this << std::endl;
#endif
	// Cache all the reverse transitions.
	std::map<const DomainTransitionGraphNode*, std::vector<Transition*>* > reverse_transitions;
	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		std::vector<Transition*>* transitions = new std::vector<Transition*>();
		reverse_transitions[dtg_node] = transitions;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
		{
			const DomainTransitionGraphNode* other_dtg_node = *ci;
			for (std::vector<Transition*>::const_iterator ci = other_dtg_node->getTransitions().begin(); ci != other_dtg_node->getTransitions().end(); ++ci)
			{
				Transition* transition = *ci;
				if (&transition->getToNode() == dtg_node)
				{
					transitions->push_back(transition);
				}
			}
		}
	}
	
	// When we split a node and nodes it is connected to need to be copied due to bindings constraints, we need to make 
	// sure that these constraints are not violated by the transitions which are added afterwards. For each node we specify
	// which nodes it cannot be connected with.
	std::multimap<const DomainTransitionGraphNode*, const DomainTransitionGraphNode*> forbidden_pairs;
	
	std::set<const DomainTransitionGraphNode*> split_nodes;
	for (unsigned int i = 0; i < nodes_.size(); ++i)
	{
		DomainTransitionGraphNode* grounded_dtg_node = nodes_[i];
		if (split_nodes.find(grounded_dtg_node) != split_nodes.end())
		{
			continue;
		}
		
		// Check if this node has lifted terms which are not part of the property space it has been created for.
		std::vector<const std::vector<const Object*>*> balanced_variable_domains;
		grounded_dtg_node->getBalancedVariableDomains(balanced_variable_domains);
		
		std::set<const std::vector<const Object*>*> unbalanced_variable_domains;
		
		bool create_copy = false;
		for (std::vector<BoundedAtom*>::const_iterator ci = grounded_dtg_node->getAtoms().begin(); ci != grounded_dtg_node->getAtoms().end(); ++ci)
		{
			const BoundedAtom* grounded_fact = *ci;
			
			for (unsigned int i = 0; i < grounded_fact->getAtom().getArity(); ++i)
			{
				const std::vector<const Object*>& grounded_variable_domain = grounded_fact->getVariableDomain(i, *bindings_);
				if (grounded_variable_domain.size() > 1 && std::find(balanced_variable_domains.begin(), balanced_variable_domains.end(), &grounded_variable_domain) == balanced_variable_domains.end())
				{
					create_copy = true;
					unbalanced_variable_domains.insert(&grounded_variable_domain);
				}
			}
		}
		
		if (create_copy)
		{
			DomainTransitionGraphNode* grounded_dtg_node_copy = new DomainTransitionGraphNode(*grounded_dtg_node);
			split_nodes.insert(grounded_dtg_node_copy);
			split_nodes.insert(grounded_dtg_node);
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cerr << "Split: " << *grounded_dtg_node << std::endl;
			
			for (std::vector<const std::vector<const Object*>*>::const_iterator ci = balanced_variable_domains.begin(); ci != balanced_variable_domains.end(); ++ci)
			{
				std::cerr << "Balanced: " << *ci << std::endl;
			}
			for (std::set<const std::vector<const Object*>*>::const_iterator ci = unbalanced_variable_domains.begin(); ci != unbalanced_variable_domains.end(); ++ci)
			{
				std::cerr << "Unbalanced: " << *ci << std::endl;
			}
#endif

			// Check if any of the nodes it is connected with should be copied.
			std::map<const DomainTransitionGraphNode*, DomainTransitionGraphNode*> org_to_nodes_to_copy_mapping;
			for (std::vector<Transition*>::const_iterator ci = grounded_dtg_node->getTransitions().begin(); ci != grounded_dtg_node->getTransitions().end(); ++ci)
			{
				const Transition* transition = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
				std::cerr << "Transition " << std::distance(grounded_dtg_node->getTransitions().begin(), ci) << "/" << grounded_dtg_node->getTransitions().size() << std::endl;
#endif
				DomainTransitionGraphNode& to_node = transition->getToNode();
				if (org_to_nodes_to_copy_mapping.find(&to_node) != org_to_nodes_to_copy_mapping.end())
				{
					continue;
				}
				
				// Make a copy iff the following properties hold:
				// 1) A variable domain which is not balanced is shared.
				// 2) Another variable domain which is lifted but is not part of the from node.
				bool contains_shared_unbalanced_variable_domain = false;
				bool contains_foreign_variable_domain = false;

				for (std::vector<BoundedAtom*>::const_iterator ci = to_node.getAtoms().begin(); ci != to_node.getAtoms().end(); ++ci)
				{
					const BoundedAtom* to_node_fact = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
					std::cerr << "Process: ";
					to_node_fact->print(std::cerr, *bindings_);
					std::cerr << std::endl;
#endif
					
					for (unsigned int i = 0; i < to_node_fact->getAtom().getArity(); ++i)
					{
						const std::vector<const Object*>& variable_domain = to_node_fact->getVariableDomain(i, *bindings_);
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
						std::cout << "Check variable domain: " << &variable_domain << std::endl;
#endif
						//if (variable_domain.size() > 1 && std::find(balanced_variable_domains.begin(), balanced_variable_domains.end(), &variable_domain) == balanced_variable_domains.end())
						if (variable_domain.size() > 1 && unbalanced_variable_domains.find(&variable_domain) != unbalanced_variable_domains.end())
						{
							contains_shared_unbalanced_variable_domain = true;
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
							std::cout << "\tContains shared unbalanced variable domain!" << std::endl;
#endif
						}
						else if (variable_domain.size() > 1 && unbalanced_variable_domains.find(&variable_domain) == unbalanced_variable_domains.end() && std::find(balanced_variable_domains.begin(), balanced_variable_domains.end(), &variable_domain) == balanced_variable_domains.end())
						{
							contains_foreign_variable_domain = true;
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
							std::cout << "\tContains foreign variable domain!" << std::endl;
#endif
						}
					}
					
					if (contains_foreign_variable_domain && contains_shared_unbalanced_variable_domain)
					{
						break;
					}
				}
				
				if (contains_foreign_variable_domain && contains_shared_unbalanced_variable_domain)
				{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS					
					std::cerr << "Make copy of: " << to_node << std::endl;
#endif
					DomainTransitionGraphNode* copied_to_node = new DomainTransitionGraphNode(to_node);
					org_to_nodes_to_copy_mapping[&to_node] = copied_to_node;
					nodes_.push_back(copied_to_node);
					reverse_transitions[copied_to_node] = new std::vector<Transition*>();
					to_node.setCopy(*copied_to_node);
					
					if (split_nodes.find(&to_node) != split_nodes.end())
					{
						split_nodes.insert(copied_to_node);
					}
					
					// Make sure that the copy does not link to any node the original is linked to and vice versa.
					forbidden_pairs.insert(std::make_pair(copied_to_node, grounded_dtg_node));
					forbidden_pairs.insert(std::make_pair(&to_node, grounded_dtg_node_copy));
					forbidden_pairs.insert(std::make_pair(grounded_dtg_node, copied_to_node));
					forbidden_pairs.insert(std::make_pair(grounded_dtg_node_copy, &to_node));
				}
			}
			
			// Add the copy.
			grounded_dtg_node->setCopy(*grounded_dtg_node_copy);
			nodes_.push_back(grounded_dtg_node_copy);
			reverse_transitions[grounded_dtg_node_copy] = new std::vector<Transition*>();
			
			// For each transition from or to the copied node we need to check if we should create a transition between the copy or the original node.
			for (std::vector<Transition*>::const_iterator ci = grounded_dtg_node->getTransitions().begin(); ci != grounded_dtg_node->getTransitions().end(); ++ci)
			{
				Transition* org_transition = *ci;
				
				std::map<const DomainTransitionGraphNode*, DomainTransitionGraphNode*>::const_iterator ci = org_to_nodes_to_copy_mapping.find(&org_transition->getToNode());
				
				Transition* transition = NULL;
				// Connect to the orignal node.
				if (ci == org_to_nodes_to_copy_mapping.end())
				{
					transition = org_transition->migrateTransition(*grounded_dtg_node_copy, org_transition->getToNode(), initial_facts);
				}
				// Connect to the copied node.
				else
				{
					transition = org_transition->migrateTransition(*grounded_dtg_node_copy, *(*ci).second, initial_facts);
				}
				
				if (transition != NULL)
				{
					if (!transition->finalise(initial_facts))
					{
						delete transition;
						continue;
					}
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
					std::cout << "Grounded transition: " << *transition << std::endl;
#endif
					grounded_dtg_node_copy->addTransition(*transition);
					reverse_transitions[&transition->getToNode()]->push_back(transition);
				}
			}
			
			// Also copy all the transitions to the original node.
			for (std::vector<Transition*>::const_iterator ci = reverse_transitions[grounded_dtg_node]->begin(); ci != reverse_transitions[grounded_dtg_node]->end(); ++ci)
			{
				Transition* org_transition = *ci;
				
				// Connect the transition from the original node to the copied node, but only if it does not contain a term which is unbalanced and 
				// shared with the from node.
				bool transition_contains_shared_unbalanced_fact = false;
				for (std::vector<BoundedAtom*>::const_iterator ci = org_transition->getFromNode().getAtoms().begin(); ci != org_transition->getFromNode().getAtoms().end(); ++ci)
				{
					const BoundedAtom* fact = *ci;
					for (std::vector<const Term*>::const_iterator ci = fact->getAtom().getTerms().begin(); ci != fact->getAtom().getTerms().end(); ++ci)
					{
						const std::vector<const Object*>& variable_domain = (*ci)->getDomain(fact->getId(), *bindings_);
						if (unbalanced_variable_domains.find(&variable_domain) != unbalanced_variable_domains.end())
						{
							transition_contains_shared_unbalanced_fact = true;
							break;
						}
					}
					
					if (transition_contains_shared_unbalanced_fact)
					{
						break;
					}
				}
				
				if (org_transition->getFromNode().getCopy() != NULL)
				{
					Transition* transition = org_transition->migrateTransition(*org_transition->getFromNode().getCopy(), *grounded_dtg_node_copy, initial_facts);
					
					if (transition != NULL)
					{
						if (!transition->finalise(initial_facts))
						{
							delete transition;
							continue;
						}
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
						std::cout << "Grounded transition: " << *transition << std::endl;
#endif
						transition->getFromNode().addTransition(*transition);
						reverse_transitions[grounded_dtg_node_copy]->push_back(transition);
					}
				}
				
				bool transition_is_allowed = true;
				std::pair<std::multimap<const DomainTransitionGraphNode*, const DomainTransitionGraphNode*>::const_iterator, std::multimap<const DomainTransitionGraphNode*, const DomainTransitionGraphNode*>::const_iterator> constraints;
				constraints = forbidden_pairs.equal_range(&org_transition->getFromNode());
				for (std::multimap<const DomainTransitionGraphNode*, const DomainTransitionGraphNode*>::const_iterator ci = constraints.first; ci != constraints.second; ++ci)
				{
					//std::cout << *(*ci).second << std::endl;
					if ((*ci).second == grounded_dtg_node_copy)
					{
						transition_is_allowed = false;
						break;
					}
				}

				if (transition_is_allowed)
				{
					Transition* transition = org_transition->migrateTransition(org_transition->getFromNode(), *grounded_dtg_node_copy, initial_facts);
					if (transition != NULL)
					{
						// NOTE Check if this constraints is necessary.
						bool add_transition = true;
						std::pair<std::multimap<const DomainTransitionGraphNode*, const DomainTransitionGraphNode*>::const_iterator, std::multimap<const DomainTransitionGraphNode*, const DomainTransitionGraphNode*>::const_iterator> constraints;
						constraints = forbidden_pairs.equal_range(&org_transition->getFromNode());
						std::vector<const DomainTransitionGraphNode*> forbidden_links;
						for (std::multimap<const DomainTransitionGraphNode*, const DomainTransitionGraphNode*>::const_iterator ci = constraints.first; ci != constraints.second; ++ci)
						{
							if ((*ci).second == grounded_dtg_node_copy)
							{
								add_transition = false;
								break;
							}
						}
						
						if (!add_transition || !transition->finalise(initial_facts))
						{
							delete transition;
							continue;
						}
						
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
						std::cout << "Grounded transition: " << *transition << std::endl;
#endif
						transition->getFromNode().addTransition(*transition);
						reverse_transitions[grounded_dtg_node_copy]->push_back(transition);
					}
				}
			}
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cerr << "Result so far." << std::endl << *this << std::endl;
#endif

		}
	}
	
	for (std::map<const DomainTransitionGraphNode*, std::vector<Transition*>* >::const_iterator ci = reverse_transitions.begin(); ci != reverse_transitions.end(); ++ci)
	{
		delete (*ci).second;
	}
}

void DomainTransitionGraph::establishTransitions()
{
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "Establish transitions for: (" << bindings_->getNr() << ") " << *this << std::endl;
#endif
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

				Transition* new_transition = Transition::createTransition(*action, *from_node, *to_node);
				if (new_transition != NULL)
				{
					from_node->addTransition(*new_transition);
				}
			}
		}
	}
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
	std::cout << "=== Result: === (" << bindings_->getNr() << ") " << std::endl << *this << std::endl;
#endif
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
		const DomainTransitionGraphNode* dtg_node = *ci;
		os << "------------------------------------" << std::endl;
		os << *dtg_node;
		for (std::vector<Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ++ci)
		{
			const Transition* transition = *ci;
			os << "\t -> " << "(" << transition->getAction().getPredicate() << " ";
			for (std::vector<const Variable*>::const_iterator ci = transition->getAction().getVariables().begin(); ci != transition->getAction().getVariables().end(); ++ci)
			{
				(*ci)->print(os, dtg.getBindings(), transition->getStepId());
				os << "{" << *ci << "}" << "(" << &(*ci)->getDomain(transition->getStepId(), dtg.getBindings()) << "), ";
			}
			os << ")" << transition->getBalancedTerm() << std::endl;
			os << transition->getToNode();
/*
			os << " Preconditions: " << std::endl;
			for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition->getAllPreconditions().begin(); ci != transition->getAllPreconditions().end(); ++ci)
			{
				os << "* ";
				(*ci).first->print(os, dtg.getBindings(), transition->getStepId());
				os << "." << std::endl;
			}
*/
		}
		os << "------------------------------------" << std::endl;
	}
	return os;
}

};

};
