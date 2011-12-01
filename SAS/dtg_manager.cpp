#include <sys/time.h>
#include <set>
#include <queue>
#include <vector>
#include <algorithm>

#include <boost/bind.hpp>
#include <boost/lambda/lambda.hpp>
#include <boost/lambda/bind.hpp>

#include "dtg_manager.h"
#include "dtg_graph.h"
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
#include "recursive_function.h"
#include "dtg_reachability.h"

//#define MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
//#define MYPOP_SAS_PLUS_DTG_MANAGER_DEBUG
//#define MYPOP_SAS_PLUS_DTG_MANAGER_DOT_OUTPUT
///#define MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME

namespace MyPOP {

namespace SAS_Plus {

/***********************
 * Bounded Atom...
 **********************/
BoundedAtom& BoundedAtom::createBoundedAtom(const Atom& atom, Bindings& bindings)
{
	StepID new_step_id = bindings.createVariableDomains(atom);
	return *(new BoundedAtom(new_step_id, atom));
}

BoundedAtom& BoundedAtom::createBoundedAtom(const Atom& atom, const Property& property, Bindings& bindings)
{
	StepID new_step_id = bindings.createVariableDomains(atom);
	std::vector<const Property*> properties;
	properties.push_back(&property);
	return *(new BoundedAtom(new_step_id, atom, properties));
}

BoundedAtom& BoundedAtom::createBoundedAtom(const Atom& atom, const std::vector<const Property*>& properties, Bindings& bindings)
{
	StepID new_step_id = bindings.createVariableDomains(atom);
	return *(new BoundedAtom(new_step_id, atom, properties));
}

	//BoundedAtom(StepID id, const Atom& atom, const Property* property);
BoundedAtom::BoundedAtom(StepID id, const Atom& atom)
	: id_(id), atom_(&atom)
{
	
}

BoundedAtom::BoundedAtom(StepID id, const Atom& atom, const std::vector<const Property*>& properties)
	: id_(id), atom_(&atom)
{
	properties_.insert(properties_.end(), properties.begin(), properties.end());
}

BoundedAtom::~BoundedAtom()
{
	delete atom_;
}

StepID BoundedAtom::getId() const
{
	return id_;
}

const Atom& BoundedAtom::getAtom() const
{
	return *atom_;
}

/*InvariableIndex BoundedAtom::getIndex(StepID id, const Term& term, const Bindings& bindings) const
{
	for (InvariableIndex i = 0; i < atom_->getArity(); i++)
	{
		const Term* bounded_term = atom_->getTerms()[i];
		
		if (bounded_term->isTheSameAs(id_, term, id, bindings))
		{
			return i;
		}
	}
	
	assert (false);
}*/

/*const Property* BoundedAtom::getProperty() const
{
	return property_;
}*/

const std::vector<const Property*>& BoundedAtom::getProperties() const
{
	return properties_;
}

unsigned int BoundedAtom::containsVariableDomain(const std::vector<const Object*>& variable_domain, const Bindings& bindings) const
{
	return atom_->containsVariableDomain(id_, variable_domain, bindings);
}
	
bool BoundedAtom::addProperty(const Property& property)
{
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		const Property* existing_property = *ci;
		if (property == *existing_property)
			return false;
	}
	
	properties_.push_back(&property);
	return true;
}

bool BoundedAtom::isBalanced(unsigned int term_index) const
{
	if (term_index == NO_INVARIABLE_INDEX) return false;
	
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		const Property* existing_property = *ci;
		if (existing_property->getIndex() == term_index) return true;
	}
	return false;
}

bool BoundedAtom::isMutexWith(const BoundedAtom& other, const Bindings& bindings) const
{
	// If either of the bounded atoms have any properties we can conclude that they cannot be mutex.
	if (properties_.size() == 0 || other.properties_.size() == 0)
	{
		return false;
	}
	
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		const Property* property = *ci;
		InvariableIndex invariable_index = property->getIndex();
		
		const Term* invariable_term = invariable_index != NO_INVARIABLE_INDEX ? atom_->getTerms()[invariable_index] : NULL;
		
		for (std::vector<const Property*>::const_iterator ci = other.properties_.begin(); ci != other.properties_.end(); ci++)
		{
			const Property* other_property = *ci;
			InvariableIndex other_property_index = other_property->getIndex();
			
			const Term* other_invariable_term = other_property_index != NO_INVARIABLE_INDEX ? other.atom_->getTerms()[other_property_index] : NULL;
			
			// If the properties are mutex, make sure the invariables match as well - if there are any.
			if (property->isMutexWith(other_property))
			{
				if (invariable_term == NULL || other_invariable_term == NULL)
				{
					return true;
				}
				
				//if (invariable_term->canUnify(id_, *other_invariable_term, other.id_, bindings))
				if (invariable_term->isTheSameAs(id_, *other_invariable_term, other.id_, bindings))
				{
					return true;
				}
			}
		}
	}
	
	return false;
}

bool BoundedAtom::isMutexWith(const Atom& atom, StepID step_id, const Bindings& bindings, InvariableIndex invariable_index) const
{
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		const Property* property = *ci;
		
		// Make sure the invariables are in agreement.
		if (!atom.getTerms()[invariable_index]->canUnify(step_id, *atom_->getTerms()[property->getIndex()], id_, bindings))
		{
	//		std::cout << "The invariables are not the same, so they cannot be mutex by default!" << std::endl;
			continue;
		}
		
		// If the predicate is present in this bounded atom's property state it isn't mutex.
		const std::vector<const Property*>& lhs_properties = property->getPropertyState().getProperties();
		for (std::vector<const Property*>::const_iterator ci = lhs_properties.begin(); ci != lhs_properties.end(); ci++)
		{
			const Property* property = *ci;
	//		std::cout << "[BoundedAtom::isMutexWith] LHS property: " << property->getPredicate().getName() << "[" << property->getIndex() << "]" << std::endl;
			if (property->getPredicate().getName() == atom.getPredicate().getName() && property->getIndex() == invariable_index)
			{
				return false;
			}
		}

		bool potentially_mutex = false;
		for (std::vector<const PropertyState*>::const_iterator ci = property->getPropertyState().getPropertySpace().getPropertyStates().begin(); ci !=  property->getPropertyState().getPropertySpace().getPropertyStates().end(); ci++)
		{
			const PropertyState* property_state = *ci;
			const std::vector<const Property*>& properties = property_state->getProperties();
			
			// If the property states are the same they are not mutex (already tested above).
			if (property_state == &property->getPropertyState())
			{
				continue;
			}
			
	//		bool bounded_atom_present = false;
			
			// If the property of another property states matches with the given one we conclude it must be mutex.
			for (std::vector<const Property*>::const_iterator ci = properties.begin(); ci != properties.end(); ci++)
			{
				const Property* property = *ci;
	//			std::cout << "[BoundedAtom::isMutexWith] Check against: " << property->getPredicate().getName() << "[" << property->getIndex() << "]" << std::endl;
				if (property->getPredicate().getName() == atom.getPredicate().getName() && property->getIndex() == invariable_index)
				{
					potentially_mutex = true;
				}
				if (property->getPredicate().getName() == property->getPredicate().getName() && property->getIndex() == property->getIndex())
				{
	//				bounded_atom_present = true;
					potentially_mutex = false;
					break;
				}
			}
		}
		
		if (potentially_mutex)
		{
			return true;
		}
	}
	return false;
}

const std::vector<const Object*>& BoundedAtom::getVariableDomain(unsigned int term_index, const Bindings& bindings) const
{
	assert (term_index < atom_->getArity());
	return atom_->getTerms()[term_index]->getDomain(id_, bindings);
}

bool BoundedAtom::isEquivalentTo(const BoundedAtom& other, const Bindings& lhs_bindings, const Bindings* rhs_bindings) const
{
	if (rhs_bindings == NULL)
	{
		rhs_bindings = &lhs_bindings;
	}
	
	if (atom_->getPredicate().getName() != other.getAtom().getPredicate().getName())
		return false;
	
	if (atom_->getArity() != other.getAtom().getArity())
		return false;
	
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		if (!atom_->getTerms()[i]->isEquivalentTo(id_, *other.getAtom().getTerms()[i], other.getId(), lhs_bindings, rhs_bindings))
			return false;
	}
	return true;
}

bool BoundedAtom::isIdenticalTo(const BoundedAtom& other, const Bindings& lhs_bindings) const
{
	if (atom_->getPredicate().getName() != other.getAtom().getPredicate().getName())
		return false;
	
	if (atom_->getArity() != other.getAtom().getArity())
		return false;
	
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		if (!atom_->getTerms()[i]->isTheSameAs(id_, *other.getAtom().getTerms()[i], other.getId(), lhs_bindings))
			return false;
	}
	return true;
}

bool BoundedAtom::isProperSubSetOf(const BoundedAtom& other, const Bindings& bindings) const
{
	if (atom_->getPredicate().getName() != other.getAtom().getPredicate().getName())
		return false;
	
	if (atom_->getArity() != other.getAtom().getArity())
		return false;
	
	bool found_sub_set = false;
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		bool is_proper_sub_set = atom_->getTerms()[i]->isProperSubSetOf(id_, *other.getAtom().getTerms()[i], other.getId(), bindings);
		bool is_equivalent_to = atom_->getTerms()[i]->isEquivalentTo(id_, *other.getAtom().getTerms()[i], other.getId(), bindings);
		
		if (is_proper_sub_set)
			found_sub_set = true;
		
		if (!is_proper_sub_set && !is_equivalent_to)
			return false;
	}
	return found_sub_set;
}

bool BoundedAtom::isProperSuperSetOf(const BoundedAtom& other, const Bindings& bindings) const
{
	if (atom_->getPredicate().getName() != other.getAtom().getPredicate().getName())
		return false;
	
	if (atom_->getArity() != other.getAtom().getArity())
		return false;
	
	bool found_super_set = false;
	for (unsigned int i = 0; i < atom_->getArity(); i++)
	{
		bool is_proper_super_set = atom_->getTerms()[i]->isProperSuperSetOf(id_, *other.getAtom().getTerms()[i], other.getId(), bindings);
		bool is_equivalent_to = atom_->getTerms()[i]->isEquivalentTo(id_, *other.getAtom().getTerms()[i], other.getId(), bindings);
		
		if (is_proper_super_set)
			found_super_set = true;
		
		if (!is_proper_super_set && !is_equivalent_to)
			return false;
	}
	return found_super_set;
}

bool BoundedAtom::canUnifyWith(const BoundedAtom& other, const Bindings& bindings) const
{
	return bindings.canUnify(getAtom(), getId(), other.getAtom(), other.getId());
}

bool BoundedAtom::shareSameProperties(const BoundedAtom& other) const
{
	if (properties_.size() != other.properties_.size()) return false;
	
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		const Property* property = *ci;
		bool found = false;
		for (std::vector<const Property*>::const_iterator ci = other.properties_.begin(); ci != other.properties_.end(); ci++)
		{
			if (*property == **ci)
			{
				found = true;
				break;
			}
		}
		
		if (!found) return false;
	}
	return true;
}

void BoundedAtom::print(std::ostream& os, const Bindings& bindings, bool verbal) const
{
	atom_->print(os, bindings, id_, verbal);
	os << " $$$ ";
	for (std::vector<const Property*>::const_iterator ci = properties_.begin(); ci != properties_.end(); ci++)
	{
		os << **ci;
		if (ci  + 1 != properties_.end())
			os << ", ";
	}
	os << " $$$ ";
}
	
/****************************************
 * void DomainTransitionGraphManager...
 ****************************************/
	
DomainTransitionGraphManager::DomainTransitionGraphManager(const PredicateManager& predicate_manager, const TypeManager& type_manager, const ActionManager& action_manager, const TermManager& term_manager, const std::vector<const Atom*>& initial_facts)
	: predicate_manager_(&predicate_manager), type_manager_(&type_manager), action_manager_(&action_manager), term_manager_(&term_manager), initial_facts_(&initial_facts)
{
	
}

DomainTransitionGraphManager::~DomainTransitionGraphManager()
{
//	for (std::map<const Predicate*, std::vector<DomainTransitionGraph*>* >::iterator i = dtg_mappings_.begin(); i != dtg_mappings_.end(); i++)
//	{
//		delete (*i).second;
//	}
}

void DomainTransitionGraphManager::getProperties(std::vector<std::pair<const Predicate*, unsigned int> >& predicates, const TIM::PropertyState& property_state) const
{
	for (std::multiset<TIM::Property*>::const_iterator lhs_properties_i = property_state.begin(); lhs_properties_i != property_state.end(); lhs_properties_i++)
	{
		const TIM::Property* property = *lhs_properties_i;

		const VAL::extended_pred_symbol* extended_property = property->root();
		const Predicate* predicate = predicate_manager_->getGeneralPredicate(extended_property->getName());
		assert (predicate != NULL);

		// Adding the predicate to the DTG will also create a lifted DTG node with that predicate.
		// Further refinements can be made to this DTG by splitting these nodes.
		predicates.push_back(std::make_pair(predicate, property->aPosn()));
	}
}

const DomainTransitionGraph& DomainTransitionGraphManager::generateDomainTransitionGraphsTIM(const VAL::pddl_type_list& types, Bindings& bindings)
{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval start_time_tim_translation;
	gettimeofday(&start_time_tim_translation, NULL);
#endif
	// Store temporary DTGs in this vector, during post processing they might get split again. Only then will we add the DTGs as a managable object (see Manager class).
	std::vector<DomainTransitionGraph*> tmp_dtgs;
	
	std::vector<TIM::PropertySpace*> property_spaces;
	property_spaces.insert(property_spaces.end(), TIM::TA->pbegin(), TIM::TA->pend());
//	property_spaces.insert(property_spaces.end(), TIM::TA->abegin(), TIM::TA->aend());
//	property_spaces.insert(property_spaces.end(), TIM::TA->sbegin(), TIM::TA->send());

	assert (property_spaces.size() > 0);
	
	std::set<const Predicate*> state_valued_predicates;

	// Construct the DTGs by combining all properties which appear together in either the LHS or RHS of a transition rule.
	for (std::vector<TIM::PropertySpace*>::const_iterator property_space_i = property_spaces.begin(); property_space_i != property_spaces.end(); ++property_space_i)
	{
		TIM::PropertySpace* property_space = *property_space_i;
		
		PropertySpace* dtg_property_space = new PropertySpace();
		
		std::set<std::vector<std::pair<const Predicate*, unsigned int> > > processed_expressions;
		
		// The DTG where all predicates will be added to.
		DomainTransitionGraph* dtg = new DomainTransitionGraph(*this, *type_manager_, *action_manager_, *predicate_manager_, bindings, *initial_facts_);

		// We need to augment some rules to get the full set of properties. If a property appears in the LHS of a rule $a$ and it is a proper subset
		// of another LHS $b$. Then add a new rule $b$ -> ($b.LHS$ \ $a.LHS$) + $a.RHS$.
		for (std::set<TIM::TransitionRule*>::const_iterator rules_i = property_space->getRules().begin(); rules_i != property_space->getRules().end(); ++rules_i)
		{
			TIM::TransitionRule* rule_a = *rules_i;
			
			// Combine the property states who appear in either the LHS of RHS of this rule.
			std::vector<std::pair<const Predicate*, unsigned int> > predicates_rule_a;
			getProperties(predicates_rule_a, *rule_a->getLHS());

			for (std::set<TIM::TransitionRule*>::const_iterator rules_i = property_space->getRules().begin(); rules_i != property_space->getRules().end(); ++rules_i)
			{
				TIM::TransitionRule* rule_b = *rules_i;
				
				// If rule_a is equal in size or larger it cannot be a proper subset.
				if (rule_a->getLHS()->size() >= rule_b->getLHS()->size())
				{
					continue;
				}
				
				std::multiset<TIM::Property*> intersection;
				std::set_intersection(rule_a->getLHS()->begin(), rule_a->getLHS()->end(), rule_b->getLHS()->begin(), rule_b->getLHS()->end(), std::inserter(intersection, intersection.begin()));
				
				// If the intersection is equal to the LHS of rule_a we know that it is a propper subset.
				if (intersection.size() == rule_a->getLHS()->size())
				{
					std::multiset<TIM::Property*> difference;
					std::set_difference(rule_b->getLHS()->begin(), rule_b->getLHS()->end(), rule_a->getLHS()->begin(), rule_a->getLHS()->end(), std::inserter(difference, difference.begin()));
					
					std::vector<std::pair<const Predicate*, unsigned int> > predicates_rhs;
					getProperties(predicates_rhs, *rule_a->getRHS());
					
//					std::cout << "!Rule: ";
//					rule_a->getLHS()->write(std::cout);
//					std::cout << " -> ";
//					rule_a->getRHS()->write(std::cout);
//					std::cout << " is a proper subset of: ";
//					rule_b->getLHS()->write(std::cout);
//					std::cout << " -> ";
//					rule_b->getRHS()->write(std::cout);
//					std::cout << std::endl;
					
//					std::cout << "Generate new rule: " << std::endl;
//					rule_b->getLHS()->write(std::cout);
//					std::cout << " =--> ";
//					rule_a->getRHS()->write(std::cout);
//					std::cout << " ++ ";
					
					std::multiset<TIM::Property*> duplicates;
					std::set_intersection(rule_a->getRHS()->begin(), rule_a->getRHS()->end(), rule_b->getLHS()->begin(), rule_b->getLHS()->end(), std::inserter(duplicates, duplicates.begin()));
					
					for (std::multiset<TIM::Property*>::const_iterator ci = difference.begin(); ci != difference.end(); ci++)
					{
						TIM::Property* property = *ci;
						const VAL::extended_pred_symbol* extended_property = property->root();
						const Predicate* predicate = predicate_manager_->getGeneralPredicate(extended_property->getName());
						assert (predicate != NULL);
						
						// Make sure we do not add duplicates:
						if (duplicates.count(property) != 0)
						{
							continue;
						}

						predicates_rhs.push_back(std::make_pair(predicate, property->aPosn()));
						
//						property->write(std::cout);
//						std::cout << " ++ ";
					}
//					std::cout << std::endl;
					
					if (processed_expressions.count(predicates_rhs) == 0)
					{
						///property_states.push_back(new PropertyState(*dtg_property_space, predicates_rhs));
						PropertyState* new_property_state = new PropertyState(*dtg_property_space, predicates_rhs);
						dtg_property_space->addPropertyState(*new_property_state);
						processed_expressions.insert(predicates_rhs);
						
						// We no longer need to process the LHS and RHS of rule_a, since it has been substituted by this rule.
						std::vector<std::pair<const Predicate*, unsigned int> > rule_a_rhs;
						getProperties(rule_a_rhs, *rule_a->getRHS());
						processed_expressions.insert(predicates_rule_a);
						processed_expressions.insert(rule_a_rhs);
					}
				}
			}
		}

		// After having augmented the rules for which the LHS formed a proper subset we finish constructing the DTGs for those rules
		// which do not have this property. The reason why this step has to be done last is because of the way we construct DTGs, if
		// we do the augmented rules before this, we might add a DTG node for a rule which is a strict subset. Then, when adding the
		// augmented rule, the DTG manager will reject adding the new node because it already exists.
		// TODO: Probably need to change this...
		for (std::set<TIM::TransitionRule*>::const_iterator rules_i = property_space->getRules().begin(); rules_i != property_space->getRules().end(); ++rules_i)
		{
			TIM::TransitionRule* rule = *rules_i;

			// Combine the property states who appear in either the LHS of RHS of this rule.
			std::vector<std::pair<const Predicate*, InvariableIndex> > predicates;
			getProperties(predicates, *rule->getLHS());
			
			if (processed_expressions.count(predicates) == 0)
			{
				PropertyState* new_property_state = new PropertyState(*dtg_property_space, predicates);
				dtg_property_space->addPropertyState(*new_property_state);
				processed_expressions.insert(predicates);
			}
			
			predicates.clear();
			getProperties(predicates, *rule->getRHS());
			
			if (processed_expressions.count(predicates) == 0)
			{
				PropertyState* new_property_state = new PropertyState(*dtg_property_space, predicates);
				dtg_property_space->addPropertyState(*new_property_state);
				processed_expressions.insert(predicates);
			}
		}
		
		dtg->addBalancedSet(*dtg_property_space, true);
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << " === DTG after adding all predicates (" << dtg->getBindings().getNr() << ") === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;
#endif
		dtg->establishTransitions();
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << " === DTG after adding all transitions (" << dtg->getBindings().getNr() << ") === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;
#endif
		dtg->addObjects();
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << " === DTG after adding all objects (" << dtg->getBindings().getNr() << ") === " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " === END DTG === " << std::endl;
#endif

		// Record all the state values predicates here so we know which ones are not yet processed later.
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			const DomainTransitionGraphNode* dtg_node = *ci;
			
			for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
			{
				state_valued_predicates.insert(&(*ci)->getAtom().getPredicate());
			}
		}

		addManagableObject(dtg);
	}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval end_time_tim_translation;
	gettimeofday(&end_time_tim_translation, NULL);
	
	double time_spend = end_time_tim_translation.tv_sec - start_time_tim_translation.tv_sec + (end_time_tim_translation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "TIM transation took: " << time_spend << " seconds" << std::endl;

	struct timeval start_time_apply_rules;
	gettimeofday(&start_time_apply_rules, NULL);
#endif
	createPointToPointTransitions();
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval end_time_apply_rules;
	gettimeofday(&end_time_apply_rules, NULL);
	
	time_spend = end_time_apply_rules.tv_sec - start_time_apply_rules.tv_sec + (end_time_apply_rules.tv_usec - start_time_apply_rules.tv_usec) / 1000000.0;
	std::cerr << "Creating point to point transitions took: " << time_spend << " seconds" << std::endl;

	struct timeval start_time_unsupported_predicates;
	gettimeofday(&start_time_unsupported_predicates, NULL);
#endif
	/**
	 * Some predicates are not seen as DTGs by TIM, these come in two categories:
	 * - Static predicates - which cannot change, ever.
	 * - Predicates which can only be made true or false.
	 * 
	 * This bit of code constructs the DTGs for those predicates.
	 * 
	 * Note that we need to do this step before we check which DTG nodes need to be split due to the
	 * grounding of the static preconditions done above. The reason being is that when we see the need
	 * for a node to change its variables, we check for all possible values which are valid among the
	 * DTG nodes. If we have not included the static and those who can only be made true or false we
	 * might reach a false conclusion that a fact or transition's precondition cannot be satisfied and
	 * end up with wrong DTGs.
	 */
	std::vector<std::pair<const Predicate*, const Atom*> > unsupported_predicates;
	for (std::vector<Predicate*>::const_iterator ci = predicate_manager_->getManagableObjects().begin(); ci != predicate_manager_->getManagableObjects().end(); ci++)
	{
		const Predicate* predicate = *ci;

		bool is_supported = false;
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << "Check if the predicate : " << *predicate << " is supported!" << std::endl;
#endif

		for (std::set<const Predicate*>::const_iterator ci = state_valued_predicates.begin(); ci != state_valued_predicates.end(); ci++)
		{
			const Predicate* state_valued_predicate = *ci;
			if (state_valued_predicate == predicate ||
			    state_valued_predicate->canSubstitute(*predicate))
			{
				is_supported = true;
				break;
			}
		}
		
		if (is_supported) continue;

		// Check if any of the DTG nodes supports the given predicate by making a dummy atom of it.
		std::vector<const Term*>* new_terms = new std::vector<const Term*>();
		for (std::vector<const Type*>::const_iterator ci = predicate->getTypes().begin(); ci != predicate->getTypes().end(); ci++)
		{
			const Type* type = *ci;
			new_terms->push_back(new Variable(*type, "test"));
		}
		Atom* possitive_atom = new Atom(*predicate, *new_terms, false);

		assert (objects_.size() > 0);
		unsupported_predicates.push_back(std::make_pair(predicate, possitive_atom));
	}
	
	for (std::vector<std::pair<const Predicate*, const Atom*> >::const_iterator ci = unsupported_predicates.begin(); ci != unsupported_predicates.end(); ci++)
	{
		const Predicate* predicate = (*ci).first;
		const Atom* possitive_atom = (*ci).second;
		/**
		 * Unsupported predicates come in two varieties:
		 * 1) The predicate is static, so only a single node needs to be constructed with these values.
		 * 2) The predicate is not static, but can only be made true or false. This is encoded using two
		 * nodes and all relevant transitions between the two. The other node must contain the atom negated.
		 */
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << "The predicate: " << *predicate << " is not processed yet!" << std::endl;
#endif
		
		// 1) The predicate is static.
		DomainTransitionGraph* new_unprocessed_dtg = new DomainTransitionGraph(*this, *type_manager_, *action_manager_, *predicate_manager_, bindings, *initial_facts_);
		std::vector<std::pair<const Predicate*, unsigned int> >* predicates_to_add = new std::vector<std::pair<const Predicate*, unsigned int> >();
		predicates_to_add->push_back(std::make_pair(predicate, NO_INVARIABLE_INDEX));
		
		DomainTransitionGraphNode* possitive_new_unprocessed_dtg = new DomainTransitionGraphNode(*new_unprocessed_dtg, NO_INVARIABLE_INDEX);
		
		StepID possitive_atom_id = new_unprocessed_dtg->getBindings().createVariableDomains(*possitive_atom);
		
		/// TEST
		PropertySpace* property_space = new PropertySpace();
		PropertyState* property_state = new PropertyState(*property_space, *predicates_to_add);
		BoundedAtom* fact = new BoundedAtom(possitive_atom_id, *possitive_atom, property_state->getProperties());
		possitive_new_unprocessed_dtg->addAtom(*fact, NO_INVARIABLE_INDEX);
		
		new_unprocessed_dtg->addNode(*possitive_new_unprocessed_dtg);

		addManagableObject(new_unprocessed_dtg);
		
		// 2) The predicate is not static.
		if (!predicate->isStatic())
		{
			// Add all preconditions which share a term with the unsupported predicate.
			DomainTransitionGraphNode* negative_new_unprocessed_dtg = new DomainTransitionGraphNode(*new_unprocessed_dtg, NO_INVARIABLE_INDEX);
			Atom* negative_atom = new Atom(*predicate, possitive_atom->getTerms(), true);
			StepID negative_atom_id = new_unprocessed_dtg->getBindings().createVariableDomains(*possitive_atom);
			BoundedAtom* bounded_negative_atom = new BoundedAtom(negative_atom_id, *negative_atom, property_state->getProperties());
			
			std::vector<const BoundedAtom*> atoms_add_to_from_node;
			atoms_add_to_from_node.push_back(bounded_negative_atom);
			
			new_unprocessed_dtg->addNode(*negative_new_unprocessed_dtg);
			
			for (std::vector<const Term*>::const_iterator ci = negative_atom->getTerms().begin(); ci != negative_atom->getTerms().end(); ci++)
			{
				const Term* from_node_term = *ci;
				const Term* to_node_term = possitive_atom->getTerms()[std::distance(negative_atom->getTerms().begin(), ci)];
				
				from_node_term->unify(negative_atom_id, *to_node_term, possitive_atom_id, new_unprocessed_dtg->getBindings());
			}
			
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Simple DTG : " << *new_unprocessed_dtg << std::endl;
#endif
			
			// Find all transitions which can make this predicate true and false and add them as transitions.
			std::vector<std::pair<const Action*, const Atom*> > achievers;
			action_manager_->getAchievingActions(achievers, *possitive_atom);
			
			for (std::vector<std::pair<const Action*, const Atom*> >::const_iterator ci = achievers.begin(); ci != achievers.end(); ci++)
			{
				const Action* achieving_action = (*ci).first;
				StepID new_action_step_id = bindings.createVariableDomains(*achieving_action);
				StepPtr new_step(new Step(new_action_step_id, *achieving_action));
				
				// Create a transition between the two nodes.
				Transition* transition = Transition::createSimpleTransition(new_step, *negative_new_unprocessed_dtg, *possitive_new_unprocessed_dtg);
				
				assert (transition != NULL);
				
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "Process the transition: " << *transition << std::endl;
#endif
				// Inspect the transition and add all preconditions which shares a term with the positive achieved fact.
				bool precondition_added = true;
				std::set<const Atom*> closed_list;
				while (precondition_added)
				{
					precondition_added = false;
					const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ci++)
					{
						const Atom* precondition = (*ci).first;
						if (closed_list.count(precondition) != 0)
						{
							continue;
						}
						
						bool precondition_added = false;
						for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ci++)
						{
							const Term* precondition_term = *ci;
							
							for (std::vector<const BoundedAtom*>::const_iterator ci = atoms_add_to_from_node.begin(); ci != atoms_add_to_from_node.end(); ci++)
							{
								const BoundedAtom* from_node_atom = *ci;
								
								for (std::vector<const Term*>::const_iterator ci = from_node_atom->getAtom().getTerms().begin(); ci != from_node_atom->getAtom().getTerms().end(); ci++)
								{
									const Term* from_node_atom_term = *ci;

									if (precondition_term->isTheSameAs(transition->getStepId(), *from_node_atom_term, from_node_atom->getId(), new_unprocessed_dtg->getBindings()))
									{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
										std::cout << "Add the precondition: ";
										precondition->print(std::cout, new_unprocessed_dtg->getBindings(), transition->getStepId());
										std::cout << std::endl;
#endif
										closed_list.insert(precondition);
										precondition_added = true;
										
										// Get the properties attached to this DTG node.
										std::vector<const Property*>* properties = new std::vector<const Property*>();
										Property::getProperties(*properties, *precondition);
										
										if (properties->size() == 0)
										{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
											std::cout << "Could not find properties for the precondition: ";
											precondition->print(std::cout, bindings, transition->getStepId());
											std::cout << "." << std::endl;
#endif
											PropertySpace* p_space = new PropertySpace();
											
											std::vector<std::pair<const Predicate*, InvariableIndex> >* predicates = new std::vector<std::pair<const Predicate*, InvariableIndex> >();
											predicates->push_back(std::make_pair(&precondition->getPredicate(), NO_INVARIABLE_INDEX));
											PropertyState* p_state = new PropertyState(*p_space, *predicates);
											properties->insert(properties->end(), p_state->getProperties().begin(), p_state->getProperties().end());
											assert (!properties->empty());
										}
										BoundedAtom* atom_to_add = new BoundedAtom(transition->getStepId(), *precondition, *properties);
										if (negative_new_unprocessed_dtg->addAtom(*atom_to_add, NO_INVARIABLE_INDEX))
										{
											atoms_add_to_from_node.push_back(atom_to_add);
											transition->addedFromNodePrecondition(*precondition);
										}
										
										// Check if this precondition is actually removed, if not add it to the to node!
										bool is_removed = false;
										for (std::vector<const Atom*>::const_iterator ci = transition->getAction().getEffects().begin(); ci != transition->getAction().getEffects().end(); ci++)
										{
											const Atom* effect = *ci;
											
											if (effect->isNegative() != precondition->isNegative() &&
											    bindings.areIdentical(*effect, transition->getStepId(), *precondition, transition->getStepId()))
											{
												is_removed = true;
												break;
											}
										}
										
										if (!is_removed)
										{
											if (possitive_new_unprocessed_dtg->addAtom(*atom_to_add, NO_INVARIABLE_INDEX))
											{
												transition->addedToNodeFact(*precondition);
											}
										}
										
										break;
									}
								}
								
								if (precondition_added)
								{
									break;
								}
							}
							
							if (precondition_added)
							{
								break;
							}
						}
					}
				}
				negative_new_unprocessed_dtg->addTransition(*transition);
			}
			
			
			// Do some grounding...
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Created the LTG for the attribute space: " << *new_unprocessed_dtg << std::endl;
#endif
			std::vector<const DomainTransitionGraphNode*> dtg_nodes_to_remove;
			std::vector<DomainTransitionGraphNode*> dtg_nodes_to_add;

			// Determine which varaible domains should be grounded.
			std::vector<const std::vector<const Object*>* > variable_domains_to_ground;
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = new_unprocessed_dtg->getNodes().begin(); ci != new_unprocessed_dtg->getNodes().end(); ci++)
			{
				const DomainTransitionGraphNode* dtg_node = *ci;
				
				for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
				{
					BoundedAtom* bounded_atom = *ci;
					
					for (unsigned int i = 0; i < bounded_atom->getAtom().getArity(); i++)
					{
						const std::vector<const Object*>& variable_domain = bounded_atom->getVariableDomain(i, bindings);
						
						for (std::vector<const Object*>::const_iterator ci = variable_domain.begin(); ci != variable_domain.end(); ci++)
						{
							if (isObjectGrounded(**ci))
							{
								if (std::find(variable_domains_to_ground.begin(), variable_domains_to_ground.end(), &variable_domain) == variable_domains_to_ground.end())
								{
									variable_domains_to_ground.push_back(&variable_domain);
								}
								break;
							}
						}
					}
				}
			}

			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = new_unprocessed_dtg->getNodes().begin(); ci != new_unprocessed_dtg->getNodes().end(); ci++)
			{
				DomainTransitionGraphNode* dtg_node = *ci;
				
				for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
				{
					const Transition* org_transition = *ci;
					
					assert (org_transition != NULL);
					
					DomainTransitionGraphNode* from_dtg_node_clone = new DomainTransitionGraphNode(*dtg_node);
					DomainTransitionGraphNode* to_dtg_node_clone = new DomainTransitionGraphNode(org_transition->getToNode());
				
					assert (&from_dtg_node_clone->getDTG() == &dtg_node->getDTG());
					assert (&to_dtg_node_clone->getDTG() == &dtg_node->getDTG());
					
					// Migrate the original transition to the cloned nodes.
					Transition* transition = org_transition->migrateTransition(*from_dtg_node_clone, *to_dtg_node_clone);
					
					assert (transition != NULL);
					
					// Ground all the terms which need to be grounded and add the result to the final DTG.
					std::vector<std::pair<DomainTransitionGraphNode*, std::map<const std::vector<const Object*>*, const Object*>* > > from_grounded_nodes;
					bool grounded_from_nodes = from_dtg_node_clone->groundTerms(from_grounded_nodes, variable_domains_to_ground);
					
					if (grounded_from_nodes)
					{
						dtg_node->removeTransitions();
						dtg_nodes_to_remove.push_back(dtg_node);
					}
					
					std::vector<std::pair<DomainTransitionGraphNode*, std::map<const std::vector<const Object*>*, const Object*>* > > to_grounded_nodes;
					bool grounded_to_nodes = to_dtg_node_clone->groundTerms(to_grounded_nodes, variable_domains_to_ground);
					if (grounded_to_nodes)
					{
						to_dtg_node_clone->removeTransitions();
						dtg_nodes_to_remove.push_back(&transition->getToNode());
					}

					if (grounded_from_nodes || grounded_to_nodes)
					{
						for (std::vector<std::pair<DomainTransitionGraphNode*, std::map<const std::vector<const Object*>*, const Object*>* > >::const_iterator ci = from_grounded_nodes.begin(); ci != from_grounded_nodes.end(); ci++)
						{
							
							DomainTransitionGraphNode* from_dtg_node = NULL;
							
							if (grounded_from_nodes)
							{
								from_dtg_node = (*ci).first;
							}
							else
							{
								from_dtg_node = new DomainTransitionGraphNode(*(*ci).first);
							}
							
							// Ground the to node too, but with respect to the variables already grounded!
							std::vector<DomainTransitionGraphNode*> selective_to_grounded_nodes;
							bool grounded_to_nodes = to_dtg_node_clone->groundTerms(selective_to_grounded_nodes, variable_domains_to_ground, *(*ci).second);
							if (grounded_to_nodes)
							{
								to_dtg_node_clone->removeTransitions();
								dtg_nodes_to_remove.push_back(&transition->getToNode());
							}
							
							//std::cerr << to_grounded_nodes.size() << " v.s. " << selective_to_grounded_nodes.size() << std::endl;
							
							
							//for (std::vector<std::pair<DomainTransitionGraphNode*, std::map<const std::vector<const Object*>*, const Object*>* > >::const_iterator ci = to_grounded_nodes.begin(); ci != to_grounded_nodes.end(); ci++)
							for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = selective_to_grounded_nodes.begin(); ci != selective_to_grounded_nodes.end(); ci++)
							{
								DomainTransitionGraphNode* to_dtg_node = NULL;
								
								if (grounded_to_nodes)
								{
									to_dtg_node = *ci;
								}
								else
								{
									to_dtg_node = new DomainTransitionGraphNode(**ci);
								}
								
								// Try to establish the original transitions.
								Transition* new_transition = transition->migrateTransition(*from_dtg_node, *to_dtg_node);
								
								if (new_transition == NULL) continue;
								if (new_transition->finalise(*initial_facts_))
								{
									from_dtg_node->addTransition(*new_transition);
									dtg_nodes_to_add.push_back(to_dtg_node);
								}
								else
								{
									delete new_transition;
								}
							}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
							std::cout << " NEW: " << *from_dtg_node << std::endl;
#endif
							dtg_nodes_to_add.push_back(from_dtg_node);
						}
					}
					else
					{
						if (transition->finalise(*initial_facts_))
						{
							from_dtg_node_clone->addTransition(*transition);
							dtg_nodes_to_add.push_back(from_dtg_node_clone);
							dtg_nodes_to_add.push_back(to_dtg_node_clone);
						}
						else
						{
							delete transition;
						}
					}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
					std::cout << "ORG:" << *from_dtg_node_clone << std::endl;
					std::cout << "to: " << *to_dtg_node_clone << std::endl;
					std::cout << " -=- ";
					transition->getAction().print(std::cout, new_unprocessed_dtg->getBindings(), transition->getStepId());
					std::cout << std::endl << " -+----------+- " << std::endl;
#endif
				}
				
				dtg_nodes_to_remove.push_back(dtg_node);
			}
			
			for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = dtg_nodes_to_remove.begin(); ci != dtg_nodes_to_remove.end(); ci++)
			{
				new_unprocessed_dtg->removeNode(**ci);
			}

			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_nodes_to_add.begin(); ci != dtg_nodes_to_add.end(); ci++)
			{
				new_unprocessed_dtg->addNode(**ci);
			}
			
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Resulting DTG: " << *new_unprocessed_dtg << std::endl;
#endif
		}
	}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval end_time_unsupported_predicates;
	gettimeofday(&end_time_unsupported_predicates, NULL);
	
	time_spend = end_time_unsupported_predicates.tv_sec - start_time_unsupported_predicates.tv_sec + (end_time_unsupported_predicates.tv_usec - start_time_unsupported_predicates.tv_usec) / 1000000.0;
	std::cerr << "Creating DTGs for unsupported predicates: " << time_spend << " seconds" << std::endl;
#endif
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "After creating all DTGs:" << std::endl;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		std::cout << **ci << std::endl;
	}
#endif
	
	// After creating all the DTG and point-to-point transitions we will post process them as follows:
	// 1) Merge all DTG nodes which are identical.
	// 2) If a node A is a subset of node B then copy all transitions of node A to node B. E.g. (at driver loc) /\ (visited driver loc) is a
	// subset of (at driver log) so the transition walk must be added.
	// 3) For all transitions which involve the set of invariables A and produce the set B. If B / A != \emptyset then the difference are in-
	// variables which were implied due to grounding a term in the from-node. Apply the same transition to all DTG nodes which contain the 
	// difference. E.g. (at ticket loc -> (have driver ticket) /\ (at driver loc) imply the precondition (at driver log).
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval start_time_merge_dtgs;
	gettimeofday(&start_time_merge_dtgs, NULL);
#endif
	DomainTransitionGraph& combined_graph = mergeIdenticalDTGs(bindings);
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval end_time_merge_dtgs;
	gettimeofday(&end_time_merge_dtgs, NULL);
	time_spend = end_time_merge_dtgs.tv_sec - start_time_merge_dtgs.tv_sec + (end_time_merge_dtgs.tv_usec - start_time_merge_dtgs.tv_usec) / 1000000.0;
	std::cerr << "Merge identical DTGs took: " << time_spend << " seconds" << std::endl;
#endif
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "Combined graph after merging identical DTGs." << std::endl;
	std::cout << combined_graph << std::endl;
#endif
	
	combined_graph.removeUnconnectedNodes();
	combined_graph.solveSubsets();
	combined_graph.removeUnconnectedNodes();

/*
	std::ofstream ofs;
	ofs.open("combined_dtg.dot", std::ios::out);
	
	ofs << "digraph {" << std::endl;

	Graphviz::printToDot(ofs, combined_graph);
	
	ofs << "}" << std::endl;
	ofs.close();
*/
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval end_time_generation;
	gettimeofday(&end_time_generation, NULL);
	
	time_spend = end_time_generation.tv_sec - start_time_tim_translation.tv_sec + (end_time_generation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "Initialize structures: " << time_spend << " seconds" << std::endl;
#endif
	return combined_graph;
}

DomainTransitionGraph& DomainTransitionGraphManager::mergeIdenticalDTGs(Bindings& bindings)
{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "[DomainTransitionGraphManager::mergeIdenticalDTGs] Start." << std::endl;
#endif

	/**
	 * During merging we try to find all sets of nodes which are identical. That is they have identical facts with 
	 * identical domains. We do not care how the fact's terms relate to each other, this is irrelevant for the 
	 * reachability analysis we wish to perform (see reachability analysis and free variables). A single member 
	 * of this set (in our case the first instance we find) will serve as the root node and will represent all 
	 * the others in the merged LTG.
	 * 
	 * Note that the facts in two nodes might be identical but arranged in a sepparate way, therefore we keep track 
	 * of the index of the fact in the 'leaf' and how this relates to the 'root' node.
	 */
	std::map<const DomainTransitionGraphNode*, DomainTransitionGraphNode*> mapping_leaf_to_root_node;
	std::map<const DomainTransitionGraphNode*, int*> map_leaf_facts_to_root;
	
	// Accumulate all the transitions of the identical DTGs.
//	std::map<const DomainTransitionGraphNode*, std::vector<const Transition*>* > mapping_merged_transitions;
	std::set<const DomainTransitionGraphNode*> closed_list;
	
	std::vector<const DomainTransitionGraphNode*> unmerged_dtg_nodes;
	for (std::vector<DomainTransitionGraph*>::const_iterator objects_ci = objects_.begin(); objects_ci != objects_.end(); objects_ci++)
	{
		const DomainTransitionGraph* dtg = *objects_ci;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* dtg_node = *ci;
			if (closed_list.count(dtg_node) != 0)
				continue;
			closed_list.insert(dtg_node);
			
//			std::vector<const Transition*>* accumulated_dtgs = new std::vector<const Transition*>();
//			mapping_merged_transitions[dtg_node] = accumulated_dtgs;
			
			// Since the node is not in the closed list it is the very first instance so we map all the values to itself.
			mapping_leaf_to_root_node[dtg_node] = dtg_node;
			
			int* initial_mapping = new int[dtg_node->getAtoms().size()];
			for (unsigned int i = 0; i < dtg_node->getAtoms().size(); i++)
			{
				initial_mapping[i] = i;
			}
			
			map_leaf_facts_to_root[dtg_node] = initial_mapping;
			
//			accumulated_dtgs->insert(accumulated_dtgs->end(), dtg_node->getTransitions().begin(), dtg_node->getTransitions().end());
			bool merged = false;
			
			// Look for all dtg nodes which are identical.
			for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
			{
				const DomainTransitionGraph* dtg2 = *ci;
				
				for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg2->getNodes().begin(); ci != dtg2->getNodes().end(); ci++)
				{
					const DomainTransitionGraphNode* dtg_node2 = *ci;
					if (closed_list.count(dtg_node2) != 0)
						continue;
					bool dtg_node_is_equivalent = true;

					// Compare if the two nodes are identical.
					if (dtg_node->getAtoms().size() != dtg_node2->getAtoms().size())
						continue;
					
					for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
					{
						const BoundedAtom* bounded_atom = *ci;
						bool found_equivalent = false;
						
						for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node2->getAtoms().begin(); ci != dtg_node2->getAtoms().end(); ci++)
						{
							const BoundedAtom* bounded_atom2 = *ci;
							if (bounded_atom->getAtom().isNegative() == bounded_atom2->getAtom().isNegative() &&
							    dtg->getBindings().areEquivalent(bounded_atom->getAtom(), bounded_atom->getId(), bounded_atom2->getAtom(), bounded_atom2->getId(), &dtg2->getBindings()))
							{
								found_equivalent = true;
								break;
							}
						}
						
						if (!found_equivalent)
						{
							dtg_node_is_equivalent = false;
							break;
						}
					}
					
					if (!dtg_node_is_equivalent)
					{
						continue;
					}
					
					int* mapping = new int[dtg_node->getAtoms().size()];
					memset(mapping, -1, sizeof(int) * dtg_node->getAtoms().size());
					
					for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node2->getAtoms().begin(); ci != dtg_node2->getAtoms().end(); ci++)
					{
						unsigned int old_fact_index = std::distance(dtg_node2->getAtoms().begin(), ci);
						const BoundedAtom* bounded_atom = *ci;
						bool found_equivalent = false;
						
						for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
						{
							unsigned int new_fact_index = std::distance(dtg_node->getAtoms().begin(), ci);
							const BoundedAtom* bounded_atom2 = *ci;
							if (bounded_atom->getAtom().isNegative() == bounded_atom2->getAtom().isNegative() &&
							    dtg->getBindings().areEquivalent(bounded_atom->getAtom(), bounded_atom->getId(), bounded_atom2->getAtom(), bounded_atom2->getId(), &dtg2->getBindings()))
							{
								found_equivalent = true;
								mapping[old_fact_index] = new_fact_index;
								break;
							}
						}
						
						if (!found_equivalent)
						{
							dtg_node_is_equivalent = false;
							break;
						}
					}
					
					if (!dtg_node_is_equivalent)
					{
						delete mapping;
						continue;
					}
					
					// The two nodes are equivalent - merge!
					bool properties_differ = false;

					if (dtg_node->getAtoms().size() != dtg_node2->getAtoms().size())
					{
						properties_differ = true;
					}

					if (!properties_differ)
					{
						for (std::vector<BoundedAtom*>::const_iterator dtg_node_ci = dtg_node->getAtoms().begin(); dtg_node_ci != dtg_node->getAtoms().end(); dtg_node_ci++)
						{
							const BoundedAtom* bounded_atom = *dtg_node_ci;
							if (bounded_atom->getProperties().size() != dtg_node2->getAtoms()[std::distance(dtg_node->getAtoms().begin(), dtg_node_ci)]->getProperties().size())
							{
								properties_differ = true;
								break;
							}
							
							for (std::vector<const Property*>::const_iterator property_ci = bounded_atom->getProperties().begin(); property_ci != bounded_atom->getProperties().end(); property_ci++)
							{
								const Property* property = *property_ci;
								if (property != dtg_node2->getAtoms()[std::distance(dtg_node->getAtoms().begin(), dtg_node_ci)]->getProperties()[std::distance(bounded_atom->getProperties().begin(), property_ci)])
								{
									properties_differ = true;
									break;
								}
							}
							
							if (properties_differ)
							{
								break;
							}
						}
					}
					
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
					if (properties_differ)
					{
						std::cout << "Map: ";
						dtg_node2->print(std::cout);
						std::cout << " to ";
						dtg_node->print(std::cout);
						std::cout << std::endl;
					}
#endif
					//if (properties_differ) continue;
					merged = true;
					
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
					if (mapping_leaf_to_root_node.count(dtg_node2) != 0)
					{
						assert (mapping_leaf_to_root_node[dtg_node2] == dtg_node || mapping_leaf_to_root_node[dtg_node2] == dtg_node2);
						std::cout << "Overwrite: " << *dtg_node2 << " -> " << *mapping_leaf_to_root_node[dtg_node2] << " with "" -> " << *dtg_node << "." << std::endl;
					}
#endif
					map_leaf_facts_to_root[dtg_node2] = mapping;
					mapping_leaf_to_root_node[dtg_node2] = dtg_node;
//					accumulated_dtgs->insert(accumulated_dtgs->end(), dtg_node2->getTransitions().begin(), dtg_node2->getTransitions().end());
					
					closed_list.insert(dtg_node2);
				}
			}
			
			// If no other DTG node has been found mark the dtg node as not merged for post processing.
			if (!merged)
			{
				unmerged_dtg_nodes.push_back(dtg_node);
			}
		}
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_DEBUG
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		const DomainTransitionGraph* dtg = *ci;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			const DomainTransitionGraphNode* dtg_node = *ci;
			assert (mapping_leaf_to_root_node.count(dtg_node) == 1);
			for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
			{
				const Transition* transition = *ci;
				assert (mapping_leaf_to_root_node.count(&transition->getFromNode()) == 1);
				assert (mapping_leaf_to_root_node.count(&transition->getToNode()) == 1);
			}
		}
	}
#endif
	
	// Create a combined DTG.
	DomainTransitionGraph* combined_dtg = new DomainTransitionGraph(*this, *type_manager_, *action_manager_, *predicate_manager_, bindings, *initial_facts_);
	
	// Add all the merged DTG nodes, these exist of the following nodes:
	// 1) Nodes which have not been merged - no need to make any changes.
	// 2) All the nodes which have been merged.
	std::map<const DomainTransitionGraphNode*, DomainTransitionGraphNode*> org_node_to_combined_node;
	for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = unmerged_dtg_nodes.begin(); ci != unmerged_dtg_nodes.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		
		// Copy the DTG node and add it to the combined DTG.
		DomainTransitionGraphNode* new_dtg_node = new DomainTransitionGraphNode(*combined_dtg, std::numeric_limits< unsigned int >::max());
		new_dtg_node->copyAtoms(*dtg_node);
		
		combined_dtg->addNode(*new_dtg_node);
		org_node_to_combined_node[dtg_node] = new_dtg_node;
	}
	
	closed_list.clear();
	
	/**
	 * For the nodes which have been merged the following steps need to be taken:
	 * - Create a new DTG node for every unique DTG node and add it to the new DTG graph.
	 */
	for (std::map<const DomainTransitionGraphNode*, DomainTransitionGraphNode*>::const_iterator ci = mapping_leaf_to_root_node.begin(); ci != mapping_leaf_to_root_node.end(); ci++)
	{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		const DomainTransitionGraphNode* identical_dtg_node = (*ci).first;
#endif
		const DomainTransitionGraphNode* hub_dtg_node = (*ci).second;
		DomainTransitionGraphNode* combined_dtg_node = NULL;
		
		// If the node which will serve as the hub for all the identical nodes has not been added yet to the new DTG, do so now.
		if (closed_list.count(hub_dtg_node) == 0)
		{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			if (hub_dtg_node->getAtoms().size() > 1)
				std::cout << "Create a new hub node out of: " << *hub_dtg_node << " *** " << hub_dtg_node << " ***" << std::endl;
#endif

			// Copy the DTG node and add it to the combined DTG.
			combined_dtg_node = new DomainTransitionGraphNode(*combined_dtg, std::numeric_limits< unsigned int >::max());
			combined_dtg_node->copyAtoms(*hub_dtg_node);
			
			combined_dtg->addNode(*combined_dtg_node);
			closed_list.insert(hub_dtg_node);
			org_node_to_combined_node[hub_dtg_node] = combined_dtg_node;
		}
		else
		{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Found an identical node: " << *identical_dtg_node << " - combine it with:" << *hub_dtg_node << "." << std::endl;
#endif
			combined_dtg_node = org_node_to_combined_node[hub_dtg_node];
		}

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << "Result of merging / creating: " << *combined_dtg_node << std::endl;
#endif
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "Combined DTG: " << *combined_dtg << "." << std::endl;
#endif
	
	// Reconnect all the DTG nodes by copying the transitions.
	for (std::map<const DomainTransitionGraphNode*, DomainTransitionGraphNode*>::const_iterator ci = mapping_leaf_to_root_node.begin(); ci != mapping_leaf_to_root_node.end(); ci++)
	{
		const DomainTransitionGraphNode* leaf_from_dtg_node = (*ci).first;
		DomainTransitionGraphNode* root_from_dtg_node = org_node_to_combined_node[(*ci).second];
		
		assert (std::find(combined_dtg->getNodes().begin(), combined_dtg->getNodes().end(), root_from_dtg_node) != combined_dtg->getNodes().end());
		
		if (leaf_from_dtg_node == root_from_dtg_node) continue;
		
		int* from_fact_ordering = map_leaf_facts_to_root[leaf_from_dtg_node];
		
		for (std::vector<const Transition*>::const_iterator ci = leaf_from_dtg_node->getTransitions().begin(); ci != leaf_from_dtg_node->getTransitions().end(); ci++)
		{
			const Transition* leaf_transition = *ci;
			
			const DomainTransitionGraphNode& leaf_to_dtg_node = leaf_transition->getToNode();
			DomainTransitionGraphNode* root_to_dtg_node = org_node_to_combined_node[mapping_leaf_to_root_node[&leaf_to_dtg_node]];
			
			assert (&leaf_to_dtg_node != root_to_dtg_node);
			
			int* to_fact_ordering = map_leaf_facts_to_root[&leaf_to_dtg_node];
			
			/**
			 * Make sure the transition doesn't already exist.
			 */
			bool transitionAlreadyExists = false;
			for (std::vector<const Transition*>::const_iterator ci = root_from_dtg_node->getTransitions().begin(); ci != root_from_dtg_node->getTransitions().end(); ci++)
			{
				const Transition* existing_transition = *ci;
				if (&leaf_transition->getAction() == &existing_transition->getAction() &&
				    &existing_transition->getToNode() == root_to_dtg_node)
				{
					transitionAlreadyExists = true;
					break;
				}
			}
			
			if (transitionAlreadyExists) continue;
			
			Transition* new_transition = leaf_transition->migrateTransition(*root_from_dtg_node, *root_to_dtg_node, from_fact_ordering, to_fact_ordering);
			if (new_transition == NULL)
			{
				std::cout << "Could not migrate the transition: " << *leaf_transition << " to the root nodes: " << std::endl;
				std::cout << *root_from_dtg_node << std::endl;
				std::cout << " TO " << std::endl;
				std::cout << *root_to_dtg_node << std::endl;
				assert (false);
			}
			
			assert (&new_transition->getFromNode() == root_from_dtg_node);
			assert (&new_transition->getToNode() == root_to_dtg_node);
			
			if (!root_from_dtg_node->addTransition(*new_transition))
			{
				assert (false);
			}
		}
	}

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_DOT_OUTPUT
	/**
	 * Print out the result in DOT format.
	 */
	std::ofstream ofs;
	ofs.open("combined_dtgs.dot", std::ios::out);
	
	ofs << "digraph {" << std::endl;

	for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = combined_dtg->getNodes().begin(); ci != combined_dtg->getNodes().end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		
		// Only include it if is part of a transition.
		if (dtg_node->getTransitions().size() == 0)
		{
			bool partOfTransition = false;
			
			for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = combined_dtg->getNodes().begin(); ci != combined_dtg->getNodes().end(); ci++)
			{
				const DomainTransitionGraphNode* dtg_node2 = *ci;
				for (std::vector<const Transition*>::const_iterator ci = dtg_node2->getTransitions().begin(); ci != dtg_node2->getTransitions().end(); ci++)
				{
					const Transition* transition = *ci;
					if (&transition->getToNode() == dtg_node2)
					{
						partOfTransition = true;
						break;
					}
				}
				
				if (partOfTransition) break;
			}
			
			if (!partOfTransition) continue;
		}
		
		
		Graphviz::printToDot(ofs, *dtg_node);
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			Graphviz::printToDot(ofs, *transition, dtg_node->getDTG().getBindings());
		}
	}
	
	ofs << "}" << std::endl;
	ofs.close();
#endif
	return *combined_dtg;
}

unsigned int* DomainTransitionGraphManager::getRelativeIndexes(const DomainTransitionGraphNode& source, const DomainTransitionGraphNode& destination, unsigned int* assignments, unsigned int index, const Bindings& bindings) const
{
/*	std::cout << "Assignments so far: ";
	for (unsigned int i = 0; i < index; i++)
	{
		std::cout << assignments[i];
		if (i != index - 1)
			std::cout << ", " ;
	}
	std::cout << "." << std::endl;
*/
	// Check if we're done.
	if (index == source.getAtoms().size())
	{
		return assignments;
	}
	
	// Map the bounded atoms in the source to the destination.
	// Map the `index`th atom to a atom in the destination node.
	const BoundedAtom* source_bounded_atom = source.getAtoms()[index];
	
	for (std::vector<BoundedAtom*>::const_iterator ci = destination.getAtoms().begin(); ci != destination.getAtoms().end(); ci++)
	{
		const BoundedAtom* candidate_fact = *ci;
		unsigned int candidate_index = std::distance(destination.getAtoms().begin(), ci);
		
		// Check if this one hasn't been assigned yet!
		bool already_assigned = false;
		for (unsigned int i = 0; i < index; i++)
		{
			if (assignments[i] == candidate_index)
			{
				already_assigned = true;
				break;
			}
		}
		
		if (already_assigned) continue;
		
		/**
		 * If we have found a fact in the destination DTG node which matches with the `index`th source fact, we
		 * need to check if all the assignments made so far match up with the relationships between the terms in
		 * the destination DTG node.
		 * 
		 * E.g. consider the following two nodes:
		 * (on block block')
		 * (on block' block*)
		 * (clear block*)
		 *
		 * AND
		 *
		 * (clear block*)
		 * (on block' block*)
		 * (on block block')
		 *
		 * Then we need to make sure that we make the following mapping:
		 * 0 -> 2
		 * 1 -> 1
		 * 2 -> 0
		 */
		if (source_bounded_atom->canUnifyWith(*candidate_fact, bindings))
		{
			bool mappings_match = true;
			
			// Go over the previous made bindings and check if any of these atoms have a variable domain in common.
			for (unsigned int i = 0; i < index; i++)
			{
				// Note that we have made the mapping from i (source) -> assignments[i] (destination).
				const BoundedAtom* destination_assigned_fact = destination.getAtoms()[assignments[i]];
				const BoundedAtom* source_assigned_fact = source.getAtoms()[i];
				
				// Check if any of the terms in the ith and matching_index matches up.
				for (unsigned int j = 0; j < candidate_fact->getAtom().getArity(); j++)
				{
					const std::vector<const Object*>& candidate_variable_domain = candidate_fact->getVariableDomain(j, bindings);
					const std::vector<const Object*>& source_variable_domain = source.getAtoms()[index]->getVariableDomain(j, bindings);
					
					for (unsigned int k = 0; k < destination_assigned_fact->getAtom().getArity(); k++)
					{
						const std::vector<const Object*>& destination_assigned_variable_domain = destination_assigned_fact->getVariableDomain(k, bindings);
						const std::vector<const Object*>& source_assigned_variable_domain = source_assigned_fact->getVariableDomain(k, bindings);
						
						// If they are similar, make sure the same relationship exists between the source facts.
						if (&candidate_variable_domain == &destination_assigned_variable_domain)
						{
							// Assert that the same relation holds between the source facts.
							if (&source_variable_domain != &source_assigned_variable_domain)
							{
								mappings_match = false;
								break;
							}
						}
						// Otherwise they are not similar and the source variable domains also must be different.
						else if (&source_variable_domain == &source_assigned_variable_domain)
						{
							mappings_match = false;
							break;
						}
					}
					
					if (!mappings_match) break;
				}
				
				if (!mappings_match) break;
			}
			
			if (!mappings_match) continue;
			
			// We have found a possible mapping!
			unsigned int* new_assignments = new unsigned int[source.getAtoms().size()];
			memcpy(&new_assignments[0], assignments, sizeof(unsigned int) * source.getAtoms().size());
			new_assignments[index] = candidate_index;
			
//			std::cout << "[" << index << "] Attempt: " << candidate_index << "." << std::endl;
			
			return getRelativeIndexes(source, destination, new_assignments, index + 1, bindings);
		}
	}
	
//	std::cout << "[" << index << "] No mapping, backtrack!" << std::endl;
	return NULL;
}

void DomainTransitionGraphManager::resolveAllProperties()
{
	// Sort out all properties for all LTG nodes.
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* dtg_node = *ci;
			
			for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node->getAtoms().begin(); ci != dtg_node->getAtoms().end(); ci++)
			{
				BoundedAtom* fact = *ci;
				
				resolveAllProperties(*fact, dtg->getBindings());
			}
		}
	}
}

void DomainTransitionGraphManager::resolveAllProperties(BoundedAtom& bounded_atom, const Bindings& bindings)
{
	// Check if we can figure out the property(ies) linked with this precondition.
	std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_nodes;
	getDTGNodes(found_nodes, bounded_atom.getId(), bounded_atom.getAtom(), bindings, ALL_INVARIABLE_INDEXES);
	
	for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ci++)
	{
		const std::vector<const Property*>& existing_property_set = (*ci).second->getProperties();
		
		// If any of the properties point to the invariable term, we can add it.
		for (std::vector<const Property*>::const_iterator ci = existing_property_set.begin(); ci != existing_property_set.end(); ci++)
		{
			bounded_atom.addProperty(**ci);
		}
	}
}

void DomainTransitionGraphManager::createPointToPointTransitions()
{
	resolveAllProperties();
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << " *************** [DomainTransitionGraphManager::createPointToPointTransitions] *******************" << std::endl;
#endif

	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << "[DomainTransitionGraphManager::createPointToPointTransitions] Check DTG: " << *dtg << std::endl;
#endif

		// Keep track of which new dtg nodes to add and which ones to remove.
		std::vector<DomainTransitionGraphNode*> dtg_nodes_to_add;
		std::vector<DomainTransitionGraphNode*> dtg_nodes_to_remove;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			DomainTransitionGraphNode* dtg_node = *ci;
			
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "[DomainTransitionGraphManager::createPointToPointTransitions] Check DTG Node: ";
			dtg_node->print(std::cout);
			std::cout << std::endl;
#endif

			for (unsigned int i = 0; i < dtg_node->getTransitions().size(); i++)
			{
				const Transition* org_transition = dtg_node->getTransitions()[i];
				DomainTransitionGraphNode* from_dtg_node_clone = new DomainTransitionGraphNode(*dtg_node);
				DomainTransitionGraphNode* to_dtg_node_clone = new DomainTransitionGraphNode(org_transition->getToNode());
				
				assert (&from_dtg_node_clone->getDTG() == &dtg_node->getDTG());
				assert (&to_dtg_node_clone->getDTG() == &dtg_node->getDTG());
				
				// Migrate the original transition to the cloned nodes.
				Transition* transition = org_transition->migrateTransition(*from_dtg_node_clone, *to_dtg_node_clone);
				
				if (transition == NULL)
				{
					std::cout << "Could not migrate the transition: " << std::endl;
					std::cout << *org_transition << std::endl;
					std::cout << "To the following pair: from: " << std::endl;
					std::cout << *from_dtg_node_clone << std::endl;
					std::cout << " TO " << std::endl;
					std::cout << *to_dtg_node_clone << std::endl;
					assert (false);
				}

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "[DomainTransitionGraphManager::createPointToPointTransitions] Original transition: " << *org_transition << std::endl;
				std::cout << "[DomainTransitionGraphManager::createPointToPointTransitions] Process the transition: " << *transition << std::endl;
#endif

				// Find out the invariable for this transition.
				assert (transition->getBalancedTerm() != NULL);

				// All new atoms which need to be added to the from node.
				std::vector<const Atom*> preconditions_to_add_to_from_node;
				
				// Some preconditions also need to be added to the to node - converted into a bounded node.
				std::vector<const Atom*> facts_to_add_to_to_node;
				
				// All sets of new preconditions / effects which are persistent.
				std::vector<std::pair<const Atom*, const Atom*> > new_persistent_sets;
				
				// Terms in the from node which need to be grounded.
				std::vector<const std::vector<const Object*>* > variable_domains_to_ground;
				
				bool finished = false;
				while (!finished)
				{
					finished = true;
					
					/**
					 * Check which terms in the transition's preconditions correspond with those of the from node. For each of
					 * these terms we have a piecewise function:
					 *
					 * Ground from_{term}             if precondition_{term} is 'unbalanced'
					 * Add precondition to from       otherwise
					 *
					 * A predicate's term is unbalanced if it does not occur in any DTG node with the term being the invariable. 
					 * Another way of putting it is saying that the predicate - given the term as index - is an attribute in 
					 * TIM terms.
					 *
					 * In addition if this term is shared between a node of the from node and a term of the to node and it 
					 * is unbalanced in the context of the fact it appears in in the to node, it also needs to be grounded.
					 */
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator precondition_ci = transition->getAllPreconditions().begin(); precondition_ci != transition->getAllPreconditions().end(); precondition_ci++)
					{
						const Atom* precondition = (*precondition_ci).first;

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
						std::cout << "Process the precondition: ";
						precondition->print(std::cout, dtg->getBindings(), transition->getStepId());
						std::cout << "." << std::endl;
#endif

						// Ignore those which are already part of the DTG node.
						const BoundedAtom* identical_bounded_atom = NULL;
						for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node_clone->getAtoms().begin(); ci != from_dtg_node_clone->getAtoms().end(); ci++)
						{
							const BoundedAtom* bounded_atom = *ci;
							if (dtg->getBindings().areIdentical(bounded_atom->getAtom(), bounded_atom->getId(), *precondition, transition->getStepId()))
							{
								identical_bounded_atom = bounded_atom;
								break;
							}
						}
						
						if (identical_bounded_atom != NULL)
						{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
							std::cout << "Already part of the DTG, moving on!" << std::endl;
#endif
							/**
							 * If the term is not removed by the effects of the action and it is balanced, we must add it to the to node.
							 */
							if (!precondition->getPredicate().isStatic() && !transition->isPreconditionRemoved(*precondition))
							{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
								std::cout << "Add the predicate to the to node!" << std::endl;
#endif
								// Update the transitions to reflect that the said precondition is a persistent fact.
								facts_to_add_to_to_node.push_back(precondition);
								new_persistent_sets.push_back(std::make_pair(precondition, precondition));
							}
							continue;
						}
						
						bool precondition_added_to_from_node = false;
						bool contains_balanced_term = false;
						
						/**
						 * Check all pairwise terms of the precondition and all the facts in the from node. If the terms are the same three things
						 * can happen:
						 * 1) The precondition is added to the from node:
						 * - If the term is the invariable and the invariable occurs in the precondition it needs to be added.
						 * - If the term is an invariable in a separate DTG it needs to be added too. (*)
						 * - If the term is part of the to node and is invariable, it needs to be added.
						 * 2) Ground the term:
						 * - If the term is not part of any balanced set it will need to be grounded.
						 * - If the term is part of a balanced set, but appears in a term in the to node where it is not balanced.
						 * 3) Leave it if its already part of the DTG node.
						 *
						 * (*) Need to look into this, does not seem right.
						 */
						const Bindings& bindings = dtg_node->getDTG().getBindings();
						
						// Compare with the from dtg node.
						for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ci++)
						{
							const Term* precondition_term = *ci;
							unsigned int precondition_term_index = std::distance(precondition->getTerms().begin(), ci);
							
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
							std::cout << "Process the " << precondition_term_index << "th term: ";
							precondition_term->print(std::cout, bindings, transition->getStepId());
							std::cout << "{" << &precondition_term->getDomain(transition->getStepId(), bindings) << "}" << std::endl;
#endif
							
							// Check if the precondition term is balanced. If this isn't the case than any matching term found must be grounded!
							std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_matching_nodes;
							getDTGNodes(found_matching_nodes, transition->getStepId(), *precondition, bindings, precondition_term_index);
							
							bool precondition_is_balanced = !found_matching_nodes.empty() || transition->getBalancedTerm() == precondition_term;
//							bool precondition_is_balanced = transition->getBalancedTerm() == precondition_term;
							
							bool is_grounded = false;
							
							if (precondition_is_balanced)
							{
								contains_balanced_term = true;
							}
							
							if (!precondition_is_balanced)
							{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
								std::cout << "Is not balanced - potentially ground!" << std::endl;
#endif
								// Ground the term if it is part of any term in the from node!
								const std::vector<const Object*>& precondition_variable_domain = precondition_term->getDomain(transition->getStepId(), bindings);
								for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node_clone->getAtoms().begin(); ci != from_dtg_node_clone->getAtoms().end(); ci++)
								{
									const BoundedAtom* bounded_atom = *ci;

									unsigned int invariable_index = bounded_atom->containsVariableDomain(precondition_variable_domain, bindings);
									if (invariable_index != NO_INVARIABLE_INDEX)
									{
										// Check if the term is balanced in the bounded_atom.
										if (bounded_atom->isBalanced(invariable_index)) break;
										
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
										std::cout << "Confirm grounding!" << std::endl;
#endif
										is_grounded = true;
										variable_domains_to_ground.push_back(&precondition_term->getDomain(transition->getStepId(), bindings));
										break;
									}
								}
								
								if (!is_grounded)
								{
									// OR if it is part of any term in the to node!
									for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node_clone->getAtoms().begin(); ci != to_dtg_node_clone->getAtoms().end(); ci++)
									{
										const BoundedAtom* bounded_atom = *ci;
										
										unsigned int invariable_index = bounded_atom->containsVariableDomain(precondition_variable_domain, bindings);
										if (invariable_index != std::numeric_limits< unsigned int>::max())
										{
											// Check if the term is balanced in the bounded_atom.
											if (bounded_atom->isBalanced(invariable_index)) break;

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
											std::cout << "Confirm grounding!" << std::endl;
#endif
											is_grounded = true;
											variable_domains_to_ground.push_back(&precondition_term->getDomain(transition->getStepId(), bindings));
											break;
										}
									}
								}
							}
							
							if (!is_grounded && !precondition_added_to_from_node)
							{
								// If the term IS balanced, check if it matches any of the terms in the from dtg_node's facts.
								for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node_clone->getAtoms().begin(); ci != from_dtg_node_clone->getAtoms().end(); ci++)
								{
									const BoundedAtom* bounded_atom = *ci;
									
									for( std::vector<const Term*>::const_iterator bounded_atom_ci = bounded_atom->getAtom().getTerms().begin(); bounded_atom_ci != bounded_atom->getAtom().getTerms().end(); bounded_atom_ci++)
									{
										const Term* from_term = *bounded_atom_ci;
										
										if (from_term->isTheSameAs(bounded_atom->getId(), *precondition_term, transition->getStepId(), bindings))
										{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
											std::cout << "Add the predicate to the from node!" << std::endl;
#endif
											preconditions_to_add_to_from_node.push_back(precondition);
											precondition_added_to_from_node = true;
											finished = false;
											break;
										}
									}
									
									if (precondition_added_to_from_node) break;
								}
							}
						}
						
						/**
						 * If the term is not removed by the effects of the action and it is balanced, we must add it to the to node.
						 */
						if (contains_balanced_term && !transition->isPreconditionRemoved(*precondition))
						{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
							std::cout << "Add the predicate to the to node!" << std::endl;
#endif
							facts_to_add_to_to_node.push_back(precondition);
							new_persistent_sets.push_back(std::make_pair(precondition, precondition));
						}
						else
						{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
							std::cout << "Do not add the predicate to the to node!" << std::endl;
#endif
						}
					}
					
					for (std::vector<const Atom*>::const_iterator ci = preconditions_to_add_to_from_node.begin(); ci != preconditions_to_add_to_from_node.end(); ci++)
					{
						const Atom* precondition_to_add = *ci;
						BoundedAtom* bounded_precondition_to_add = new BoundedAtom(transition->getStepId(), *precondition_to_add);
						resolveAllProperties(*bounded_precondition_to_add, from_dtg_node_clone->getDTG().getBindings());
						
						assert (transition->getBalancedTerm() != NULL);
						
						from_dtg_node_clone->addAtom(*bounded_precondition_to_add, bounded_precondition_to_add->containsVariableDomain(transition->getBalancedTerm()->getDomain(transition->getStepId(), dtg->getBindings()), dtg->getBindings()));
						transition->addedFromNodePrecondition(*precondition_to_add);
					}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
					if (!preconditions_to_add_to_from_node.empty())
					{
						std::cout << "From DTG node after adding atoms: " << *from_dtg_node_clone << "." << std::endl;
					}
#endif
					preconditions_to_add_to_from_node.clear();
					
					/**
					 * In addition add all the effects which are added and refer to an invariable in the to node.
					 */
					const std::vector<std::pair<const Atom*, InvariableIndex> >& effects = transition->getAllEffects();
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
					{
						facts_to_add_to_to_node.push_back((*ci).first);
					}
					
					for (std::vector<const Atom*>::const_iterator ci = facts_to_add_to_to_node.begin(); ci != facts_to_add_to_to_node.end(); ci++)
					{
						const Atom* fact_to_add = *ci;
						if (fact_to_add->isNegative()) continue;
						
						// Make sure it isn't already part of the to node!
						bool is_already_part = false;
						for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node_clone->getAtoms().begin(); ci != to_dtg_node_clone->getAtoms().end(); ci++)
						{
							const BoundedAtom* to_node_fact = *ci;
							
							if (to_dtg_node_clone->getDTG().getBindings().areIdentical(to_node_fact->getAtom(), to_node_fact->getId(), *fact_to_add, transition->getStepId()))
							{
								is_already_part = true;
								break;
							}
						}
						
						if (is_already_part) continue;
						
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
						std::cout << "Process the precondition / effect: ";
						fact_to_add->print(std::cout, dtg->getBindings(), transition->getStepId());
						std::cout << std::endl;
#endif

						// Check if it references any invariable in the to node.
						bool references_invariable = false;
						for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node_clone->getAtoms().begin(); ci != to_dtg_node_clone->getAtoms().end(); ci++)
						{
							const BoundedAtom* to_node_fact = *ci;
							
							for (unsigned int i = 0; i < to_node_fact->getAtom().getArity(); i++)
							{
								if (!to_node_fact->isBalanced(i)) continue;
								
								if (fact_to_add->containsVariableDomain(transition->getStepId(), to_node_fact->getVariableDomain(i, dtg->getBindings()), dtg->getBindings()) != NO_INVARIABLE_INDEX)
								{
									references_invariable = true;
									break;
								}
							}
							
							if (references_invariable) break;
						}
						
						// ALternatively, if the precondition / effect itself has an invariable which matches with a term in the to node add it as well.
						// This happens - for example - in the driverlog domain with the fact (at package loc) -> (in package truck), because (in_1) is 
						// not a balanced property while at_0 is!
						
						BoundedAtom* bounded_fact_to_add = NULL;
						if (!references_invariable)
						{
							bounded_fact_to_add = new BoundedAtom(transition->getStepId(), *fact_to_add);
							resolveAllProperties(*bounded_fact_to_add, to_dtg_node_clone->getDTG().getBindings());
							
							for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node_clone->getAtoms().begin(); ci != to_dtg_node_clone->getAtoms().end(); ci++)
							{
								const BoundedAtom* to_node_fact = *ci;
							
								for (unsigned int i = 0; i < bounded_fact_to_add->getAtom().getArity(); i++)
								{
									if (!bounded_fact_to_add->isBalanced(i)) continue;
									
									if (to_node_fact->containsVariableDomain(bounded_fact_to_add->getVariableDomain(i, dtg->getBindings()), dtg->getBindings()) != NO_INVARIABLE_INDEX)
									{
										references_invariable = true;
										break;
									}
								}
								
								if (references_invariable) break;
							}
							
							if (!references_invariable)
							{
								// TODO: Memory leak!
//								delete bounded_fact_to_add;
								continue;
							}
						}
						
						if (bounded_fact_to_add == NULL)
						{
							bounded_fact_to_add = new BoundedAtom(transition->getStepId(), *fact_to_add);
							resolveAllProperties(*bounded_fact_to_add, to_dtg_node_clone->getDTG().getBindings());
						}
						
						assert (transition->getBalancedTerm() != NULL);
						
						to_dtg_node_clone->addAtom(*bounded_fact_to_add, bounded_fact_to_add->containsVariableDomain(transition->getBalancedTerm()->getDomain(transition->getStepId(), dtg->getBindings()), dtg->getBindings()));
						
						transition->addedToNodeFact(*fact_to_add);
					}
					
					facts_to_add_to_to_node.clear();
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT					
					if (!preconditions_to_add_to_from_node.empty())
					{
						std::cout << "To DTG node after adding atoms: " << *to_dtg_node_clone << "." << std::endl;
					}
#endif
					
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
					std::cout << "[END] Add the effects!" << std::endl;
#endif
				}
				
				/**
				 * If a term is shared between the from and to node and it is not balanced, it needs to be grounded too!
				 * Unless it's the exact same fact!
				 */
				for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node_clone->getAtoms().begin(); ci != from_dtg_node_clone->getAtoms().end(); ci++)
				{
					const BoundedAtom* from_bounded_atom = *ci;
					
					for (unsigned int i = 0; i < from_bounded_atom->getAtom().getArity(); i++)
					{
						std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_nodes;
						getDTGNodes(found_nodes, from_bounded_atom->getId(), from_bounded_atom->getAtom(), from_dtg_node_clone->getDTG().getBindings(), i);
					
						if (!found_nodes.empty()) continue;
						
						const std::vector<const Object*>& imbalanced_variable_domain = from_bounded_atom->getVariableDomain(i, from_dtg_node_clone->getDTG().getBindings());
						
						for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node_clone->getAtoms().begin(); ci != to_dtg_node_clone->getAtoms().end(); ci++)
						{
							const BoundedAtom* to_bounded_atom = *ci;
							if (to_bounded_atom->containsVariableDomain(imbalanced_variable_domain, to_dtg_node_clone->getDTG().getBindings()) != std::numeric_limits< unsigned int>::max() &&
							    !from_bounded_atom->isIdenticalTo(*to_bounded_atom, to_dtg_node_clone->getDTG().getBindings()))
							{
								variable_domains_to_ground.push_back(&imbalanced_variable_domain);
								break;
							}
						}
					}
				}

				/**
				 * Ground all the terms which need to be grounded and add the result to the final DTG.
				 */
				std::vector<std::pair<DomainTransitionGraphNode*, std::map<const std::vector<const Object*>*, const Object*>* > > from_grounded_nodes;
				bool grounded_from_nodes = from_dtg_node_clone->groundTerms(from_grounded_nodes, variable_domains_to_ground);
				
				if (grounded_from_nodes)
				{
					from_dtg_node_clone->removeTransitions();
					dtg_nodes_to_remove.push_back(dtg_node);
				}
				
				std::vector<std::pair<DomainTransitionGraphNode*, std::map<const std::vector<const Object*>*, const Object*>* > > to_grounded_nodes;
				bool grounded_to_nodes = to_dtg_node_clone->groundTerms(to_grounded_nodes, variable_domains_to_ground);
				if (grounded_to_nodes)
				{
					to_dtg_node_clone->removeTransitions();
					dtg_nodes_to_remove.push_back(&transition->getToNode());
				}
				
//				std::cerr << "Ground ";
//				transition->getStep()->getAction().print(std::cerr, transition->getFromNode().getDTG().getBindings(), transition->getStep()->getStepId());
//				std::cerr << " into: " << from_grounded_nodes.size() << " / " << to_grounded_nodes.size() << " nodes!" << std::endl;
				
				for (std::vector<const std::vector<const Object*>* >::const_iterator ci = variable_domains_to_ground.begin(); ci != variable_domains_to_ground.end(); ci++)
				{
					grounded_objects_.insert((*ci)->begin(), (*ci)->end());
				}

				if (grounded_from_nodes || grounded_to_nodes)
				{
					for (std::vector<std::pair<DomainTransitionGraphNode*, std::map<const std::vector<const Object*>*, const Object*>* > >::const_iterator ci = from_grounded_nodes.begin(); ci != from_grounded_nodes.end(); ci++)
					{
						
						DomainTransitionGraphNode* from_dtg_node = NULL;
						
						if (grounded_from_nodes)
						{
							from_dtg_node = (*ci).first;
						}
						else
						{
							from_dtg_node = new DomainTransitionGraphNode(*(*ci).first);
						}
						
						// Ground the to node too, but with respect to the variables already grounded!
						std::vector<DomainTransitionGraphNode*> selective_to_grounded_nodes;
						bool grounded_to_nodes = to_dtg_node_clone->groundTerms(selective_to_grounded_nodes, variable_domains_to_ground, *(*ci).second);
						if (grounded_to_nodes)
						{
							to_dtg_node_clone->removeTransitions();
							dtg_nodes_to_remove.push_back(&transition->getToNode());
						}
						
						//std::cerr << to_grounded_nodes.size() << " v.s. " << selective_to_grounded_nodes.size() << std::endl;
						
						
						//for (std::vector<std::pair<DomainTransitionGraphNode*, std::map<const std::vector<const Object*>*, const Object*>* > >::const_iterator ci = to_grounded_nodes.begin(); ci != to_grounded_nodes.end(); ci++)
						for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = selective_to_grounded_nodes.begin(); ci != selective_to_grounded_nodes.end(); ci++)
						{
							DomainTransitionGraphNode* to_dtg_node = NULL;
							
							if (grounded_to_nodes)
							{
								to_dtg_node = *ci;
							}
							else
							{
								to_dtg_node = new DomainTransitionGraphNode(**ci);
							}
							
							// Try to establish the original transitions.
							Transition* new_transition = transition->migrateTransition(*from_dtg_node, *to_dtg_node);
							
							if (new_transition == NULL) continue;
							if (new_transition->finalise(*initial_facts_))
							{
								from_dtg_node->addTransition(*new_transition);
								dtg_nodes_to_add.push_back(to_dtg_node);
							}
							else
							{
								delete new_transition;
							}
						}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
						std::cout << " NEW: " << *from_dtg_node << std::endl;
#endif
						dtg_nodes_to_add.push_back(from_dtg_node);
					}
				}
				else
				{
					if (transition->finalise(*initial_facts_))
					{
						from_dtg_node_clone->addTransition(*transition);
						dtg_nodes_to_add.push_back(from_dtg_node_clone);
						dtg_nodes_to_add.push_back(to_dtg_node_clone);
					}
					else
					{
						delete transition;
					}
				}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "ORG:" << *from_dtg_node_clone << std::endl;
				std::cout << "to: " << *to_dtg_node_clone << std::endl;
				std::cout << " -=- ";
				transition->getAction().print(std::cout, dtg->getBindings(), transition->getStepId());
				std::cout << std::endl << " -+----------+- " << std::endl;
#endif
			}
			
			dtg_nodes_to_remove.push_back(dtg_node);
		}
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_nodes_to_remove.begin(); ci != dtg_nodes_to_remove.end(); ci++)
		{
				dtg->removeNode(**ci);
		}
				
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg_nodes_to_add.begin(); ci != dtg_nodes_to_add.end(); ci++)
		{
			dtg->addNode(**ci);
		}
		
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << " -+- Final result -+- " << std::endl;
		std::cout << *dtg << std::endl;
		std::cout << " -+- THE END -+- " << std::endl;
#endif
	}
/*
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	**
	 * Print out the result in DOT format.
	 *
	std::ofstream ofs;
	ofs.open("relaxed_dtgs.dot", std::ios::out);
	
	ofs << "digraph {" << std::endl;

	for (std::vector<const DomainTransitionGraphNode*>::const_iterator ci = resulting_nodes.begin(); ci != resulting_nodes.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = *ci;
		Graphviz::printToDot(ofs, *dtg_node);
		
		for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
		{
			const Transition* transition = *ci;
			Graphviz::printToDot(ofs, *transition, dtg_node->getDTG().getBindings());
		}
	}
	
	ofs << "}" << std::endl;
	ofs.close();
#endif
*/
}

bool DomainTransitionGraphManager::isTermStatic(const Atom& atom, StepID step_id, InvariableIndex term_index, const Bindings& bindings) const
{
	std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_dtg_nodes;
	getDTGNodes(found_dtg_nodes, step_id, atom, bindings);
	
	for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_dtg_nodes.begin(); ci != found_dtg_nodes.end(); ci++)
	{
		const DomainTransitionGraphNode* dtg_node = (*ci).first;
		const BoundedAtom* bounded_atom = (*ci).second;
		
		if (dtg_node->getIndex(*bounded_atom) == term_index)
		{
			return false;
		}
	}
	
	return true;
}
bool DomainTransitionGraphManager::removeDTG(const DomainTransitionGraph& dtg)
{
	for (std::vector<DomainTransitionGraph*>::iterator i = objects_.begin(); i != objects_.end(); i++)
	{
		if (&dtg == *i)
		{
			objects_.erase(i);
			return true;
		}
	}
	
	return false;
}

void DomainTransitionGraphManager::getDTGs(std::vector<const DomainTransitionGraph*>& found_dtgs, StepID step_id, const Atom& atom, const Bindings& bindings, unsigned int index) const
{
	// For each DTG find if there is a node which can unify with the given atom and id.
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > dtg_nodes;
		(*ci)->getNodes(dtg_nodes, step_id, atom, bindings, index);

		if (dtg_nodes.size() > 0)
		{
			found_dtgs.push_back(*ci);
		}
	}
}

void DomainTransitionGraphManager::getDTGNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& found_dtg_nodes, StepID step_id, const Atom& atom, const Bindings& bindings, unsigned int index) const
{
	// For each DTG find if there is a node which can unify with the given atom and id.
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		///std::vector<const SAS_Plus::DomainTransitionGraphNode*> dtg_nodes;
		///(*ci)->getNodes(dtg_nodes, step_id, atom, bindings, index);
		///found_dtg_nodes.insert(found_dtg_nodes.end(), dtg_nodes.begin(), dtg_nodes.end());
		(*ci)->getNodes(found_dtg_nodes, step_id, atom, bindings, index);
	}
}

void DomainTransitionGraphManager::getDTGNodes(std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >& found_dtg_nodes, const std::vector<const Atom*>& initial_facts, const Bindings& bindings) const
{
	// For each DTG find if there is a node which can unify with the given atom and id.
 	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		///std::vector<const SAS_Plus::DomainTransitionGraphNode*> dtg_nodes;
		///(*ci)->getNodes(dtg_nodes, initial_facts, bindings);
		///found_dtg_nodes.insert(found_dtg_nodes.end(), dtg_nodes.begin(), dtg_nodes.end());
		(*ci)->getNodes(found_dtg_nodes, initial_facts, bindings);
	}
}

};

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::Transition& transition, const Bindings& bindings)
{
	printToDot(ofs, transition.getFromNode());
	ofs << " -> ";
	printToDot(ofs, transition.getToNode());
	ofs << "[ label=\"";
	transition.getAction().print(ofs, bindings, transition.getStepId());
	ofs << "\"]" << std::endl;
}

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraphNode& dtg_node)
{
	ofs << "\"[" << &dtg_node << "] ";
	for (std::vector<SAS_Plus::BoundedAtom*>::const_iterator ci = dtg_node.getAtoms().begin(); ci != dtg_node.getAtoms().end(); ci++)
	{
		(*ci)->print(ofs, dtg_node.getDTG().getBindings(), false);
		
		if (ci + 1 != dtg_node.getAtoms().end())
		{
			ofs << "\\n";
		}
	}
	ofs << "\"";
}

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraph& dtg)
{
	// Declare the nodes.
	for (std::vector<SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = dtg.getNodes().begin(); ci != dtg.getNodes().end(); ci++)
	{
		const SAS_Plus::DomainTransitionGraphNode* dtg_node = *ci;
		printToDot(ofs, *dtg_node);
		ofs << std::endl;
	}
	
	// Create the edges.
	for (std::vector<SAS_Plus::DomainTransitionGraphNode*>::const_iterator ci = dtg.getNodes().begin(); ci != dtg.getNodes().end(); ci++)
	{
		const SAS_Plus::DomainTransitionGraphNode* dtg_node = *ci;
		const std::vector<const SAS_Plus::Transition*>& transitions = dtg_node->getTransitions();

		for (std::vector<const SAS_Plus::Transition*>::const_iterator transitions_ci = transitions.begin(); transitions_ci != transitions.end(); transitions_ci++)
		{
			const SAS_Plus::Transition* transition = *transitions_ci;
			printToDot(ofs, *transition, dtg.getBindings());
		}
	}
}

void Graphviz::printToDot(const SAS_Plus::DomainTransitionGraphManager& dtg_manager)
{
	std::ofstream ofs;
	ofs.open("dtgs.dot", std::ios::out);
	
	ofs << "digraph {" << std::endl;

	for (std::vector<SAS_Plus::DomainTransitionGraph*>::const_iterator ci = dtg_manager.getManagableObjects().begin(); ci != dtg_manager.getManagableObjects().end(); ci++)
	{
		Graphviz::printToDot(ofs, **ci);
	}
	
	ofs << "}" << std::endl;
	ofs.close();
}

void Graphviz::printPredicatesToDot(std::ofstream& ofs, const SAS_Plus::DomainTransitionGraph& dtg)
{
/*		const std::vector<const MyPOP::SAS_Plus::Property*>& predicates = dtg.getPredicates();
		
		ofs << "\"[" << dtg.getId() << "] ";
		for (std::vector<const MyPOP::SAS_Plus::Property*>::const_iterator pred_ci = predicates.begin(); pred_ci != predicates.end(); pred_ci++)
		{
			ofs << (*pred_ci)->getPredicate();
			if (pred_ci + 1 != predicates.end())
			{
				ofs << ", ";
			}
		}
		ofs << "\"";
		*/
}

};
