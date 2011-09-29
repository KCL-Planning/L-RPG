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

///#define MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
///#define MYPOP_SAS_PLUS_DTG_MANAGER_DEBUG
///#define MYPOP_SAS_PLUS_DTG_MANAGER_DOT_OUTPUT

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
	std::vector<const Property*>* properties = new std::vector<const Property*>();
	properties->push_back(&property);
	return *(new BoundedAtom(new_step_id, atom, *properties));
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

}

StepID BoundedAtom::getId() const
{
	return id_;
}

const Atom& BoundedAtom::getAtom() const
{
	return *atom_;
}

InvariableIndex BoundedAtom::getIndex(StepID id, const Term& term, const Bindings& bindings) const
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
}

/*const Property* BoundedAtom::getProperty() const
{
	return property_;
}*/

const std::vector<const Property*>& BoundedAtom::getProperties() const
{
	return properties_;
}

unsigned int BoundedAtom::constainsVariableDomain(const std::vector<const Object*>& variable_domain, const Bindings& bindings) const
{
	return atom_->constainsVariableDomain(id_, variable_domain, bindings);
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
	struct timeval start_time_tim_translation;
	gettimeofday(&start_time_tim_translation, NULL);
	
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
	struct timeval end_time_tim_translation;
	gettimeofday(&end_time_tim_translation, NULL);
	
	double time_spend = end_time_tim_translation.tv_sec - start_time_tim_translation.tv_sec + (end_time_tim_translation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "TIM transation took: " << time_spend << " seconds" << std::endl;

	struct timeval start_time_apply_rules;
	gettimeofday(&start_time_apply_rules, NULL);
	
	createPointToPointTransitions();
	
	struct timeval end_time_apply_rules;
	gettimeofday(&end_time_apply_rules, NULL);
	
	time_spend = end_time_apply_rules.tv_sec - start_time_apply_rules.tv_sec + (end_time_apply_rules.tv_usec - start_time_apply_rules.tv_usec) / 1000000.0;
	std::cerr << "Creating point to point transitions took: " << time_spend << " seconds" << std::endl;
	
	struct timeval start_time_unsupported_predicates;
	gettimeofday(&start_time_unsupported_predicates, NULL);

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
		DomainTransitionGraph* new_dtg = new DomainTransitionGraph(*this, *type_manager_, *action_manager_, *predicate_manager_, bindings, *initial_facts_);
//		unsupported_predicates_dtg.insert(new_dtg);
		std::vector<std::pair<const Predicate*, unsigned int> >* predicates_to_add = new std::vector<std::pair<const Predicate*, unsigned int> >();
		predicates_to_add->push_back(std::make_pair(predicate, NO_INVARIABLE_INDEX));
		
		DomainTransitionGraphNode* possitive_new_dtg_node = new DomainTransitionGraphNode(*new_dtg, NO_INVARIABLE_INDEX, !predicate->isStatic());
		
		StepID possitive_atom_id = new_dtg->getBindings().createVariableDomains(*possitive_atom);
		
		/// TEST
		PropertySpace* property_space = new PropertySpace();
		PropertyState* property_state = new PropertyState(*property_space, *predicates_to_add);
		possitive_new_dtg_node->addAtom(new BoundedAtom(possitive_atom_id, *possitive_atom, property_state->getProperties()), NO_INVARIABLE_INDEX);
		
		new_dtg->addNode(*possitive_new_dtg_node);

		addManagableObject(new_dtg);
		
		// 2) The predicate is not static.
		if (!predicate->isStatic())
		{
			// Add all preconditions which share a term with the unsupported predicate.
			DomainTransitionGraphNode* negative_new_dtg_node = new DomainTransitionGraphNode(*new_dtg, NO_INVARIABLE_INDEX, true);
			Atom* negative_atom = new Atom(*predicate, possitive_atom->getTerms(), true);
			StepID negative_atom_id = new_dtg->getBindings().createVariableDomains(*possitive_atom);
			BoundedAtom* bounded_negative_atom = new BoundedAtom(negative_atom_id, *negative_atom, property_state->getProperties());
			
			negative_new_dtg_node->addAtom(bounded_negative_atom, NO_INVARIABLE_INDEX);
			new_dtg->addNode(*negative_new_dtg_node);
			
			for (std::vector<const Term*>::const_iterator ci = negative_atom->getTerms().begin(); ci != negative_atom->getTerms().end(); ci++)
			{
				const Term* from_node_term = *ci;
				const Term* to_node_term = possitive_atom->getTerms()[std::distance(negative_atom->getTerms().begin(), ci)];
				
				from_node_term->unify(negative_atom_id, *to_node_term, possitive_atom_id, new_dtg->getBindings());
			}
			
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Simple DTG : " << *new_dtg << std::endl;
#endif
			
			// Find all transitions which can make this predicate true and false and add them as transitions.
			std::vector<std::pair<const Action*, const Atom*> > achievers;
			action_manager_->getAchievingActions(achievers, *possitive_atom);
			
			for (std::vector<std::pair<const Action*, const Atom*> >::const_iterator ci = achievers.begin(); ci != achievers.end(); ci++)
			{
				const Action* achieving_action = (*ci).first;
				
				// Create a transition between the two nodes.
				const Transition* transition = Transition::createTransition(*achieving_action, *negative_new_dtg_node, *possitive_new_dtg_node, *initial_facts_);
				
				assert (transition != NULL);
				
				if (transition != NULL)
				{
					
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
								
								for (std::vector<BoundedAtom*>::const_iterator ci = negative_new_dtg_node->getAtoms().begin(); ci != negative_new_dtg_node->getAtoms().end(); ci++)
								{
									const BoundedAtom* from_node_atom = *ci;
									
									for (std::vector<const Term*>::const_iterator ci = from_node_atom->getAtom().getTerms().begin(); ci != from_node_atom->getAtom().getTerms().end(); ci++)
									{
										const Term* from_node_atom_term = *ci;

										if (precondition_term->isTheSameAs(transition->getStep()->getStepId(), *from_node_atom_term, from_node_atom->getId(), new_dtg->getBindings()))
										{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
											std::cout << "Add the precondition: ";
											precondition->print(std::cout, new_dtg->getBindings(), transition->getStep()->getStepId());
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
												precondition->print(std::cout, bindings, transition->getStep()->getStepId());
												std::cout << "." << std::endl;
#endif
												PropertySpace* p_space = new PropertySpace();
												
												std::vector<std::pair<const Predicate*, InvariableIndex> >* predicates = new std::vector<std::pair<const Predicate*, InvariableIndex> >();
												predicates->push_back(std::make_pair(&precondition->getPredicate(), NO_INVARIABLE_INDEX));
												PropertyState* p_state = new PropertyState(*p_space, *predicates);
												properties->insert(properties->end(), p_state->getProperties().begin(), p_state->getProperties().end());
												assert (!properties->empty());
											}
											BoundedAtom* atom_to_add = new BoundedAtom(transition->getStep()->getStepId(), *precondition, *properties);
											negative_new_dtg_node->addAtom(atom_to_add, NO_INVARIABLE_INDEX);
											
											// Check if this precondition is actually removed, if not add it to the to node!
											bool is_removed = false;
											for (std::vector<const Atom*>::const_iterator ci = transition->getStep()->getAction().getEffects().begin(); ci != transition->getStep()->getAction().getEffects().end(); ci++)
											{
												const Atom* effect = *ci;
												
												if (effect->isNegative() != precondition->isNegative() &&
												    bindings.areIdentical(*effect, transition->getStep()->getStepId(), *precondition, transition->getStep()->getStepId()))
												{
													is_removed = true;
													break;
												}
											}
											
											if (!is_removed)
											{
												possitive_new_dtg_node->addAtom(atom_to_add, NO_INVARIABLE_INDEX);
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
					
					negative_new_dtg_node->addTransition(*transition, false);
				}
			}
			
			negative_new_dtg_node->removeAtom(*bounded_negative_atom);
			
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Resulting DTG: " << *new_dtg << std::endl;
#endif
		}
	}
	
	struct timeval end_time_unsupported_predicates;
	gettimeofday(&end_time_unsupported_predicates, NULL);
	
	time_spend = end_time_unsupported_predicates.tv_sec - start_time_unsupported_predicates.tv_sec + (end_time_unsupported_predicates.tv_usec - start_time_unsupported_predicates.tv_usec) / 1000000.0;
	std::cerr << "Creating DTGs for unsupported predicates: " << time_spend << " seconds" << std::endl;

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
	
	struct timeval start_time_merge_dtgs;
	gettimeofday(&start_time_merge_dtgs, NULL);
	
	Bindings* merged_dtg_bindings = new Bindings(bindings);
	DomainTransitionGraph& combined_graph = mergeIdenticalDTGs(*merged_dtg_bindings);
	
	struct timeval end_time_merge_dtgs;
	gettimeofday(&end_time_merge_dtgs, NULL);
	time_spend = end_time_merge_dtgs.tv_sec - start_time_merge_dtgs.tv_sec + (end_time_merge_dtgs.tv_usec - start_time_merge_dtgs.tv_usec) / 1000000.0;
	std::cerr << "Merge identical DTGs took: " << time_spend << " seconds" << std::endl;
	
	
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "Combined graph after merging identical DTGs." << std::endl;
	std::cout << combined_graph << std::endl;
#endif
	
	struct timeval start_time_solve_subsets;
	gettimeofday(&start_time_solve_subsets, NULL);
	
	combined_graph.solveSubsets();
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "After solving subsets:" << std::endl;
	std::cout << combined_graph << std::endl;
#endif
	
	struct timeval end_time_solve_subsets;
	gettimeofday(&end_time_solve_subsets, NULL);
	time_spend = end_time_solve_subsets.tv_sec - start_time_solve_subsets.tv_sec + (end_time_solve_subsets.tv_usec - start_time_solve_subsets.tv_usec) / 1000000.0;
	std::cerr << "Solve subsets: " << time_spend << " seconds" << std::endl;
	
	combined_graph.splitSelfReferencingNodes();
	
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "FINAL RESULTS" << std::endl;
	std::cout << combined_graph << std::endl;
#endif

	combined_graph.resolveProperties();
	
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "After resolving properties: " << std::endl;
	std::cout << combined_graph << std::endl;
#endif
/*
	std::ofstream ofs;
	ofs.open("combined_dtg.dot", std::ios::out);
	
	ofs << "digraph {" << std::endl;

	Graphviz::printToDot(ofs, combined_graph);
	
	ofs << "}" << std::endl;
	ofs.close();
*/

	struct timeval end_time_generation;
	gettimeofday(&end_time_generation, NULL);
	
	time_spend = end_time_generation.tv_sec - start_time_tim_translation.tv_sec + (end_time_generation.tv_usec - start_time_tim_translation.tv_usec) / 1000000.0;
	std::cerr << "Initialize structures: " << time_spend << " seconds" << std::endl;
	
	return combined_graph;
}

DomainTransitionGraph& DomainTransitionGraphManager::mergeIdenticalDTGs(Bindings& bindings)
{
	// Map all identical DTGs to a single DTG.
	std::map<const DomainTransitionGraphNode*, const DomainTransitionGraphNode*> mapping_old_to_new_dtg_node;
	std::map<const DomainTransitionGraphNode*, int*> map_old_facts_to_new;
	
	// Accumulate all the transitions of the identical DTGs.
	std::map<const DomainTransitionGraphNode*, std::vector<const Transition*>* > mapping_merged_transitions;
	
	std::set<const DomainTransitionGraphNode*> closed_list;
	
	std::vector<const DomainTransitionGraphNode*> unmerged_dtg_nodes;
	for (std::vector<DomainTransitionGraph*>::const_iterator objects_ci = objects_.begin(); objects_ci != objects_.end(); objects_ci++)
	{
		const DomainTransitionGraph* dtg = *objects_ci;
		
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			const DomainTransitionGraphNode* dtg_node = *ci;
			if (closed_list.count(dtg_node) != 0)
				continue;
			closed_list.insert(dtg_node);
			
			std::vector<const Transition*>* accumulated_dtgs = new std::vector<const Transition*>();
			mapping_merged_transitions[dtg_node] = accumulated_dtgs;
			mapping_old_to_new_dtg_node[dtg_node] = dtg_node;
			
			int* initial_mapping = new int[dtg_node->getAtoms().size()];
			for (unsigned int i = 0; i < dtg_node->getAtoms().size(); i++)
			{
				initial_mapping[i] = i;
			}
			
			map_old_facts_to_new[dtg_node] = initial_mapping;
			
			accumulated_dtgs->insert(accumulated_dtgs->end(), dtg_node->getTransitions().begin(), dtg_node->getTransitions().end());
			bool merged = false;
			
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
					
					merged = true;
					
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
					if (mapping_old_to_new_dtg_node.count(dtg_node2) != 0)
					{
						assert (mapping_old_to_new_dtg_node[dtg_node2] == dtg_node || mapping_old_to_new_dtg_node[dtg_node2] == dtg_node2);
						std::cout << "Overwrite: " << *dtg_node2 << " -> " << *mapping_old_to_new_dtg_node[dtg_node2] << " with "" -> " << *dtg_node << "." << std::endl;
					}
#endif
					map_old_facts_to_new[dtg_node2] = mapping;
					mapping_old_to_new_dtg_node[dtg_node2] = dtg_node;
					accumulated_dtgs->insert(accumulated_dtgs->end(), dtg_node2->getTransitions().begin(), dtg_node2->getTransitions().end());
					
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
			assert (mapping_old_to_new_dtg_node.count(dtg_node) == 1);
			for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
			{
				const Transition* transition = *ci;
				assert (mapping_old_to_new_dtg_node.count(&transition->getFromNode()) == 1);
				assert (mapping_old_to_new_dtg_node.count(&transition->getToNode()) == 1);
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
		DomainTransitionGraphNode* new_dtg_node = new DomainTransitionGraphNode(*combined_dtg, std::numeric_limits< unsigned int >::max(), dtg_node->isAttributeSpace());
		new_dtg_node->copyAtoms(*dtg_node);
		
		combined_dtg->addNode(*new_dtg_node);
		org_node_to_combined_node[dtg_node] = new_dtg_node;
	}
	
	closed_list.clear();
	
	/**
	 * For the nodes which have been merged the following steps need to be taken:
	 * - Create a new DTG node for every unique DTG node and add it to the new DTG graph.
	 * - Given a set X of identical DTG nodes, merge the properties of each of the facts.
	 * The latter is needed because the transitions between the DTG nodes may cut accross
	 * different property spaces. If the properties are not merged we will not be able to
	 * create these transitions.
	 */
	for (std::map<const DomainTransitionGraphNode*, const DomainTransitionGraphNode*>::const_iterator ci = mapping_old_to_new_dtg_node.begin(); ci != mapping_old_to_new_dtg_node.end(); ci++)
	{
		const DomainTransitionGraphNode* identical_dtg_node = (*ci).first;
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
			combined_dtg_node = new DomainTransitionGraphNode(*combined_dtg, std::numeric_limits< unsigned int >::max(), hub_dtg_node->isAttributeSpace());
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
		
		// Merge the properties of all the facts.
//		std::cout << "Merge the properties of all facts: " << *identical_dtg_node << " - combine it with:" << *combined_dtg_node << "." << std::endl;
		
		// Make sure the invariable references by the properties match up.
		std::set<const std::vector<const Object*>* > possible_matching_invariables;
		
		// Initialise it so all term domains are condidates.
		for (std::vector<BoundedAtom*>::const_iterator ci = combined_dtg_node->getAtoms().begin(); ci != combined_dtg_node->getAtoms().end(); ci++)
		{
			BoundedAtom* combined_atom = *ci;
			for (std::vector<const Term*>::const_iterator ci = combined_atom->getAtom().getTerms().begin(); ci != combined_atom->getAtom().getTerms().end(); ci++)
			{
				const Term* term = *ci;
				const std::vector<const Object*>& domain = term->getDomain(combined_atom->getId(), combined_dtg->getBindings());
				possible_matching_invariables.insert(&domain);
			}
		}
		
		for (std::vector<BoundedAtom*>::const_iterator ci = identical_dtg_node->getAtoms().begin(); ci != identical_dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
//			bool found_equivalent = false;
			
			if (bounded_atom->getProperties().empty()) continue;
			
			std::vector<const std::vector<const Object*>* > possible_domains;
			
			for (std::vector<BoundedAtom*>::const_iterator ci = combined_dtg_node->getAtoms().begin(); ci != combined_dtg_node->getAtoms().end(); ci++)
			{
				BoundedAtom* combined_atom = *ci;
				
				if (combined_dtg_node->getDTG().getBindings().areEquivalent(combined_atom->getAtom(), combined_atom->getId(), bounded_atom->getAtom(), bounded_atom->getId(), &identical_dtg_node->getDTG().getBindings()))
				{
//					found_equivalent = true;
					for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
					{
						const Property* property = *ci;
						if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
						
						possible_domains.push_back(&combined_atom->getAtom().getTerms()[property->getIndex()]->getDomain(combined_atom->getId(), combined_dtg->getBindings()));
					}
				}
			}
			
			// Remove all terms which cannot be the invariable.
			std::vector<const std::vector<const Object*>*> to_remove;
			for (std::set<const std::vector<const Object*>* >::reverse_iterator ri = possible_matching_invariables.rbegin(); ri != possible_matching_invariables.rend(); ri++)
			{
				const std::vector<const Object*>* invariable = *ri;
				bool present = false;
				for (std::vector<const std::vector<const Object*>* >::const_iterator ci = possible_domains.begin(); ci != possible_domains.end(); ci++)
				{
					const std::vector<const Object*>* domain = *ci;
					if (domain == invariable)
					{
						present = true;
						break;
					}
				}
				
				if (!present)
				{
					to_remove.push_back(invariable);
				}
			}
			
			for (std::vector<const std::vector<const Object*>*>::const_iterator ci = to_remove.begin(); ci != to_remove.end(); ci++)
			{
				possible_matching_invariables.erase(*ci);
			}
		}
		
		// If no domains are left these nodes cannot be combined!
		if (possible_matching_invariables.empty())
		{
//			std::cout << "Could not find a possible matching invariant - aborting!" << std::endl;
			continue;
		}
		
		for (std::vector<BoundedAtom*>::const_iterator ci = identical_dtg_node->getAtoms().begin(); ci != identical_dtg_node->getAtoms().end(); ci++)
		{
			const BoundedAtom* bounded_atom = *ci;
			bool found_equivalent = false;
			
			for (std::vector<BoundedAtom*>::const_iterator ci = combined_dtg_node->getAtoms().begin(); ci != combined_dtg_node->getAtoms().end(); ci++)
			{
				BoundedAtom* combined_atom = *ci;
				
				if (combined_dtg_node->getDTG().getBindings().areEquivalent(combined_atom->getAtom(), combined_atom->getId(), bounded_atom->getAtom(), bounded_atom->getId(), &identical_dtg_node->getDTG().getBindings()))
				{
					found_equivalent = true;
					for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
					{
						const Property* property = *ci;
						
						if (property->getIndex() != NO_INVARIABLE_INDEX)
						{
							const std::vector<const Object*>& domain = combined_atom->getAtom().getTerms()[property->getIndex()]->getDomain(combined_atom->getId(), combined_dtg->getBindings());
							if (possible_matching_invariables.count(&domain) != 0)
							{
								combined_atom->addProperty(**ci);
							}
//							else
//							{
//								std::cout << "Although the atoms were equivalent, the (invariable) terms could not be combined!" << std::endl;
//							}
						}
						else
						{
							combined_atom->addProperty(**ci);
						}
					}
				}
			}
			
			if (!found_equivalent)
			{
				std::cout << "Could not find an equivalent node for: ";
				bounded_atom->print(std::cout, combined_dtg_node->getDTG().getBindings());
				std::cout << std::endl;
				assert (false);
			}
			
		}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << "Result of merging / creating: " << *combined_dtg_node << std::endl;
#endif
	}
	
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << "Combined DTG: " << *combined_dtg << "." << std::endl;
#endif
	
	// Reconnect all the DTG nodes by copying the transitions.
	for (std::map<const DomainTransitionGraphNode*, std::vector<const Transition*>* >::const_iterator ci = mapping_merged_transitions.begin(); ci != mapping_merged_transitions.end(); ci++)
	{
		const DomainTransitionGraphNode* fake_org_from_dtg_node = (*ci).first;
		const std::vector<const Transition*>* org_transition = (*ci).second;
		
		DomainTransitionGraphNode* merged_from_dtg_node = org_node_to_combined_node[fake_org_from_dtg_node];
		assert (merged_from_dtg_node != NULL);
		
		for (std::vector<const Transition*>::const_iterator ci = org_transition->begin(); ci != org_transition->end(); ci++)
		{
			const Transition* org_transition = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Process the transition: " << *org_transition << std::endl;
#endif

			const DomainTransitionGraphNode& org_to_dtg_node = org_transition->getToNode();
			
			assert (mapping_old_to_new_dtg_node.count(&org_to_dtg_node) != 0);
			
			const DomainTransitionGraphNode* org_merged_to_dtg_node = mapping_old_to_new_dtg_node[&org_to_dtg_node];
			assert (org_merged_to_dtg_node != NULL);
			
			DomainTransitionGraphNode* merged_to_dtg_node = org_node_to_combined_node[org_merged_to_dtg_node];
			assert (merged_to_dtg_node != NULL);
			
			/**
			 * Make sure the transition doesn't already exist.
			 */
			bool transitionAlreadyExists = false;
			for (std::vector<const Transition*>::const_iterator ci = merged_from_dtg_node->getTransitions().begin(); ci != merged_from_dtg_node->getTransitions().end(); ci++)
			{
				const Transition* existing_transition = *ci;
				if (&org_transition->getStep()->getAction() == &existing_transition->getStep()->getAction() &&
				    &existing_transition->getToNode() == merged_to_dtg_node) {
					transitionAlreadyExists = true;
					break;
				}
			}
			
			if (transitionAlreadyExists) continue;

			const DomainTransitionGraphNode& org_from_dtg_node = org_transition->getFromNode();
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Create a transition from: " << *merged_from_dtg_node << " to " << *merged_to_dtg_node << "." << std::endl;
			std::cout << "Original transition: " << org_from_dtg_node << " to " << org_to_dtg_node << std::endl;
#endif

			// Make sure that if in the previous transition two terms were equal they still are!
			const Bindings& org_bindings = org_from_dtg_node.getDTG().getBindings();
			const std::vector<const Object*>** from_variable_domains[org_from_dtg_node.getAtoms().size()];
			
			for (std::vector<BoundedAtom*>::const_iterator ci = org_from_dtg_node.getAtoms().begin(); ci != org_from_dtg_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* org_from_fact = *ci;

				unsigned int index = NO_INVARIABLE_INDEX;
				for (std::vector<BoundedAtom*>::const_iterator ci = merged_from_dtg_node->getAtoms().begin(); ci != merged_from_dtg_node->getAtoms().end(); ci++)
				{
					const BoundedAtom* merged_from_fact = *ci;
					if (org_from_fact->shareSameProperties(*merged_from_fact) && org_from_fact->canUnifyWith(*merged_from_fact, bindings))
					{
						index = std::distance(merged_from_dtg_node->getAtoms().begin(), ci);
					}
				}
				
				assert (index != NO_INVARIABLE_INDEX);
				
				from_variable_domains[index] = new const std::vector<const Object*>*[org_from_fact->getAtom().getArity()];
				
				for (unsigned int i = 0; i < org_from_fact->getAtom().getArity(); i++)
				{
					from_variable_domains[index][i] = &org_from_fact->getVariableDomain(i, org_bindings);
				}
			}
				
			const std::vector<const Object*>** to_variable_domains[org_to_dtg_node.getAtoms().size()];
			for (std::vector<BoundedAtom*>::const_iterator ci = org_to_dtg_node.getAtoms().begin(); ci != org_to_dtg_node.getAtoms().end(); ci++)
			{
				const BoundedAtom* org_to_fact = *ci;

				unsigned int index = NO_INVARIABLE_INDEX;
				for (std::vector<BoundedAtom*>::const_iterator ci = merged_to_dtg_node->getAtoms().begin(); ci != merged_to_dtg_node->getAtoms().end(); ci++)
				{
					const BoundedAtom* merged_to_fact = *ci;
					if (org_to_fact->shareSameProperties(*merged_to_fact) && org_to_fact->canUnifyWith(*merged_to_fact, bindings))
					{
						index = std::distance(merged_to_dtg_node->getAtoms().begin(), ci);
					}
				}
				
				if (index == NO_INVARIABLE_INDEX)
				{
					std::cout << "Could not find the equivalent merged fact of: ";
					org_to_fact->print(std::cout, bindings);
					std::cout << "." << std::endl;
					
					for (std::vector<BoundedAtom*>::const_iterator ci = merged_to_dtg_node->getAtoms().begin(); ci != merged_to_dtg_node->getAtoms().end(); ci++)
					{
						std::cout << "OPT: ";
						const BoundedAtom* merged_to_fact = *ci;
						merged_to_fact->print(std::cout, bindings);
						std::cout << "." << std::endl;
					}
					assert (false);
				}
				
				to_variable_domains[index] = new const std::vector<const Object*>*[org_to_fact->getAtom().getArity()];
				
				for (unsigned int i = 0; i < org_to_fact->getAtom().getArity(); i++)
				{
					to_variable_domains[index][i] = &org_to_fact->getVariableDomain(i, org_bindings);
				}
			}
			
			Bindings& merged_bindings = merged_from_dtg_node->getDTG().getBindings();
			for (unsigned int i = 0; i < org_from_dtg_node.getAtoms().size(); i++)
			{
				const BoundedAtom* org_from_fact = org_from_dtg_node.getAtoms()[i];
				for (unsigned int j = 0; j < org_from_fact->getAtom().getArity(); j++)
				{
					for (unsigned int k = 0; k < org_to_dtg_node.getAtoms().size(); k++)
					{
						const BoundedAtom* org_to_fact = org_to_dtg_node.getAtoms()[k];
						for (unsigned int l = 0; l < org_to_fact->getAtom().getArity(); l++)
						{
							if (from_variable_domains[i][j] == to_variable_domains[k][l])
							{
								merged_from_dtg_node->getAtoms()[i]->getAtom().getTerms()[j]->unify(merged_from_dtg_node->getAtoms()[i]->getId(), *merged_to_dtg_node->getAtoms()[k]->getAtom().getTerms()[l], merged_to_dtg_node->getAtoms()[k]->getId(), merged_bindings);
							}
						}
					}
				}
			}

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "MERGE TRANS: Create a transition from: ";
			merged_from_dtg_node->print(std::cout);
			std::cout << " to ";
			merged_to_dtg_node->print(std::cout);
			std::cout << "." << std::endl;
#endif
			
			const Transition* new_transition = Transition::createTransition(org_transition->getStep()->getAction(), *merged_from_dtg_node, *merged_to_dtg_node, *initial_facts_);
			if (new_transition == NULL) {
				continue;
			}
			
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
			std::cout << "Result: " << *new_transition << "." << std::endl;
#endif
			
			merged_from_dtg_node->addTransition(*new_transition, false);
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

void DomainTransitionGraphManager::createPointToPointTransitions()
{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
	std::cout << " *************** [DomainTransitionGraphManager::createPointToPointTransitions] *******************" << std::endl;
#endif

	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
//		std::cout << "[DomainTransitionGraphManager::createPointToPointTransitions] Check DTG: " << *dtg << std::endl;
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
				DomainTransitionGraphNode* from_dtg_node_clone = new DomainTransitionGraphNode(*dtg_node, false, false);
				DomainTransitionGraphNode* to_dtg_node_clone = new DomainTransitionGraphNode(org_transition->getToNode(), false, false);
				
				Transition* transition = Transition::createTransition(org_transition->getStep()->getAction(), *from_dtg_node_clone, *to_dtg_node_clone, *initial_facts_);
				
				assert (transition != NULL);

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "[DomainTransitionGraphManager::createPointToPointTransitions] Original transition: " << *org_transition << std::endl;
				std::cout << "[DomainTransitionGraphManager::createPointToPointTransitions] Process the transition: " << *transition << std::endl;
#endif

				// Find out the invariable for this transition.
				const Term* invariable_term = NULL;
				for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator ci = transition->getPreconditions().begin(); ci != transition->getPreconditions().end(); ci++)
				{
					InvariableIndex invariable_index = (*ci).second;
					if (invariable_index == NO_INVARIABLE_INDEX)
					{
						continue;
					}
					
					const Atom* precondition = (*ci).first;
					
					if (invariable_term == NULL)
					{
						invariable_term = precondition->getTerms()[invariable_index];
					}
					else
					{
						assert (invariable_term == precondition->getTerms()[invariable_index]);
					}
				}

				assert (invariable_term != NULL);

				// All new atoms which need to be added to the from node.
				std::vector<std::pair<BoundedAtom*, InvariableIndex> > atoms_to_add_to_from_node;
				
				// Some preconditions also need to be added to the to node - converted into a bounded node.
				std::vector<std::pair<BoundedAtom*, InvariableIndex> > preconditions_to_add_to_to_node;
				
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
					 * Ground from_{term}             if precondition_{term} is 'unballanced'
					 * Add precondition to from       otherwise
					 *
					 * A predicate's term is unballanced if it does not occur in any DTG node with the term being the invariable. 
					 * Another way of putting it is saying that the predicate - given the term as index - is an attribute in 
					 * TIM terms.
					 *
					 * In addition if this term is shared between a node of the from node and a term of the to node and it 
					 * is unballanced in the context of the fact it appears in in the to node, it also needs to be grounded.
					 */
					const std::vector<std::pair<const Atom*, InvariableIndex> >& preconditions = transition->getAllPreconditions();
					
					for (std::vector<std::pair<const Atom*, InvariableIndex> >::const_iterator precondition_ci = preconditions.begin(); precondition_ci != preconditions.end(); precondition_ci++)
					{
						const Atom* precondition = (*precondition_ci).first;
						InvariableIndex precondition_invariable_index = (*precondition_ci).second;

#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
						std::cout << "Process the precondition: ";
						precondition->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
						std::cout << "." << std::endl;
#endif

						// Ignore those which are already part of the DTG node.
						const BoundedAtom* identical_bounded_atom = NULL;
						for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node_clone->getAtoms().begin(); ci != from_dtg_node_clone->getAtoms().end(); ci++)
						{
							const BoundedAtom* bounded_atom = *ci;
							if (dtg->getBindings().areIdentical(bounded_atom->getAtom(), bounded_atom->getId(), *precondition, transition->getStep()->getStepId()))
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
							if (!precondition->getPredicate().isStatic() && !transition->isPreconditionRemoved(*precondition, dtg->getBindings()))
							{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
								std::cout << "Add the predicate to the to node!" << std::endl;
#endif
								BoundedAtom* bounded_precondition = new BoundedAtom(transition->getStep()->getStepId(), *precondition, identical_bounded_atom->getProperties());
								preconditions_to_add_to_to_node.push_back(std::make_pair(bounded_precondition, precondition_invariable_index));
							}
							continue;
						}
						
						/**
						 * Check all pairwise terms of the precondition and all the facts in the from node. If the terms are the same three things
						 * can happen:
						 * 1) The precondition is added to the from node:
						 * - If the term is the invariable and the invariable occurs in the precondition it needs to be added.
						 * - If the term is an invariable in a separate DTG it needs to be added too. (*)
						 * - If the term is part of the to node and is invariable, it needs to be added.
						 * 2) Ground the term:
						 * - If the term is not part of any ballanced set it will need to be grounded.
						 * - If the term is part of a ballanced set, but appears in a term in the to node where it is not ballanced.
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
							precondition_term->print(std::cout, bindings, transition->getStep()->getStepId());
							std::cout << "{" << &precondition_term->getDomain(transition->getStep()->getStepId(), bindings) << "}" << std::endl;
#endif
							
							// Check if the precondition term is ballanced. If this isn't the case than any matching term found must be grounded!
							std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_matching_nodes;
							getDTGNodes(found_matching_nodes, transition->getStep()->getStepId(), *precondition, bindings, precondition_term_index);
							
							bool precondition_is_ballanced = !found_matching_nodes.empty();
							
							// Check if we can figure out the property(ies) linked with this precondition.
							// TODO: Need to do this before runnning the reachability!
							std::vector<const Property*> property_set;
							
							// Only do this if the term of the precondition actually matches the invariable.
							if (invariable_term->isTheSameAs(transition->getStep()->getStepId(), *precondition_term, transition->getStep()->getStepId(), bindings))
							{
								std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_nodes;
								getDTGNodes(found_nodes, transition->getStep()->getStepId(), *precondition, dtg->getBindings(), precondition_term_index);
								
								for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ci++)
								{
									const std::vector<const Property*>& existing_property_set = (*ci).second->getProperties();
									
									// If any of the properties point to the invariable term, we can add it.
									for (std::vector<const Property*>::const_iterator ci = existing_property_set.begin(); ci != existing_property_set.end(); ci++)
									{
										const Property* property = *ci;
										
										bool is_present = false;
										for (std::vector<const Property*>::const_iterator ci = property_set.begin(); ci != property_set.end(); ci++)
										{
											const Property* existing_property = *ci;
											if (*property == *existing_property)
											{
												is_present = true;
												break;
											}
										}
										
										if (!is_present)
										{
											property_set.push_back(property);
										}
									}
								}
							}
							
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
							std::cout << "Found properties: ";
							for (std::vector<const Property*>::const_iterator ci = property_set.begin(); ci != property_set.end(); ci++)
							{
								const Property* shared_property = *ci;
								std::cout << *shared_property;
								
								if (ci + 1 != property_set.end())
									std::cout << ", ";
							}
							std::cout << "." << std::endl;
#endif
							std::vector<const Property*>* property_list = new std::vector<const Property*>();
							property_list->insert(property_list->end(), property_set.begin(), property_set.end());
							
							bool is_grounded = false;
							if (!precondition_is_ballanced)
							{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
								std::cout << "Is not ballanced - potentially ground!" << std::endl;
#endif
								// Ground the term if it is part of any term in the dtg_node!
								const std::vector<const Object*>& precondition_variable_domain = precondition_term->getDomain(transition->getStep()->getStepId(), bindings);
								for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node_clone->getAtoms().begin(); ci != from_dtg_node_clone->getAtoms().end(); ci++)
								{
									const BoundedAtom* bounded_atom = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
									std::cout << "contained by the from node: ";
									bounded_atom->print(std::cout, bindings);
									std::cout << "? ->";
#endif
									unsigned int invariable_index = bounded_atom->constainsVariableDomain(precondition_variable_domain, bindings);
									if (invariable_index != std::numeric_limits< unsigned int>::max())
									{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
										std::cout << "YES" << std::endl;
#endif

										// Check if the term is ballanced in the bounded_atom.
										bool is_ballanced_after_all = false;
										for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
										{
											if ((*ci)->getIndex() == invariable_index)
											{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
												std::cout << "Is invariable after all!" << std::endl;
#endif
												is_ballanced_after_all = true;
												break;
											}
										}
										
										if (is_ballanced_after_all) break;
										
										// Ground!
										is_grounded = true;
										variable_domains_to_ground.push_back(&precondition_term->getDomain(transition->getStep()->getStepId(), bindings));
									}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
									else
									{
										std::cout << "NO" << std::endl;
									}
#endif
								}
								
								for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node_clone->getAtoms().begin(); ci != to_dtg_node_clone->getAtoms().end(); ci++)
								{
									const BoundedAtom* bounded_atom = *ci;
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
									std::cout << "contained by the to node: ";
									bounded_atom->print(std::cout, bindings);
									std::cout << "? -> ";
#endif
									unsigned int invariable_index = bounded_atom->constainsVariableDomain(precondition_variable_domain, bindings);
									if (invariable_index != std::numeric_limits< unsigned int>::max())
									{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
										std::cout << "YES" << std::endl;
#endif
										// Check if the term is ballanced in the bounded_atom.
										bool is_ballanced_after_all = false;
										for (std::vector<const Property*>::const_iterator ci = bounded_atom->getProperties().begin(); ci != bounded_atom->getProperties().end(); ci++)
										{
											if ((*ci)->getIndex() == invariable_index)
											{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
												std::cout << "Is invariable after all!" << std::endl;
#endif
												is_ballanced_after_all = true;
												break;
											}
										}
										
										if (is_ballanced_after_all) break;

										// Ground!
										is_grounded = true;
										variable_domains_to_ground.push_back(&precondition_term->getDomain(transition->getStep()->getStepId(), bindings));
									}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
									else
									{
										std::cout << "NO" << std::endl;
									}
#endif
								}
							}
							
							if (!is_grounded)
							{
								
								// If the term IS ballanced, check if it matches any of the terms in the from dtg_node's facts.
								bool precondition_added = false;
								for (std::vector<BoundedAtom*>::const_iterator ci = from_dtg_node_clone->getAtoms().begin(); ci != from_dtg_node_clone->getAtoms().end(); ci++)
								{
									const BoundedAtom* bounded_atom = *ci;
									
									for( std::vector<const Term*>::const_iterator bounded_atom_ci = bounded_atom->getAtom().getTerms().begin(); bounded_atom_ci != bounded_atom->getAtom().getTerms().end(); bounded_atom_ci++)
									{
										const Term* from_term = *bounded_atom_ci;
										
										if (from_term->isTheSameAs(bounded_atom->getId(), *precondition_term, transition->getStep()->getStepId(), bindings))
										{
	#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
											std::cout << "Add the predicate to the from node!" << std::endl;
	#endif
											BoundedAtom* bounded_precondition = new BoundedAtom(transition->getStep()->getStepId(), *precondition, *property_list);
											atoms_to_add_to_from_node.push_back(std::make_pair(bounded_precondition, precondition_invariable_index));
											precondition_added = true;
											finished = false;
											break;
										}
									}
									
									if (precondition_added) break;
								}
							}
							
							/**
							 * If the term is not removed by the effects of the action and it is balanced, we must add it to the to node.
							 */
							if (!transition->isPreconditionRemoved(*precondition, bindings))
							{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
								std::cout << "Add the predicate to the to node!" << std::endl;
#endif
								BoundedAtom* bounded_precondition = new BoundedAtom(transition->getStep()->getStepId(), *precondition, *property_list);
								preconditions_to_add_to_to_node.push_back(std::make_pair(bounded_precondition, precondition_invariable_index));
							}
							else
							{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
								std::cout << "Do not add the predicate to the to node!" << std::endl;
#endif
							}
						}
					}
					
					for (std::vector<std::pair<BoundedAtom*, InvariableIndex> >::const_iterator ci = atoms_to_add_to_from_node.begin(); ci != atoms_to_add_to_from_node.end(); ci++)
					{
						from_dtg_node_clone->addAtom((*ci).first, (*ci).second);
					}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT					
					if (!atoms_to_add_to_from_node.empty())
					{
						std::cout << "From DTG node after adding atoms: " << *from_dtg_node_clone << "." << std::endl;
					}
#endif
					atoms_to_add_to_from_node.clear();
					
					
					addFactsToNode(preconditions_to_add_to_to_node, *to_dtg_node_clone);
					preconditions_to_add_to_to_node.clear();
					
					/**
					 * In addition add all the effects which are added and refer to an invariable in the to node.
					 */
//					std::cout << "Add the effects!" << std::endl;
					const std::vector<const Atom*>& effects = transition->getStep()->getAction().getEffects();
					std::vector<std::pair<BoundedAtom*, InvariableIndex> > bounded_effects;
					
					for (std::vector<const Atom*>::const_iterator ci = effects.begin(); ci != effects.end(); ci++)
					{
						const Atom* effect = *ci;
						if (effect->isNegative()) continue;
						
						InvariableIndex invariable_index = NO_INVARIABLE_INDEX;
						
//						std::cout << "Process the effect: ";
//						effect->print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
//						std::cout << std::endl;
						
						std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_nodes;
						getDTGNodes(found_nodes, transition->getStep()->getStepId(), *effect, dtg->getBindings());
						
						std::vector<const Property*>* possible_properties = new std::vector<const Property*>();
						for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ci++)
						{
							const BoundedAtom* matching_bounded_atom = (*ci).second;
							
							for (std::vector<const Property*>::const_iterator ci = matching_bounded_atom->getProperties().begin(); ci != matching_bounded_atom->getProperties().end(); ci++)
							{
								const Property* property_to_add = *ci;
								if (std::find(possible_properties->begin(), possible_properties->end(), property_to_add) != possible_properties->end()) continue;
								
//								std::cout << "Possible property: " << *property_to_add << "." << std::endl;
								
								possible_properties->push_back(property_to_add);
							}
						}
						BoundedAtom* bounded_effect = new BoundedAtom(transition->getStep()->getStepId(), *effect, *possible_properties);
						bounded_effects.push_back(std::make_pair(bounded_effect, invariable_index));
					}
					
					addFactsToNode(bounded_effects, *to_dtg_node_clone);
//					std::cout << "[END] Add the effects!" << std::endl;
				}
				
				/**
				 * If a term is shared between the from and to node and it is not ballanced, it needs to be grounded too!
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
						
						const std::vector<const Object*>& imballanced_variable_domain = from_bounded_atom->getVariableDomain(i, from_dtg_node_clone->getDTG().getBindings());
						
						for (std::vector<BoundedAtom*>::const_iterator ci = to_dtg_node_clone->getAtoms().begin(); ci != to_dtg_node_clone->getAtoms().end(); ci++)
						{
							const BoundedAtom* to_bounded_atom = *ci;
							if (to_bounded_atom->constainsVariableDomain(imballanced_variable_domain, to_dtg_node_clone->getDTG().getBindings()) != std::numeric_limits< unsigned int>::max() &&
							    !from_bounded_atom->isIdenticalTo(*to_bounded_atom, to_dtg_node_clone->getDTG().getBindings()))
							{
								variable_domains_to_ground.push_back(&imballanced_variable_domain);
								break;
							}
						}
					}
				}

				/**
				 * Ground all the terms which need to be grounded and add the result to the final DTG.
				 */
				std::vector<DomainTransitionGraphNode*> from_grounded_nodes;
				bool grounded_from_nodes = from_dtg_node_clone->groundTerms(from_grounded_nodes, variable_domains_to_ground);
				if (grounded_from_nodes)
				{
					from_dtg_node_clone->removeTransitions(true);
					dtg_nodes_to_remove.push_back(dtg_node);
				}
				
				std::vector<DomainTransitionGraphNode*> to_grounded_nodes;
				bool grounded_to_nodes = to_dtg_node_clone->groundTerms(to_grounded_nodes, variable_domains_to_ground);
				if (grounded_to_nodes)
				{
					to_dtg_node_clone->removeTransitions(true);
					dtg_nodes_to_remove.push_back(&transition->getToNode());
				}
				
				for (std::vector<const std::vector<const Object*>* >::const_iterator ci = variable_domains_to_ground.begin(); ci != variable_domains_to_ground.end(); ci++)
				{
					grounded_objects_.insert((*ci)->begin(), (*ci)->end());
				}

				if (grounded_from_nodes || grounded_to_nodes)
				{
					for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = from_grounded_nodes.begin(); ci != from_grounded_nodes.end(); ci++)
					{
						
						DomainTransitionGraphNode* from_dtg_node = NULL;
						
						if (grounded_from_nodes)
						{
							from_dtg_node = *ci;
						}
						else
						{
							from_dtg_node = new DomainTransitionGraphNode(**ci, false, false);
						}
						
						for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = to_grounded_nodes.begin(); ci != to_grounded_nodes.end(); ci++)
						{
							DomainTransitionGraphNode* to_dtg_node = NULL;
							
							if (grounded_to_nodes)
							{
								to_dtg_node = *ci;
							}
							else
							{
								to_dtg_node = new DomainTransitionGraphNode(**ci, false, false);
							}
							
							// Try to establish the original transitions.
							// TODO: WAY TO SLOWWW!!! - called too often!
							const Transition* new_transition = transition->migrateTransition(*initial_facts_, *from_dtg_node, *to_dtg_node);
							
							if (new_transition == NULL)
							{
								continue;
							}
							from_dtg_node->addTransition(*new_transition, false);
								
							dtg_nodes_to_add.push_back(to_dtg_node);
						}
	#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
						std::cout << " NEW: " << *from_dtg_node << std::endl;
	#endif
						dtg_nodes_to_add.push_back(from_dtg_node);
					}
				}
				else
				{
					from_dtg_node_clone->addTransition(*transition, false);
					dtg_nodes_to_add.push_back(from_dtg_node_clone);
					dtg_nodes_to_add.push_back(to_dtg_node_clone);
				}
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
				std::cout << "ORG:" << *from_dtg_node_clone << std::endl;
				std::cout << " -=- ";
				transition->getStep()->getAction().print(std::cout, dtg->getBindings(), transition->getStep()->getStepId());
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
			assert (dtg->addNode(**ci));
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
	unsigned int nr_transitions = 0;
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		for (std::vector<DomainTransitionGraphNode*>::const_iterator ci = dtg->getNodes().begin(); ci != dtg->getNodes().end(); ci++)
		{
			const DomainTransitionGraphNode* dtg_node = *ci;
			for (std::vector<const Transition*>::const_iterator ci = dtg_node->getTransitions().begin(); ci != dtg_node->getTransitions().end(); ci++)
			{
				++nr_transitions;
			}
		}
	}
	
	std::cerr << "Point to point transitions: " << nr_transitions << "." << std::endl;
}

void DomainTransitionGraphManager::addFactsToNode(const std::vector<std::pair<BoundedAtom*, InvariableIndex> >& facts_to_add, DomainTransitionGraphNode& dtg_node)
{
	bool precondition_added = true;
	bool facts_processed[facts_to_add.size()];
	
//	std::cout << "Add the following facts:" << std::endl;
	
	for (std::vector<std::pair<BoundedAtom*, InvariableIndex> >::const_iterator ci = facts_to_add.begin(); ci != facts_to_add.end(); ci++)
	{
		const BoundedAtom* bounded_atom = (*ci).first;
		unsigned int index = std::distance(facts_to_add.begin(), ci);
		
		facts_processed[index] = dtg_node.containsExactCopyOf(*bounded_atom);
		
//		std::cout << "- ";
//		bounded_atom->print(std::cout, dtg_node.getDTG().getBindings());
//		std::cout << "." << std::endl;
	}
	
//	std::cout << " to: ";
//	dtg_node.print(std::cout);
//	std::cout << std::endl;
	
	bool done_map[facts_to_add.size()];
	memset(&done_map[0], true, sizeof(bool) * facts_to_add.size());
	while (precondition_added && memcmp(&facts_processed[0], &done_map[0], facts_to_add.size()) != 0)
	{
		precondition_added = false;
		for (std::vector<std::pair<BoundedAtom*, InvariableIndex> >::const_iterator ci = facts_to_add.begin(); ci != facts_to_add.end(); ci++)
		{
			BoundedAtom* atom_to_add = (*ci).first;
			InvariableIndex invariable_index = (*ci).second;
			
			unsigned int index = std::distance(facts_to_add.begin(), ci);
			if (facts_processed[index]) continue;
			
			/**
			 * Static preconditions do not have properties attached to them because they are not part of a property space.
			 * Check all the tmers of the precondition and add the precondition is any of them matches an invariable term
			 * which is already part of the to node.
			 */
			if (atom_to_add->getAtom().getPredicate().isStatic())
			{
				bool is_added = false;
				for (std::vector<const Term*>::const_iterator ci = atom_to_add->getAtom().getTerms().begin(); ci != atom_to_add->getAtom().getTerms().end(); ci++)
				{
					const Term* precondition_term = *ci;
					
					for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node.getAtoms().begin(); ci != dtg_node.getAtoms().end(); ci++)
					{
						const BoundedAtom* to_fact = *ci;
						for (std::vector<const Property*>::const_iterator ci = to_fact->getProperties().begin(); ci != to_fact->getProperties().end(); ci++)
						{
							const Property* to_fact_property = *ci;
							
							if (to_fact_property->getIndex() == NO_INVARIABLE_INDEX) continue;

							if (to_fact->getAtom().getTerms()[to_fact_property->getIndex()]->isTheSameAs(to_fact->getId(), *precondition_term, atom_to_add->getId(), dtg_node.getDTG().getBindings()))
							{
								dtg_node.addAtom(atom_to_add, invariable_index);
								
//								std::cout << "The fact: ";
//								atom_to_add->print(std::cout, dtg_node.getDTG().getBindings());
//								std::cout << "HAS been added!" << std::endl;
								
								facts_processed[index] = true;
								precondition_added = true;
								is_added = true;
								break;
							}
						}
						
						if (is_added) break;
					}
					
					if (is_added) break;
				}
				continue;
			}
			
//			bool added = false;
			
			// TODO: This code is now used as a substitute to figure out which predicates can be mapped to
			// which bounded atoms which is very expensive and a shit way of doing this.
			std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> > found_nodes;
			getDTGNodes(found_nodes, atom_to_add->getId(), atom_to_add->getAtom(), dtg_node.getDTG().getBindings());
			
			for (std::vector<std::pair<const DomainTransitionGraphNode*, const BoundedAtom*> >::const_iterator ci = found_nodes.begin(); ci != found_nodes.end(); ci++)
			{
				const BoundedAtom* matching_bounded_atom = (*ci).second;
				bool found_property = false;
				
				// Make sure the invariable actually is part of the to node.
				for (std::vector<const Property*>::const_iterator ci = matching_bounded_atom->getProperties().begin(); ci != matching_bounded_atom->getProperties().end(); ci++)
//				for (std::vector<const Property*>::const_iterator ci = atom_to_add->getProperties().begin(); ci != atom_to_add->getProperties().end(); ci++)
				{
					const Property* property = *ci;
					if (property->getIndex() == NO_INVARIABLE_INDEX) continue;
					
					const Term* invariable_term = atom_to_add->getAtom().getTerms()[property->getIndex()];
					const std::vector<const Object*>& invariable_domain = invariable_term->getDomain(atom_to_add->getId(), dtg_node.getDTG().getBindings());
					
					for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node.getAtoms().begin(); ci != dtg_node.getAtoms().end(); ci++)
					{
						if ((*ci)->constainsVariableDomain(invariable_domain, dtg_node.getDTG().getBindings()) != std::numeric_limits< unsigned int>::max())
						{
							dtg_node.addAtom(atom_to_add, invariable_index);
							
//							std::cout << "The fact: ";
//							atom_to_add->print(std::cout, dtg_node.getDTG().getBindings());
//							std::cout << "HAS been added!" << std::endl;
							
							facts_processed[index] = true;
							found_property = true;
							precondition_added = true;
//							added = true;
							break;
						}
					}
					
					if (found_property) break;
				}
				
				if (found_property) break;
			}

//			if (!added)
//			{
//				std::cout << "The fact: ";
//				atom_to_add->print(std::cout, dtg_node.getDTG().getBindings());
//				std::cout << " could not been added!" << std::endl;
//			}
		}
	}
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

bool DomainTransitionGraphManager::isSupported(unsigned int id, const MyPOP::Atom& atom, const MyPOP::Bindings& bindings) const
{
	for (std::vector<DomainTransitionGraph*>::const_iterator ci = objects_.begin(); ci != objects_.end(); ci++)
	{
		DomainTransitionGraph* dtg = *ci;
		if (dtg->isSupported(id, atom, bindings))
		{
			return true;
		}
	}
	return false;
}

};

void Graphviz::printToDot(std::ofstream& ofs, const SAS_Plus::Transition& transition, const Bindings& bindings)
{
	printToDot(ofs, transition.getFromNode());
	ofs << " -> ";
	printToDot(ofs, transition.getToNode());
	ofs << "[ label=\"";
	transition.getStep()->getAction().print(ofs, bindings, transition.getStep()->getStepId());
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
