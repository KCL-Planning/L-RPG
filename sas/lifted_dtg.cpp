#include "lifted_dtg.h"

#include "../VALfiles/ptree.h"
#include "../VALfiles/SASActions.h"
#include "../VALfiles/ToFunction.h"
#include "../action_manager.h"
#include "../plan_bindings.h"
#include "../formula.h"
#include "../term_manager.h"
#include "../predicate_manager.h"
#include "heuristics/fact_set.h"
#include "property_space.h"
#include <type_manager.h>
#include <parser_utils.h>

//#define MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT

namespace MyPOP
{
namespace SAS_Plus
{

MultiValuedTransition::MultiValuedTransition(const Action& action, const MultiValuedValue& precondition, const MultiValuedValue& effect, const std::vector<std::vector<unsigned int>* >& precondition_to_action_variable_mappings, const std::vector<std::vector<unsigned int>* >& effect_to_action_variable_mappings, const TypeManager& type_manager)
	: action_(&action), precondition_(&precondition), effect_(&effect), precondition_to_action_variable_mappings_(&precondition_to_action_variable_mappings), effect_to_action_variable_mappings_(&effect_to_action_variable_mappings)
{
	assert (precondition_->getValues().size() == precondition_to_action_variable_mappings_->size());
	assert (effect_->getValues().size() == effect_to_action_variable_mappings_->size());

	for (unsigned int action_variable_index = 0; action_variable_index < action.getVariables().size(); ++action_variable_index)
	{
		std::vector<const Object*> objects_in_variable_domain;
		type_manager.getObjectsOfType(objects_in_variable_domain, *action.getVariables()[action_variable_index]->getType());
		HEURISTICS::VariableDomain* new_variable_domain = new HEURISTICS::VariableDomain(objects_in_variable_domain);
		action_variable_domains_.push_back(new_variable_domain);
	}
	
	// Update the variable domains based on the preconditions and effects.
	for (unsigned int precondition_index = 0; precondition_index < precondition_to_action_variable_mappings.size(); ++precondition_index)
	{
		std::vector<unsigned int>* links_to_action_variables = precondition_to_action_variable_mappings[precondition_index];
		if (links_to_action_variables == NULL)
		{
			continue;
		}
		for (unsigned int term_index = 0; term_index < links_to_action_variables->size(); ++term_index)
		{
			const HEURISTICS::VariableDomain* precondition_variable_domain = precondition.getValues()[precondition_index]->getVariableDomains()[term_index];
			HEURISTICS::VariableDomain* action_variable_domain = action_variable_domains_[(*links_to_action_variables)[term_index]];
			
			HEURISTICS::VariableDomain updated_action_variable_domain;
			action_variable_domain->getIntersection(updated_action_variable_domain, *precondition_variable_domain);
			action_variable_domain->set(updated_action_variable_domain.getVariableDomain());
		}
	}
	
	for (unsigned int effect_index = 0; effect_index < effect_to_action_variable_mappings.size(); ++effect_index)
	{
		std::vector<unsigned int>* links_to_action_variables = effect_to_action_variable_mappings[effect_index];
		if (links_to_action_variables == NULL)
		{
			continue;
		}
		for (unsigned int term_index = 0; term_index < links_to_action_variables->size(); ++term_index)
		{
			const HEURISTICS::VariableDomain* effect_variable_domain = effect.getValues()[effect_index]->getVariableDomains()[term_index];
			HEURISTICS::VariableDomain* action_variable_domain = action_variable_domains_[(*links_to_action_variables)[term_index]];
			
			HEURISTICS::VariableDomain updated_action_variable_domain;
			action_variable_domain->getIntersection(updated_action_variable_domain, *effect_variable_domain);
			action_variable_domain->set(updated_action_variable_domain.getVariableDomain());
		}
	}
}

MultiValuedTransition::~MultiValuedTransition()
{
	for (std::vector<std::vector<unsigned int>* >::const_iterator ci = precondition_to_action_variable_mappings_->begin(); ci != precondition_to_action_variable_mappings_->end(); ++ci)
	{
		delete *ci;
	}
	
	for (std::vector<std::vector<unsigned int>* >::const_iterator ci = effect_to_action_variable_mappings_->begin(); ci != effect_to_action_variable_mappings_->end(); ++ci)
	{
		delete *ci;
	}
	
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_domains_.begin(); ci != action_variable_domains_.end(); ++ci)
	{
		delete *ci;
	}
	
	delete precondition_to_action_variable_mappings_;
	delete effect_to_action_variable_mappings_;
}

MultiValuedTransition* MultiValuedTransition::migrateTransition(const MultiValuedValue& from_node, const MultiValuedValue& to_node, const std::vector<const Atom*>& initial_facts, const TypeManager& type_manager) const
{
	std::vector<std::vector<unsigned int>* >* precondition_to_action_variable_mappings = new std::vector<std::vector<unsigned int>* >();
	std::vector<std::vector<unsigned int>* >* effect_to_action_variable_mappings = new std::vector<std::vector<unsigned int>* >();
	
	for (std::vector<std::vector<unsigned int>* >::const_iterator ci = precondition_to_action_variable_mappings_->begin(); ci != precondition_to_action_variable_mappings_->end(); ++ci)
	{
		if (*ci != NULL)
		{
			precondition_to_action_variable_mappings->push_back(new std::vector<unsigned int>(**ci));
		}
		else
		{
			precondition_to_action_variable_mappings->push_back(NULL);
		}
	}
	
	for (std::vector<std::vector<unsigned int>* >::const_iterator ci = effect_to_action_variable_mappings_->begin(); ci != effect_to_action_variable_mappings_->end(); ++ci)
	{
		if (*ci != NULL)
		{
			effect_to_action_variable_mappings->push_back(new std::vector<unsigned int>(**ci));
		}
		else
		{
			effect_to_action_variable_mappings->push_back(NULL);
		}
	}
	
	MultiValuedTransition* transition = new MultiValuedTransition(*action_, from_node, to_node, *precondition_to_action_variable_mappings, *effect_to_action_variable_mappings, type_manager);
	
	// Check that no static preconditions are violated.
	bool all_static_precondition_statisfied = true;
	std::vector<const Atom*> preconditions;
	Utility::convertFormula(preconditions, &transition->action_->getPrecondition());
	for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
	{
		const Atom* precondition = *ci;
		if (!precondition->getPredicate().isStatic())
		{
			continue;
		}
		
		std::vector<const HEURISTICS::VariableDomain*> precondition_variable_domains;
		for (std::vector<const Term*>::const_iterator ci = precondition->getTerms().begin(); ci != precondition->getTerms().end(); ++ci)
		{
			const Term* precondition_term = *ci;
			//for (std::vector<const Variable*>::const_iterator ci = transition->action_->getVariables().begin(); ci != transition->action_->getVariables().end(); ++ci)
			for (unsigned int action_variable_index = 0; action_variable_index < transition->action_->getVariables().size(); ++action_variable_index)
			{
				if (precondition_term == transition->action_->getVariables()[action_variable_index])
				{
					precondition_variable_domains.push_back(transition->action_variable_domains_[action_variable_index]);
					break;
				}
			}
		}
		
		// Check if the precondition is backed by one of the facts in the initial state.
		bool found_matching_initial_fact = false;
		for (std::vector<const Atom*>::const_iterator ci = initial_facts.begin(); ci != initial_facts.end(); ++ci)
		{
			const Atom* initial_fact = *ci;
			if (initial_fact->getArity() != precondition->getArity() ||
			    initial_fact->getPredicate().getName() != precondition->getPredicate().getName())
			{
				continue;
			}
			
			bool terms_match = true;
			for (unsigned int term_index = 0; term_index < initial_fact->getArity(); ++term_index)
			{
				if (!precondition_variable_domains[term_index]->contains(*static_cast<const Object*>(initial_fact->getTerms()[term_index])))
				{
					terms_match = false;
					break;
				}
			}
			
			if (!terms_match)
			{
				continue;
			}
			
			found_matching_initial_fact = true;
			break;
		}
		
		if (!found_matching_initial_fact)
		{
			all_static_precondition_statisfied = false;
			break;
		}
	}
	
	if (!all_static_precondition_statisfied)
	{
		delete transition;
		return NULL;
	}
	
	// Check that none of the action variables are empty.
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = transition->action_variable_domains_.begin(); ci != transition->action_variable_domains_.end(); ++ci)
	{
		if ((*ci)->getVariableDomain().empty())
		{
			delete transition;
			return NULL;
		}
	}
	return transition;
}

std::ostream& operator<<(std::ostream& os, const MultiValuedTransition& transition)
{
	os << *transition.action_ << " ";
	for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = transition.action_variable_domains_.begin(); ci != transition.action_variable_domains_.end(); ++ci)
	{
		os << **ci << " ";
	}
	os << std::endl;
	os << "Preconditions:" << std::endl;
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = transition.precondition_->getValues().begin(); ci != transition.precondition_->getValues().end(); ++ci)
	{
		unsigned int precondition_index = std::distance(transition.precondition_->getValues().begin(), ci);
		os << "* " << **ci << std::endl;
		std::vector<unsigned int>* mappings = (*transition.precondition_to_action_variable_mappings_)[precondition_index];
		if (mappings == NULL)
		{
			os << "No bindings!";
		}
		else
		{
			for (std::vector<unsigned int>::const_iterator ci = mappings->begin(); ci != mappings->end(); ++ci)
			{
				os << *ci << ", ";
			}
		}
		os << std::endl;
	}
	
	os << "Effects:" << std::endl;
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = transition.effect_->getValues().begin(); ci != transition.effect_->getValues().end(); ++ci)
	{
		unsigned int effects_index = std::distance(transition.effect_->getValues().begin(), ci);
		os << "* " << **ci << std::endl;
		std::vector<unsigned int>* mappings = (*transition.effect_to_action_variable_mappings_)[effects_index];
		if (mappings == NULL)
		{
			os << "No bindings!";
		}
		else
		{
			for (std::vector<unsigned int>::const_iterator ci = mappings->begin(); ci != mappings->end(); ++ci)
			{
				os << *ci << ", ";
			}
		}
		os << std::endl;
	}
	
	return os;
}

	
MultiValuedValue::MultiValuedValue(std::vector<HEURISTICS::Fact*>& values, const PropertyState& property_state)
	: values_(&values), property_state_(&property_state)
{

}

MultiValuedValue::MultiValuedValue(const MultiValuedValue& other)
	: property_state_(other.property_state_)
{
	values_ = new std::vector<HEURISTICS::Fact*>();
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = other.getValues().begin(); ci != other.getValues().end(); ++ci)
	{
		values_->push_back(new HEURISTICS::Fact(**ci));
	}
}
	
MultiValuedValue::~MultiValuedValue()
{
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = values_->begin(); ci != values_->end(); ++ci)
	{
		delete *ci;
	}
	delete values_;
	
		
	for (std::vector<const MultiValuedTransition*>::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ++ci)
	{
		delete *ci;
	}
}

void MultiValuedValue::addTransition(const MultiValuedTransition& transition)
{
	transitions_.push_back(&transition);
}

std::ostream& operator<<(std::ostream& os, const MultiValuedValue& value)
{
	os << " === VALUE === " << std::endl;
	for (std::vector<HEURISTICS::Fact*>::const_iterator ci = value.values_->begin(); ci != value.values_->end(); ++ci)
	{
		os << **ci << std::endl;
	}
	
	for (std::vector<const MultiValuedTransition*>::const_iterator ci = value.transitions_.begin(); ci != value.transitions_.end(); ++ci)
	{
		os << **ci << std::endl;
	}
	
	return os;
}

void LiftedDTG::getProperties(const PredicateManager& predicate_manager, std::vector<std::pair<const Predicate*, unsigned int> >& predicates, const TIM::PropertyState& property_state)
{
	for (std::multiset<TIM::Property*>::const_iterator lhs_properties_i = property_state.begin(); lhs_properties_i != property_state.end(); lhs_properties_i++)
	{
		const TIM::Property* property = *lhs_properties_i;

		const VAL::extended_pred_symbol* extended_property = property->root();
		const Predicate* predicate = predicate_manager.getGeneralPredicate(extended_property->getName());
		assert (predicate != NULL);

		// Adding the predicate to the DTG will also create a lifted DTG node with that predicate.
		// Further refinements can be made to this DTG by splitting these nodes.
		predicates.push_back(std::make_pair(predicate, property->aPosn()));
	}
}

//std::vector<LiftedDTG*> LiftedDTG::all_lifted_dtgs_;

void LiftedDTG::createLiftedDTGs(std::vector< LiftedDTG* >& created_lifted_dtgs, const VAL::pddl_type_list& types, const PredicateManager& predicate_manager, const TypeManager& type_manager, const ActionManager& action_manager, const TermManager& term_manager, const std::vector<const Atom* >& initial_facts)
{
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_KEEP_TIME
	struct timeval start_time_tim_translation;
	gettimeofday(&start_time_tim_translation, NULL);
#endif
	// Store temporary DTGs in this vector, during post processing they might get split again. Only then will we add the DTGs as a managable object (see Manager class).
	std::vector<TIM::PropertySpace*> property_spaces;
	property_spaces.insert(property_spaces.end(), TIM::TA->pbegin(), TIM::TA->pend());
	
	std::set<const Predicate*> state_valued_predicates;

	std::vector<PropertySpace*> all_property_spaces_;
	
	// Construct the DTGs by combining all properties which appear together in either the LHS or RHS of a transition rule.
	for (std::vector<TIM::PropertySpace*>::const_iterator property_space_i = property_spaces.begin(); property_space_i != property_spaces.end(); ++property_space_i)
	{
		TIM::PropertySpace* property_space = *property_space_i;
		SAS_Plus::PropertySpace& dtg_property_space = SAS_Plus::PropertySpace::createPropertySpace(term_manager, property_space->obegin(), property_space->oend());
		
		std::map<std::vector<std::pair<const Predicate*, unsigned int> >, PropertyState* > processed_expressions;

		// We need to augment some rules to get the full set of properties. If a property appears in the LHS of a rule $a$ and it is a proper subset
		// of another LHS $b$. Then add a new rule $b$ -> ($b.LHS$ \ $a.LHS$) + $a.RHS$.
		for (std::set<TIM::TransitionRule*>::const_iterator rules_i = property_space->getRules().begin(); rules_i != property_space->getRules().end(); ++rules_i)
		{
			TIM::TransitionRule* rule_a = *rules_i;
			
			// Combine the property states who appear in either the LHS of RHS of this rule.
			std::vector<std::pair<const Predicate*, unsigned int> > predicates_rule_a;
			getProperties(predicate_manager, predicates_rule_a, *rule_a->getLHS());

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
					getProperties(predicate_manager, predicates_rhs, *rule_a->getRHS());

					std::multiset<TIM::Property*> duplicates;
					std::set_intersection(rule_a->getRHS()->begin(), rule_a->getRHS()->end(), rule_b->getLHS()->begin(), rule_b->getLHS()->end(), std::inserter(duplicates, duplicates.begin()));
					
					for (std::multiset<TIM::Property*>::const_iterator ci = difference.begin(); ci != difference.end(); ci++)
					{
						TIM::Property* property = *ci;
						const VAL::extended_pred_symbol* extended_property = property->root();
						const Predicate* predicate = predicate_manager.getGeneralPredicate(extended_property->getName());
						assert (predicate != NULL);
						
						// Make sure we do not add duplicates:
						if (duplicates.count(property) != 0)
						{
							continue;
						}

						predicates_rhs.push_back(std::make_pair(predicate, property->aPosn()));
					}
					
					if (processed_expressions.count(predicates_rhs) == 0)
					{
						PropertyState* new_property_state = new PropertyState(dtg_property_space, predicates_rhs);
						dtg_property_space.addPropertyState(*new_property_state);
						processed_expressions[predicates_rhs] = new_property_state;
						
						// We no longer need to process the LHS and RHS of rule_a, since it has been substituted by this rule.
						std::vector<std::pair<const Predicate*, unsigned int> > rule_a_rhs;
						getProperties(predicate_manager, rule_a_rhs, *rule_a->getRHS());
						processed_expressions[predicates_rule_a] = new_property_state;
						processed_expressions[rule_a_rhs] = new_property_state;
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
			getProperties(predicate_manager, predicates, *rule->getLHS());
			
			if (processed_expressions.count(predicates) == 0)
			{
				// TODO: Memory leak.
				PropertyState* new_property_state = new PropertyState(dtg_property_space, predicates);
				dtg_property_space.addPropertyState(*new_property_state);
				processed_expressions[predicates] = new_property_state;
			}
			
			predicates.clear();
			getProperties(predicate_manager, predicates, *rule->getRHS());
			
			if (processed_expressions.count(predicates) == 0)
			{
				// TODO: Memory leak.
				PropertyState* new_property_state = new PropertyState(dtg_property_space, predicates);
				dtg_property_space.addPropertyState(*new_property_state);
				processed_expressions[predicates] = new_property_state;
			}
		}
		
		dtg_property_space.addTransitions(predicate_manager, type_manager, action_manager, property_space->getRules());
	
		// Check if there is another property space with the same type.
		bool is_merged = false;

		for (std::vector<PropertySpace*>::reverse_iterator ri = all_property_spaces_.rbegin(); ri != all_property_spaces_.rend(); ++ri)
		{
			PropertySpace* processed_property_space = *ri;
			PropertySpace* merged_property_space = PropertySpace::merge(dtg_property_space, *processed_property_space);
			if (merged_property_space != NULL)
			{
				is_merged = true;
				all_property_spaces_.erase(ri.base() - 1);
				all_property_spaces_.push_back(merged_property_space);
				
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
				std::cout << "Merged: " << *merged_property_space << std::endl;
#endif
				
				break;
			}
		}

		if (!is_merged)
		{
			all_property_spaces_.push_back(&dtg_property_space);
		}
	}
	
	for (std::vector<PropertySpace*>::const_iterator ci = all_property_spaces_.begin(); ci != all_property_spaces_.end(); ++ci)
	{
		LiftedDTG* new_ldtg = new LiftedDTG(predicate_manager, type_manager, **ci);
		created_lifted_dtgs.push_back(new_ldtg);
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
		std::cout << *new_ldtg << std::endl;
#endif
	}
	
	// Create the lifted DTGs for those predicates which have not been processed yet.
	for (std::vector<Predicate*>::const_iterator ci = predicate_manager.getManagableObjects().begin(); ci != predicate_manager.getManagableObjects().end(); ci++)
	{
		const Predicate* predicate = *ci;
		if (predicate->isStatic())
		{
			continue;
		}
		
		bool is_supported = false;
#ifdef MYPOP_SAS_PLUS_DTG_MANAGER_COMMENT
		std::cout << "Check if the predicate : " << *predicate << " is supported!" << std::endl;
#endif
		for (std::vector<PropertySpace*>::const_iterator ci = all_property_spaces_.begin(); ci != all_property_spaces_.end(); ++ci)
		{
			const PropertySpace* property_space = *ci;
			for (std::vector<PropertyState*>::const_iterator ci = property_space->getPropertyStates().begin(); ci != property_space->getPropertyStates().end(); ++ci)
			{
				const PropertyState* property_state = *ci;
				for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ++ci)
				{
					const Property* property = *ci;
					const Predicate& state_valued_predicate = property->getPredicate();
					if (&state_valued_predicate == predicate ||
							state_valued_predicate.canSubstitute(*predicate))
					{
						is_supported = true;
						break;
					}
				}
				if (is_supported)
				{
					break;
				}
			}
			if (is_supported)
			{
				break;
			}
		}
		
		if (is_supported) continue;
		
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
		std::cerr << "Unsupported predicate: " << *predicate << std::endl;
#endif
		
		// Create an attribute space.
		PropertySpace& attribute_space = PropertySpace::createAttributeSpace();
		
		PropertyState* property_state = new PropertyState(attribute_space);
		attribute_space.addPropertyState(*property_state);
		Property* property = new Property(*property_state, *predicate, std::numeric_limits<unsigned int>::max());
		property_state->addProperty(*property);
		
		PropertyState* empty_property_state = new PropertyState(attribute_space);
		attribute_space.addPropertyState(*empty_property_state);
		
		for (std::vector<Action*>::const_iterator ci = action_manager.getManagableObjects().begin(); ci != action_manager.getManagableObjects().end(); ++ci)
		{
			const Action* action = *ci;
			for (std::vector<const Atom*>::const_iterator ci = action->getEffects().begin(); ci != action->getEffects().end(); ++ci)
			{
				const Atom* effect = *ci;
				if (effect->isNegative())
				{
					continue;
				}
				
				if (effect->getArity() != predicate->getArity() ||
				    effect->getPredicate().getName() != predicate->getName())
				{
					continue;
				}
				
				std::vector<unsigned int>* effect_variable_mapping = new std::vector<unsigned int>();
				bool types_match = true;
				
				
				std::vector<HEURISTICS::VariableDomain*> tmp_action_variable_to_effect_mappings;
				for (std::vector<const Variable*>::const_iterator ci = action->getVariables().begin(); ci != action->getVariables().end(); ++ci)
				{
					std::vector<const Object*> variable_domain;
					type_manager.getObjectsOfType(variable_domain, *(*ci)->getType());
					tmp_action_variable_to_effect_mappings.push_back(new HEURISTICS::VariableDomain(variable_domain));
				}
				
				for (unsigned int term_index = 0; term_index < effect->getArity(); ++term_index)
				{
					const Type* effect_type = effect->getTerms()[term_index]->getType();
					const Type* predicate_type = predicate->getTypes()[term_index];
					
					if (!effect_type->isEqual(*predicate_type) && !effect_type->isSubtypeOf(*predicate_type) && !effect_type->isSupertypeOf(*predicate_type))
					{
						types_match = false;
						break;
					}
					
					// Find matching action variable and update the variable domain.
					for (unsigned int action_variable_index = 0; action_variable_index < action->getVariables().size(); ++action_variable_index)
					{
						if (action->getVariables()[action_variable_index] == effect->getTerms()[term_index])
						{
							effect_variable_mapping->push_back(action_variable_index);
							
							std::vector<const Object*> effect_objects;
							type_manager.getObjectsOfType(effect_objects, *effect->getTerms()[term_index]->getType());
							
							HEURISTICS::VariableDomain effect_variable_domain(effect_objects);
							HEURISTICS::VariableDomain intersection;
							effect_variable_domain.getIntersection(intersection, *tmp_action_variable_to_effect_mappings[action_variable_index]);
							
							tmp_action_variable_to_effect_mappings[action_variable_index]->set(intersection.getVariableDomain());
							break;
						}
					}
				}
				
				if (types_match)
				{
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
					std::cerr << action->getPredicate() << " supports " << *predicate << "." << std::endl;
					for (std::vector<unsigned int>::const_iterator ci = effect_variable_mapping->begin(); ci != effect_variable_mapping->end(); ++ci)
					{
						std::cerr << *ci << " ";
					}
					std::cerr << std::endl;
#endif
					std::map<const Property*, std::vector<unsigned int>* >* precondition_mappings = new std::map<const Property*, std::vector<unsigned int>* >();
					std::map<const Property*, std::vector<unsigned int>* >* effect_mappings = new std::map<const Property*, std::vector<unsigned int>* >();
					(*effect_mappings)[property] = effect_variable_mapping;
					std::vector<const HEURISTICS::VariableDomain*>* action_variable_to_effect_mappings = new std::vector<const HEURISTICS::VariableDomain*>();
					
					for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = tmp_action_variable_to_effect_mappings.begin(); ci != tmp_action_variable_to_effect_mappings.end(); ++ci)
					{
						action_variable_to_effect_mappings->push_back(*ci);
					}
					
					PropertyStateTransition* transition = new PropertyStateTransition(*empty_property_state, *property_state, empty_property_state->getProperties(), property_state->getProperties(), *action, *precondition_mappings, *effect_mappings, *action_variable_to_effect_mappings);
					empty_property_state->addTransition(*transition);
				}
				else
				{
					delete effect_variable_mapping;
				}
			}
		}
		
		LiftedDTG* new_lifted_dtg = new LiftedDTG(predicate_manager, type_manager, attribute_space);
		created_lifted_dtgs.push_back(new_lifted_dtg);
	}
	
	for (std::vector<LiftedDTG*>::const_iterator ci = created_lifted_dtgs.begin(); ci != created_lifted_dtgs.end(); ++ci)
	{
		(*ci)->createTransitions(created_lifted_dtgs, type_manager);
	}
	
	for (std::vector<LiftedDTG*>::const_iterator ci = created_lifted_dtgs.begin(); ci != created_lifted_dtgs.end(); ++ci)
	{
		(*ci)->ground(created_lifted_dtgs, initial_facts, term_manager, type_manager);
	}
}

LiftedDTG::LiftedDTG(const PredicateManager& predicate_manager, const TypeManager& type_manager, const SAS_Plus::PropertySpace& property_space)
	: property_space_(&property_space)
{
	for (std::vector<PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ++ci)
	{
		const PropertyState* property_state = *ci;
		std::vector<HEURISTICS::Fact*>* all_facts = new std::vector<HEURISTICS::Fact*>();
		for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ++ci)
		{
			const Property* property = *ci;
			
			std::vector<const HEURISTICS::VariableDomain*>* variable_domains = new std::vector<const HEURISTICS::VariableDomain*>();
			for (std::vector<const Type*>::const_iterator ci = property->getPredicate().getTypes().begin(); ci != property->getPredicate().getTypes().end(); ++ci)
			{
				std::vector<const Object*> objects_of_type;
				type_manager.getObjectsOfType(objects_of_type, **ci);
				
				HEURISTICS::VariableDomain* vd = new HEURISTICS::VariableDomain(objects_of_type);
				variable_domains->push_back(vd);
			}
			
			HEURISTICS::Fact* fact = new HEURISTICS::Fact(predicate_manager, property->getPredicate(), *variable_domains);
			all_facts->push_back(fact);
		}
		MultiValuedValue* mvv = new MultiValuedValue(*all_facts, *property_state);
		nodes_.push_back(mvv);
	}
}

LiftedDTG::~LiftedDTG()
{
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		delete *ci;
	}
}

void LiftedDTG::createTransitions(const std::vector<LiftedDTG*>& all_lifted_dtgs, const TypeManager& type_manager)
{
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
	std::cout << "Create transitions for " << *this << std::endl;
#endif
	// Connect the transitions.
	for (std::vector<PropertyState*>::const_iterator ci = property_space_->getPropertyStates().begin(); ci != property_space_->getPropertyStates().end(); ++ci)
	{
		const PropertyState* property_state = *ci;
		for (std::vector<const PropertyStateTransition*>::const_iterator ci = property_state->getTransitions().begin(); ci != property_state->getTransitions().end(); ++ci)
		{
			const PropertyStateTransition* transition = *ci;
			
			MultiValuedValue* from_node = getMultiValuedValue(transition->getFromPropertyState());
			MultiValuedValue* to_node = getMultiValuedValue(transition->getToPropertyState());
			
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
			std::cout << "Create a transition from " << *from_node << " to " << *to_node << std::endl;
			std::cout << "Transition: " << *transition << std::endl;
#endif
			
			//const std::map<const Property*, std::vector<unsigned int>* >& precondition_mappings_to_action_variables = transition->getMappingToActionVariables();
			const std::vector<const HEURISTICS::VariableDomain*>& action_variables = transition->getActionVariableDomains();
			
			// We map each term of each value of each precondition to the variables of the action.
			std::vector<std::vector<unsigned int>* >* precondition_to_action_variable_mappings = new std::vector<std::vector<unsigned int>* >();
			
			// We map each action variable to each term of the effect.
			std::vector<std::vector<unsigned int>* >* effects_to_action_variable_mappings = new std::vector<std::vector<unsigned int>* >();
			
			const std::vector<HEURISTICS::Fact*>& from_values = from_node->getValues();
			for (unsigned int fact_index = 0; fact_index < from_values.size(); ++fact_index)
			{
				HEURISTICS::Fact* fact = from_values[fact_index];
				const Property* property = from_node->getPropertyState().getProperties()[fact_index];
				
				const std::vector<unsigned int>* mapping_to_action_variables = transition->getMappingsOfProperty(*property, true);
				
				//if (mappings_to_action_variables.find(property) == mappings_to_action_variables.end())
				if (mapping_to_action_variables == NULL)
				{
					precondition_to_action_variable_mappings->push_back(NULL);
					continue;
				}
				//assert (mappings_to_action_variables.find(property) != mappings_to_action_variables.end());
				
				std::vector<unsigned int>* precondition_mapping = new std::vector<unsigned int>();
				precondition_to_action_variable_mappings->push_back(precondition_mapping);
				
				for (unsigned int fact_term_index = 0; fact_term_index < fact->getVariableDomains().size(); ++fact_term_index)
				{
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
					std::cout << "The " << fact_term_index << " is mapped to the " << (*mapping_to_action_variables)[fact_term_index] << "th action variable!" << std::endl;
#endif
					assert ((*mapping_to_action_variables).size() > fact_term_index);
					assert ((*mapping_to_action_variables)[fact_term_index] < action_variables.size());
					fact->setVariableDomain(fact_term_index, *action_variables[(*mapping_to_action_variables)[fact_term_index]]);
					precondition_mapping->push_back((*mapping_to_action_variables)[fact_term_index]);
				}
			}
			
			const std::vector<HEURISTICS::Fact*>& to_values = to_node->getValues();
			for (unsigned int fact_index = 0; fact_index < to_values.size(); ++fact_index)
			{
				HEURISTICS::Fact* fact = to_values[fact_index];
				const Property* property = to_node->getPropertyState().getProperties()[fact_index];
				
				const std::vector<unsigned int>* mapping_to_action_variables = transition->getMappingsOfProperty(*property, false);
				
				//if (mappings_to_action_variables.find(property) == mappings_to_action_variables.end())
				if (mapping_to_action_variables == NULL)
				{
					effects_to_action_variable_mappings->push_back(NULL);
					continue;
				}
				
				std::vector<unsigned int>* effect_to_action_variable_mappings = new std::vector<unsigned int>();
				effects_to_action_variable_mappings->push_back(effect_to_action_variable_mappings);
				
				for (unsigned int fact_term_index = 0; fact_term_index < fact->getVariableDomains().size(); ++fact_term_index)
				{
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
					std::cout << "The " << fact_term_index << " is mapped to the " << (*mapping_to_action_variables)[fact_term_index] << "th action variable! (" << action_variables.size() << ")" << transition->getAction().getVariables().size() << std::endl;
#endif
					fact->setVariableDomain(fact_term_index, *action_variables[(*mapping_to_action_variables)[fact_term_index]]);
					effect_to_action_variable_mappings->push_back((*mapping_to_action_variables)[fact_term_index]);
				}
			}
			
			MultiValuedTransition* new_transition = new MultiValuedTransition(transition->getAction(), *from_node, *to_node, *precondition_to_action_variable_mappings, *effects_to_action_variable_mappings, type_manager);
			from_node->addTransition(*new_transition);
		}
	}
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
	std::cout << *this << std::endl;
#endif
}

void LiftedDTG::ground(const std::vector<LiftedDTG*>& all_lifted_dtgs, const std::vector<const Atom*>& initial_facts, const TermManager& term_manager, const TypeManager& type_manager)
{
#ifdef MYPOP_SAS_PLUS_MULTI_VALUED_TRANSITION_COMMENT
	std::cout << "GROUND" << std::endl << *this << std::endl;
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
				const Object* o = static_cast<const Object*>(*ci);
				if (o == object)
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
						const Object* o1 = static_cast<const Object*>(static_fact->getTerms()[i]);
						const Object* o2 = static_cast<const Object*>(other_static_fact->getTerms()[i]);
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
	
	for (std::map<const Object*, std::vector<const Atom*>* >::const_iterator ci = object_to_static_constraints_mapping.begin(); ci != object_to_static_constraints_mapping.end(); ++ci)
	{
		delete (*ci).second;
	}
	
	// Break the nodes up along the equivalent object sets.
	std::map<MultiValuedValue*, const MultiValuedValue*> new_to_old_node_mapping;
	std::map<const MultiValuedValue*, std::vector<MultiValuedValue*>*> old_to_new_node_mapping;
	
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		const MultiValuedValue* dtg_node = *ci;
		old_to_new_node_mapping[dtg_node] = new std::vector<MultiValuedValue*>();
		
		// Check if this node needs to be split up.
		std::set<const HEURISTICS::VariableDomain*> all_variable_domains;
		
		for (std::vector<HEURISTICS::Fact*>::const_iterator ci = dtg_node->getValues().begin(); ci != dtg_node->getValues().end(); ++ci)
		{
			HEURISTICS::Fact* fact = *ci;
			all_variable_domains.insert(fact->getVariableDomains().begin(), fact->getVariableDomains().end());
		}
		
		// Split the variable domains up based on the equivalence relationships.
		std::map<const HEURISTICS::VariableDomain*, std::vector<const HEURISTICS::VariableDomain*>* > split_up_variable_domains;
		std::map<const HEURISTICS::VariableDomain*, unsigned int> counters;
		for (std::set<const HEURISTICS::VariableDomain*>::const_iterator ci = all_variable_domains.begin(); ci != all_variable_domains.end(); ++ci)
		{
			const HEURISTICS::VariableDomain* variable_domain = *ci;
			if (split_up_variable_domains.find(variable_domain) != split_up_variable_domains.end())
			{
				continue;
			}
			
			counters[variable_domain] = 0;
			std::vector<const HEURISTICS::VariableDomain* >* split_up_variable_domain = new std::vector<const HEURISTICS::VariableDomain* >();
			split_up_variable_domains[variable_domain] = split_up_variable_domain;
			std::set<const Object*> processed_objects;
			
			for (std::vector<const Object*>::const_iterator ci = variable_domain->getVariableDomain().begin(); ci != variable_domain->getVariableDomain().end(); ++ci)
			{
				const Object* object = *ci;
				if (processed_objects.find(object) != processed_objects.end())
				{
					continue;
				}
				
				std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator> equivalent_objects = equivalent_relationships.equal_range(object);
				
				std::vector<const Object*>* new_variable_domain = new std::vector<const Object*>();
				new_variable_domain->push_back(object);

				split_up_variable_domain->push_back(new HEURISTICS::VariableDomain(*new_variable_domain));
				
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
			MultiValuedValue* dtg_node_copy = new MultiValuedValue(*dtg_node);
			
			//for (std::vector<BoundedAtom*>::const_iterator ci = dtg_node_copy->getAtoms().begin(); ci != dtg_node_copy->getAtoms().end(); ++ci)
			for (unsigned int i = 0; i < dtg_node_copy->getValues().size(); ++i)
			{
				const HEURISTICS::Fact* org_fact = dtg_node->getValues()[i];
				const HEURISTICS::Fact* copied_fact = dtg_node_copy->getValues()[i];
				
				for (unsigned int term_index = 0; term_index < org_fact->getVariableDomains().size(); ++term_index)
				{
					const HEURISTICS::VariableDomain* org_domain = org_fact->getVariableDomains()[term_index];
					const HEURISTICS::VariableDomain* to_map_to = (*split_up_variable_domains[org_domain])[counters[org_domain]];
					const_cast<HEURISTICS::VariableDomain*>(copied_fact->getVariableDomains()[term_index])->set(to_map_to->getVariableDomain());
				}
			}
			
			old_to_new_node_mapping[dtg_node]->push_back(dtg_node_copy);
			new_to_old_node_mapping[dtg_node_copy] = dtg_node;
#ifdef MYPOP_SAS_PLUS_DTG_GRAPH_COMMENTS
			std::cout << "Split up dtg node: " << std::endl << *dtg_node_copy << std::endl;
#endif
			
			// Update the counters.
			for (std::map<const HEURISTICS::VariableDomain*, unsigned int>::const_iterator ci = counters.begin(); ci != counters.end(); ++ci)
			{
				const HEURISTICS::VariableDomain* variable_domain = (*ci).first;
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
		
		for (std::map<const HEURISTICS::VariableDomain*, std::vector<const HEURISTICS::VariableDomain*>* >::const_iterator ci = split_up_variable_domains.begin(); ci != split_up_variable_domains.end(); ++ci)
		{
			delete (*ci).second;
		}
	}
	
	// Remove the old nodes and add the new nodes.
	nodes_.clear();
	for (std::map<MultiValuedValue*, const MultiValuedValue*>::const_iterator ci = new_to_old_node_mapping.begin(); ci != new_to_old_node_mapping.end(); ++ci)
	{
		MultiValuedValue* new_node = (*ci).first;
		nodes_.push_back(new_node);
		const MultiValuedValue* old_node = (*ci).second;
		
		// Reestablish all the transitions.
		for (std::vector<const MultiValuedTransition*>::const_iterator ci = old_node->getTransitions().begin(); ci != old_node->getTransitions().end(); ++ci)
		{
			const MultiValuedTransition* transition = *ci;
			std::vector<MultiValuedValue*>* new_to_nodes = old_to_new_node_mapping[&transition->getToNode()];
			
			for (std::vector<MultiValuedValue*>::const_iterator ci = new_to_nodes->begin(); ci != new_to_nodes->end(); ++ci)
			{
				MultiValuedTransition* new_transition = transition->migrateTransition(*new_node, **ci, initial_facts, type_manager);
				if (new_transition != NULL)
				{
					new_node->addTransition(*new_transition);
				}
			}
		}
	}
	
	for (std::map<const MultiValuedValue*, std::vector<MultiValuedValue*>*>::const_iterator ci = old_to_new_node_mapping.begin(); ci != old_to_new_node_mapping.end(); ++ci)
	{
		delete (*ci).second;
	}
/*
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
	*/
}

MultiValuedValue* LiftedDTG::getMultiValuedValue(const PropertyState& property_state) const
{
	for (std::vector<MultiValuedValue*>::const_iterator ci = nodes_.begin(); ci != nodes_.end(); ++ci)
	{
		if (&(*ci)->getPropertyState() == &property_state)
		{
			return *ci;
		}
	}
	return NULL;
}

std::ostream& operator<<(std::ostream& os, const LiftedDTG& lifted_dtg)
{
	os << " === Lifted DTG === " << std::endl;
	for (std::vector<MultiValuedValue*>::const_iterator ci = lifted_dtg.nodes_.begin(); ci != lifted_dtg.nodes_.end(); ++ci)
	{
		os << **ci << std::endl;
	}
	return os;
}


};

};