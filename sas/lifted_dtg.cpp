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

namespace MyPOP
{
namespace SAS_Plus
{

MultiValuedValue::MultiValuedValue(const std::vector<HEURISTICS::Fact*>& values, const PropertyState& property_state)
	: values_(&values), property_state_(&property_state)
{

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
		std::cout << *new_ldtg << std::endl;
	}
	
	for (std::vector<LiftedDTG*>::const_iterator ci = created_lifted_dtgs.begin(); ci != created_lifted_dtgs.end(); ++ci)
	{
		LiftedDTG* lifted_dtg = *ci;
		lifted_dtg->createTransitions(created_lifted_dtgs);
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

void LiftedDTG::createTransitions(const std::vector<LiftedDTG*>& all_lifted_dtgs)
{
	// Connect the transitions.
	for (std::vector<PropertyState*>::const_iterator ci = property_space_->getPropertyStates().begin(); ci != property_space_->getPropertyStates().end(); ++ci)
	{
		const PropertyState* property_state = *ci;
		for (std::vector<const PropertyStateTransition*>::const_iterator ci = property_state->getTransitions().begin(); ci != property_state->getTransitions().end(); ++ci)
		{
			const PropertyStateTransition* transition = *ci;
			
			MultiValuedValue* from_node = getMultiValuedValue(transition->getFromPropertyState());
			MultiValuedValue* to_node = getMultiValuedValue(transition->getToPropertyState());
			
			const std::map<const Property*, std::vector<unsigned int>* >& mappings_to_action_variables = transition->getMappingToActionVariables();
			const std::vector<const HEURISTICS::VariableDomain*>& action_variables = transition->getActionVariableDomains();
			
			const std::vector<HEURISTICS::Fact*>& from_values = from_node->getValues();
			for (unsigned int fact_index = 0; fact_index < from_values.size(); ++fact_index)
			{
				HEURISTICS::Fact* fact = from_values[fact_index];
				const Property* property = from_node->getPropertyState().getProperties()[fact_index];
				
				assert (mappings_to_action_variables.find(property) != mappings_to_action_variables.end());
				
				const std::vector<unsigned int>* mapping_to_action_variables = (*mappings_to_action_variables.find(property)).second;
				for (unsigned int fact_term_index = 0; fact_term_index < fact->getVariableDomains().size(); ++fact_term_index)
				{
					std::cout << "The " << fact_term_index << " is mapped to the " << (*mapping_to_action_variables)[fact_term_index] << "th action variable!" << std::endl;
					assert ((*mapping_to_action_variables).size() > fact_term_index);
					assert ((*mapping_to_action_variables)[fact_term_index] < action_variables.size());
					fact->setVariableDomain(fact_term_index, *action_variables[(*mapping_to_action_variables)[fact_term_index]]);
				}
			}
			
			const std::vector<HEURISTICS::Fact*>& to_values = to_node->getValues();
			for (unsigned int fact_index = 0; fact_index < to_values.size(); ++fact_index)
			{
				HEURISTICS::Fact* fact = to_values[fact_index];
				const Property* property = to_node->getPropertyState().getProperties()[fact_index];
				
				const std::vector<unsigned int>* mapping_to_action_variables = (*mappings_to_action_variables.find(property)).second;
				for (unsigned int fact_term_index = 0; fact_term_index < fact->getVariableDomains().size(); ++fact_term_index)
				{
					fact->setVariableDomain(fact_term_index, *action_variables[(*mapping_to_action_variables)[fact_term_index]]);
				}
			}
		}
	}
	
	std::cout << *this << std::endl;
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