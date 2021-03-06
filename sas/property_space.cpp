#include "property_space.h"

#include <vector>
#include "predicate_manager.h"
#include "formula.h"
#include "term_manager.h"
#include "action_manager.h"
#include "type_manager.h"
#include <parser_utils.h>
#include <heuristics/fact_set.h>

//#define MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT

namespace MyPOP {

namespace SAS_Plus {

std::vector<const Property*> Property::all_properties_;

PropertyStateTransition::PropertyStateTransition(PropertyState& lhs, PropertyState& rhs, const std::vector<const Property*>& preconditions, const std::vector<const Property*>& added_properties, const Action& action, std::map<const Property*, std::vector<unsigned int>* >& precondition_properties_to_action_variable_mappings, std::map<const Property*, std::vector<unsigned int>* >& effect_properties_to_action_variable_mappings, const std::vector<const HEURISTICS::VariableDomain*>& action_variable_to_effect_mappings)
	: lhs_property_state_(&lhs), rhs_property_state_(&rhs), preconditions_(preconditions), effects_(added_properties), action_(&action), precondition_properties_to_action_variable_index_(&precondition_properties_to_action_variable_mappings), effect_properties_to_action_variable_index_(&effect_properties_to_action_variable_mappings), action_variable_domains_(&action_variable_to_effect_mappings)
{
	unsigned int invariable_action_variable = 0;
	
	for (std::map<const Property*, std::vector<unsigned int>* >::const_iterator ci = precondition_properties_to_action_variable_mappings.begin(); ci != precondition_properties_to_action_variable_mappings.end(); ++ci)
	{
		const Property* property = (*ci).first;
		const std::vector<unsigned int>* mappings = (*ci).second;
		if (mappings != NULL && property->getIndex() != std::numeric_limits<unsigned int>::max())
		{
			invariable_action_variable = (*mappings)[property->getIndex()];
			break;
		}
	}

	// Search for persistent facts.
	for (std::vector<const Property*>::const_iterator ci = lhs.getProperties().begin(); ci != lhs.getProperties().end(); ++ci)
	{
		const Property* property = *ci;
	
		if (precondition_properties_to_action_variable_mappings.find(property) != precondition_properties_to_action_variable_mappings.end())
		{
			continue;
		}
		
		// Find a precondition that can unify with the property.
		std::vector<const Atom*> preconditions;
		Utility::convertFormula(preconditions, &action.getPrecondition());
		
		for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
		{
			const Atom* precondition = *ci;
			
			if (property->getPredicate().getArity() != precondition->getPredicate().getArity() ||
			    property->getPredicate().getName() != precondition->getPredicate().getName())
			{
				continue;
			}
			
			// Check there is no effect which removes this.
			bool precondition_is_deleted = false;
			for (std::vector<const Atom*>::const_iterator ci = action.getEffects().begin(); ci != action.getEffects().end(); ++ci)
			{
				const Atom* effect = *ci;
				if (!effect->isNegative() ||
				    precondition->getArity() != effect->getArity() ||
				    precondition->getPredicate().getName() != effect->getPredicate().getName())
				{
					continue;
				}
				
				bool terms_match = true;
				for (unsigned int term_index = 0; term_index < effect->getArity(); ++term_index)
				{
					if (effect->getTerms()[term_index] != precondition->getTerms()[term_index])
					{
						terms_match = false;
						break;
					}
				}
				
				if (terms_match)
				{
					precondition_is_deleted = true;
					break;
				}
			}
			
			if (precondition_is_deleted)
			{
				continue;
			}
			
			bool terms_match = true;
			std::vector<unsigned int>* mappings = new std::vector<unsigned int>();
			for (unsigned int term_index = 0; term_index < precondition->getArity(); ++term_index)
			{
				if (!precondition->getTerms()[term_index]->getType()->isEqual(*property->getPredicate().getTypes()[term_index]) &&
				    !precondition->getTerms()[term_index]->getType()->isSubtypeOf(*property->getPredicate().getTypes()[term_index]) &&
				    !precondition->getTerms()[term_index]->getType()->isSupertypeOf(*property->getPredicate().getTypes()[term_index]))
				{
					terms_match = false;
					break;
				}
				
				for (unsigned int action_variable_index = 0; action_variable_index < action.getVariables().size(); ++action_variable_index)
				{
					if (action.getVariables()[action_variable_index] == precondition->getTerms()[term_index])
					{
						mappings->push_back(action_variable_index);
						break;
					}
				}
			}
			
			if (!terms_match || (*mappings)[property->getIndex()] != invariable_action_variable)
			{
				delete mappings;
				continue;
			}
			
			(*precondition_properties_to_action_variable_index_)[property] = mappings;
			
			// Map the effects too.
			for (std::vector<const Property*>::const_iterator ci = rhs.getProperties().begin(); ci != rhs.getProperties().end(); ++ci)
			{
				const Property* effect = *ci;
				if (effect->getIndex() == property->getIndex() &&
				    effect->getPredicate().getArity() == property->getPredicate().getArity() &&
				    effect->getPredicate().getName() == property->getPredicate().getName())
				{
					(*effect_properties_to_action_variable_index_)[effect] = new std::vector<unsigned int>(*mappings);
					break;
				}
			}
			break;
		}
	}
}

PropertyStateTransition& PropertyStateTransition::merge(const PropertyStateTransition& lhs, const PropertyStateTransition& rhs)
{
	if (&lhs.getFromPropertyState() != &rhs.getFromPropertyState() ||
	    &lhs.getToPropertyState() != &rhs.getToPropertyState() ||
	    &lhs.getAction() != &rhs.getAction())
	{
		std::cerr << lhs.getFromPropertyState() << "<=>" << rhs.getFromPropertyState() << std::endl;
		std::cerr << lhs.getToPropertyState() << "<=>" << rhs.getToPropertyState() << std::endl;
		std::cerr << lhs.getAction() << "<=>" << rhs.getAction() << std::endl;
		
		std::cerr << lhs << std::endl << rhs << std::endl;
	}
	
	assert (&lhs.getFromPropertyState() == &rhs.getFromPropertyState());
	assert (&lhs.getToPropertyState() == &rhs.getToPropertyState());
	assert (&lhs.getAction() == &rhs.getAction());
	
	std::vector<const Property*>* combined_preconditions = new std::vector<const Property*>(lhs.preconditions_);
	std::vector<const Property*>* combined_effects = new std::vector<const Property*>(lhs.effects_);
	
	for (std::vector<const Property*>::const_iterator ci = rhs.preconditions_.begin(); ci != rhs.preconditions_.end(); ++ci)
	{
		if (std::find(combined_preconditions->begin(), combined_preconditions->end(), *ci) == combined_preconditions->end())
		{
			combined_preconditions->push_back(*ci);
		}
	}
	
	for (std::vector<const Property*>::const_iterator ci = rhs.effects_.begin(); ci != rhs.effects_.end(); ++ci)
	{
		if (std::find(combined_effects->begin(), combined_effects->end(), *ci) == combined_effects->end())
		{
			combined_effects->push_back(*ci);
		}
	}
	
	//precondition_properties_to_action_variable_mappings, 
	std::map<const Property*, std::vector<unsigned int>* >* combined_precondition_mappings = new std::map<const Property*, std::vector<unsigned int>* >(*lhs.precondition_properties_to_action_variable_index_);
	combined_precondition_mappings->insert(rhs.precondition_properties_to_action_variable_index_->begin(), rhs.precondition_properties_to_action_variable_index_->end());
	//effect_properties_to_action_variable_mappings, 
	std::map<const Property*, std::vector<unsigned int>* >* combined_effect_mappings = new std::map<const Property*, std::vector<unsigned int>* >(*lhs.effect_properties_to_action_variable_index_);
	combined_effect_mappings->insert(rhs.effect_properties_to_action_variable_index_->begin(), rhs.effect_properties_to_action_variable_index_->end());
	//action_variable_to_effect_mappings
	std::vector<const HEURISTICS::VariableDomain*>* action_variable_to_effect_mappings = new std::vector<const HEURISTICS::VariableDomain*>(*lhs.action_variable_domains_);
	for (unsigned int i = 0; i < action_variable_to_effect_mappings->size(); ++i)
	{
		assert (*(*action_variable_to_effect_mappings)[i] == *(*rhs.action_variable_domains_)[i]);
	}

	PropertyStateTransition* merged_transition = new PropertyStateTransition(lhs.getFromPropertyState(), lhs.getToPropertyState(), *combined_preconditions, *combined_effects, lhs.getAction(), *combined_precondition_mappings, *combined_effect_mappings, *action_variable_to_effect_mappings);
	
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cerr << "Merged: " << *merged_transition << std::endl;
#endif
	return *merged_transition;
}

const std::vector<unsigned int>* PropertyStateTransition::getMappingsOfProperty(const Property& property, bool is_precondition) const
{
	std::map<const Property*, std::vector<unsigned int>* >::const_iterator ci;
	
	if (is_precondition)
	{
		ci = precondition_properties_to_action_variable_index_->find(&property);
		if (ci == precondition_properties_to_action_variable_index_->end())
		{
			return NULL;
		}
	}
	else
	{
		ci = effect_properties_to_action_variable_index_->find(&property);
		if (ci == effect_properties_to_action_variable_index_->end())
		{
			return NULL;
		}
	}
	return (*ci).second;
}

std::ostream& operator<<(std::ostream& os, const PropertyStateTransition& transition)
{
	os << "Transition: " << transition.action_->getPredicate() << " ";
	for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = transition.action_variable_domains_->begin(); ci != transition.action_variable_domains_->end(); ++ci)
	{
		os << **ci << " ";
	}
	os << "." << std::endl;
	
	os << "From node: " << std::endl;
	for (std::vector<const Property*>::const_iterator ci = transition.lhs_property_state_->getProperties().begin(); ci != transition.lhs_property_state_->getProperties().end(); ++ci)
	{
		os << **ci;
		
		const std::vector<unsigned int>* mappings = transition.getMappingsOfProperty(**ci, true);
		if (mappings != NULL)
		{
			os << "(";
			for (std::vector<unsigned int>::const_iterator ci = mappings->begin(); ci != mappings->end(); ++ci)
			{
				os << *ci << ", ";
			}
			os << ")";
		}
		os << std::endl;
	}
	
	os << "To node: " << std::endl;
	for (std::vector<const Property*>::const_iterator ci = transition.rhs_property_state_->getProperties().begin(); ci != transition.rhs_property_state_->getProperties().end(); ++ci)
	{
		os << **ci;
		
		const std::vector<unsigned int>* mappings = transition.getMappingsOfProperty(**ci, false);
		if (mappings != NULL)
		{
			os << "(";
			for (std::vector<unsigned int>::const_iterator ci = mappings->begin(); ci != mappings->end(); ++ci)
			{
				os << *ci << ", ";
			}
			os << ")";
		}
		os << std::endl;
	}
	return os;
}


/*****************************
 * Property state.
 ****************************/
/*PropertyState::PropertyState(const PropertySpace& property_space, const Property& property)
	: property_space_(&property_space)
{
	property_.push_back(&property);
}*/

PropertyState::PropertyState(const PropertySpace& property_space)
	: property_space_(&property_space)
{
	
}

PropertyState::PropertyState(const PropertySpace& property_space, const std::vector<std::pair<const Predicate*, InvariableIndex> >& properties)
	: property_space_(&property_space)
{
	for (std::vector<std::pair<const Predicate*, InvariableIndex> >::const_iterator ci = properties.begin(); ci != properties.end(); ci++)
	{
		property_.push_back(new Property(*this, *(*ci).first, (*ci).second));
	}
}

PropertyState::~PropertyState()
{
	for (std::vector<const Property*>::const_iterator ci = property_.begin(); ci != property_.end(); ci++)
	{
		delete *ci;
	}
}

void PropertyState::findMappings(std::vector<std::vector<const Property*>* >& mappings, const TIM::PropertyState& tim_property_state) const
{
	std::vector<const Property*> current_mapping;
	findMappings(mappings, current_mapping, tim_property_state, 0);
}

void PropertyState::findMappings(std::vector<std::vector<const Property*>* >& mappings, std::vector<const Property*>& current_mapping, const TIM::PropertyState& tim_property_state, unsigned int index) const
{
	TIM::PropertyState::PSIterator current_psi;
	unsigned int i = 0;
	for (current_psi = tim_property_state.begin(); ; ++current_psi)
	{
		if (i == index)
		{
			break;
		}
		++i;
	}
	if (current_psi == tim_property_state.end())
	{
		// Found a mapping!
		mappings.push_back(new std::vector<const Property*>(current_mapping));
		return;
	}
	
	TIM::Property* tim_property = *current_psi;
	
	// Find a property which can match with the TIM property.
	for (std::vector<const Property*>::const_iterator ci = property_.begin(); ci != property_.end(); ++ci)
	{
		const Property* property = *ci;
		
		if (property->getPredicate().getName() == tim_property->root()->getName() &&
		    property->getIndex() == (unsigned int)tim_property->aPosn())
		{
			std::vector<const Property*> new_mapping(current_mapping);
			new_mapping.push_back(property);
			findMappings(mappings, new_mapping, tim_property_state, index + 1);
		}
	}
}

bool PropertyState::contains(InvariableIndex index, const Predicate& predicate) const
{
	for (std::vector<const Property*>::const_iterator ci = property_.begin(); ci != property_.end(); ci++)
	{
		const Property* property = *ci;
		if (property->getPredicate().getName() == predicate.getName() && property->getPredicate().getArity() == predicate.getArity() && property->getIndex() == index)
		{
			return true;
		}
	}
	return false;
}

const std::vector<const Property*>& PropertyState::getProperties() const
{
	return property_;
}

const PropertySpace& PropertyState::getPropertySpace() const
{
	return *property_space_;
}

void PropertyState::addTransition(const PropertyStateTransition& transition)
{
	for (std::vector<const PropertyStateTransition*>::iterator i = transitions_.begin(); i != transitions_.end(); ++i)
	{
		const PropertyStateTransition* t = *i;
		
		// If the action already exists, it must be merged!
		if (&t->getAction() == &transition.getAction() &&
		    &t->getFromPropertyState() == &transition.getFromPropertyState() &&
		    &t->getToPropertyState() == &transition.getToPropertyState())
		{
			PropertyStateTransition& merged_transition = PropertyStateTransition::merge(*t, transition);
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
			std::cerr << "Merged action: " << merged_transition << "!" << std::endl;
#endif
			transitions_.erase(i);
			transitions_.push_back(&merged_transition);
			return;

		}
	}
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cerr << "Add the action " << transition.getAction().getPredicate() << " to " << this << std::endl;
#endif
	transitions_.push_back(&transition);
}

void PropertyState::addTransition(const PredicateManager& property_manager, const TypeManager& type_manager, const MyPOP::Action& action, PropertyState& rhs_property_state, const std::vector<const Property*>& preconditions, const std::vector<const Property*>& added_properties)
{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cout << "ADD TRANSITION: " << action.getPredicate() << std::endl << *this << std::endl << "=== TO ===" << std::endl << rhs_property_state << std::endl;
#endif
	for (std::vector<const PropertyStateTransition*>::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ++ci)
	{
		if (&(*ci)->getAction() == &action && &(*ci)->getToPropertyState() == &rhs_property_state)
		{
			return;
		}
	}
	
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	if (this == &rhs_property_state)
	{
		std::cout << "Cyclic transition!!!" << std::endl;
	}
#endif
	
	// Update the types.
	std::vector<const HEURISTICS::VariableDomain*> action_variable_types;
	for (std::vector<const Variable*>::const_iterator ci = action.getVariables().begin(); ci != action.getVariables().end(); ++ci)
	{
		const Variable* variable = *ci;
		std::vector<const Object*> objects_of_type;
		type_manager.getObjectsOfType(objects_of_type, *variable->getType());
		action_variable_types.push_back(new HEURISTICS::VariableDomain(objects_of_type));
	}
	
	// Make sure that non of the action variables are empty.
	bool contains_empty_variable_domain = false;
	for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_types.begin(); ci != action_variable_types.end(); ++ci)
	{
		const HEURISTICS::VariableDomain* vd = *ci;
		if (vd->getVariableDomain().empty())
		{
			contains_empty_variable_domain = true;
			break;
		}
	}
	if (!contains_empty_variable_domain)
	{
		std::map<const Property*, std::vector<unsigned int>* > precondition_mappings;
		std::map<const Property*, std::vector<unsigned int>* > effect_mappings;
		
		FoundVariableMappings* found_mapping = getMappings(type_manager, preconditions, added_properties, action, action_variable_types, 0, precondition_mappings, effect_mappings);
		if (!found_mapping)
		{
			std::cerr << "The transition " << action.getPredicate() << " cannot go from " << std::endl;
			for (std::vector<const Property*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
			{
				std::cerr << **ci << std::endl;
			}
			std::cerr << "to" << std::endl;
			for (std::vector<const Property*>::const_iterator ci = added_properties.begin(); ci != added_properties.end(); ++ci)
			{
				std::cerr << **ci << std::endl;
			}
			assert (false);
		}
		
		//std::pair<std::map<const Property*, std::vector<unsigned int>* >*, const std::vector<const HEURISTICS::VariableDomain*>* > mapping = getMappings(type_manager, preconditions, added_properties, action, bindings_to_action_variables, action_variable_types, 0);
		PropertyStateTransition* new_transition = new PropertyStateTransition(*this, rhs_property_state, preconditions, added_properties, action, *found_mapping->precondition_mappings_, *found_mapping->effect_mappings_, *found_mapping->action_variable_assignments_);
		transitions_.push_back(new_transition);
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
		std::cout << "New transition: " << *new_transition << std::endl;
#endif
	}
	for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_types.begin(); ci != action_variable_types.end(); ++ci)
	{
		delete *ci;
	}
}

FoundVariableMappings* PropertyState::getMappings(const TypeManager& type_manager, const std::vector<const Property*>& precondition_properties, const std::vector<const Property*>& effects_properties, const Action& action, const std::vector<const HEURISTICS::VariableDomain*>& action_variable_types, unsigned int property_index_to_process, std::map<const Property*, std::vector<unsigned int>* >& precondition_mappings, std::map<const Property*, std::vector<unsigned int>* >& effect_mappings)
{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cout << "[PropertyState::getMappings] " << property_index_to_process << std::endl;
	
	std::cout << "Current assignments: " << action.getPredicate();
	for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_types.begin(); ci != action_variable_types.end(); ++ci)
	{
		std::cout << **ci << ", ";
	}
	std::cout << "." << std::endl;
	std::cout << " = Preconditions: " << std::endl;
	for (std::vector<const Property*>::const_iterator ci = precondition_properties.begin(); ci != precondition_properties.end(); ++ci)
	{
		const Property* precondition = *ci;
		std::cout << precondition->getPredicate().getName();
		
		if (precondition_mappings.find(*ci) == precondition_mappings.end())
		{
			continue;
		}
		std::vector<unsigned int>* mappings_to_action_variable = (*precondition_mappings.find(*ci)).second;
		for (std::vector<unsigned int>::const_iterator ci = mappings_to_action_variable->begin(); ci != mappings_to_action_variable->end(); ++ci)
		{
			std::cout << *action_variable_types[*ci] << " ";
		}
		std::cout << "." << std::endl;
	}
	
	std::cout << " = Effects: " << std::endl;
	for (std::vector<const Property*>::const_iterator ci = effects_properties.begin(); ci != effects_properties.end(); ++ci)
	{
		const Property* effect = *ci;
		std::cout << effect->getPredicate().getName();
		
		if (effect_mappings.find(*ci) == effect_mappings.end())
		{
			continue;
		}
		
		std::vector<unsigned int>* mappings_to_action_variable = (*effect_mappings.find(*ci)).second;
		for (std::vector<unsigned int>::const_iterator ci = mappings_to_action_variable->begin(); ci != mappings_to_action_variable->end(); ++ci)
		{
			std::cout << *action_variable_types[*ci] << " ";
		}
		std::cout << "." << std::endl;
	}
#endif
	const Property* property_to_process = NULL;
	std::vector<const Atom*> action_facts;
	bool is_precondition = true;
	
	// Found a complete assignment!
	if (property_index_to_process == precondition_properties.size() + effects_properties.size())
	{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
		std::cout << "Found propper mappings: " << action.getPredicate();
		for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_types.begin(); ci != action_variable_types.end(); ++ci)
		{
			std::cout << **ci << ", ";
		}
		std::cout << "." << std::endl;
		std::cout << " = Preconditions: " << std::endl;
		for (std::vector<const Property*>::const_iterator ci = precondition_properties.begin(); ci != precondition_properties.end(); ++ci)
		{
			const Property* precondition = *ci;
			std::cout << precondition->getPredicate().getName();
			
			std::vector<unsigned int>* mappings_to_action_variable = (*precondition_mappings.find(*ci)).second;
			for (std::vector<unsigned int>::const_iterator ci = mappings_to_action_variable->begin(); ci != mappings_to_action_variable->end(); ++ci)
			{
				std::cout << *action_variable_types[*ci] << " ";
			}
			std::cout << "." << std::endl;
		}
		
		std::cout << " = Effects: " << std::endl;
		for (std::vector<const Property*>::const_iterator ci = effects_properties.begin(); ci != effects_properties.end(); ++ci)
		{
			const Property* effect = *ci;
			std::cout << effect->getPredicate().getName();
			
			std::vector<unsigned int>* mappings_to_action_variable = (*effect_mappings.find(*ci)).second;
			for (std::vector<unsigned int>::const_iterator ci = mappings_to_action_variable->begin(); ci != mappings_to_action_variable->end(); ++ci)
			{
				std::cout << *action_variable_types[*ci] << " ";
			}
			std::cout << "." << std::endl;
		}
#endif
		std::map<const Property*, std::vector<unsigned int>* >* precondition_mappings_copy = new std::map<const Property*, std::vector<unsigned int>* >();
		for (std::map<const Property*, std::vector<unsigned int>* >::const_iterator ci = precondition_mappings.begin(); ci != precondition_mappings.end(); ++ci)
		{
			std::vector<unsigned int>* bindings = new std::vector<unsigned int>(*(*ci).second);
			(*precondition_mappings_copy)[(*ci).first] = bindings;
		}
		
		std::map<const Property*, std::vector<unsigned int>* >* effect_mappings_copy = new std::map<const Property*, std::vector<unsigned int>* >();
		for (std::map<const Property*, std::vector<unsigned int>* >::const_iterator ci = effect_mappings.begin(); ci != effect_mappings.end(); ++ci)
		{
			std::vector<unsigned int>* bindings = new std::vector<unsigned int>(*(*ci).second);
			(*effect_mappings_copy)[(*ci).first] = bindings;
		}
		
		std::vector<const HEURISTICS::VariableDomain*>* new_action_variable_assignments = new std::vector<const HEURISTICS::VariableDomain*>();
		for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_types.begin(); ci != action_variable_types.end(); ++ci)
		{
			new_action_variable_assignments->push_back(new HEURISTICS::VariableDomain((*ci)->getVariableDomain()));
		}
		return new FoundVariableMappings(*new_action_variable_assignments, *precondition_mappings_copy, *effect_mappings_copy);
	}
	else if (property_index_to_process < precondition_properties.size())
	{
		property_to_process = precondition_properties[property_index_to_process];
		Utility::convertFormula(action_facts, &action.getPrecondition());
	}
	else
	{
		property_to_process = effects_properties[property_index_to_process - precondition_properties.size()];
		is_precondition = false;
		action_facts = action.getEffects();
	}
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cout << "Find a fact which can unify with: " << *property_to_process << std::endl;
#endif
	for (std::vector<const Atom*>::const_iterator ci = action_facts.begin(); ci != action_facts.end(); ++ci)
	{
		const Atom* action_fact = *ci;
		if (action_fact->getArity() != property_to_process->getPredicate().getArity() ||
		    action_fact->getPredicate().getName() != property_to_process->getPredicate().getName())
		{
			continue;
		}
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
		std::cout << "Compare against:  ";
		action_fact->print(std::cout);
		std::cout << "." << std::endl;
#endif
		// Can this be 'unified' with the property at hand.
		std::vector<unsigned int> action_variable_mappings;
		bool terms_match = true;
		
		// Update the variable domains of the action.
		std::vector<const HEURISTICS::VariableDomain*> new_action_variable_assignments;
		for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_types.begin(); ci != action_variable_types.end(); ++ci)
		{
			new_action_variable_assignments.push_back(new HEURISTICS::VariableDomain(**ci));
		}
		
		for (unsigned int term_index = 0; term_index < action_fact->getTerms().size(); ++term_index)
		{
			const Term* action_term = action_fact->getTerms()[term_index];
			
			for (unsigned int i = 0; i < action.getVariables().size(); ++i)
			{
				if (action.getVariables()[i] == action_term)
				{
					action_variable_mappings.push_back(i);
					break;
				}
			}
			unsigned int matching_action_variable_index = action_variable_mappings[term_index];
//			std::cout << "The " << term_index << "th term index is linked to the " << action_term << " action variable." << std::endl;
			
			// Can this term unify with the term_index's index of the property.
			const Type& action_type = *action_term->getType();
			const Type& property_type = *property_to_process->getPredicate().getTypes()[term_index];
			
			if (!action_type.isEqual(property_type) && !action_type.isSubtypeOf(property_type) && !action_type.isSupertypeOf(property_type))
			{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
				std::cout << "The " << term_index << " variable does not match due to predicate issues... Type: " << action_type << " <-> " << property_type << std::endl;
#endif
				terms_match = false;
				break;
			}
			
			// Update the variable domain.
			std::vector<const Object*> objects_of_type;
			type_manager.getObjectsOfType(objects_of_type, property_type);
			HEURISTICS::VariableDomain type_variable_domain(objects_of_type);
			
			HEURISTICS::VariableDomain* intersection = new HEURISTICS::VariableDomain();
			type_variable_domain.getIntersection(*intersection, *new_action_variable_assignments[matching_action_variable_index]);
			delete new_action_variable_assignments[matching_action_variable_index];
			if (intersection->getVariableDomain().empty())
			{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
				std::cout << "The " << term_index << " variable does not match, due to an empty intersection..." << std::endl;
				std::cout << type_variable_domain << std::endl;
				std::cout << "v.s." << std::endl;
				std::cout << *new_action_variable_assignments[matching_action_variable_index] << std::endl;
#endif
				terms_match = false;
				break;
			}
			new_action_variable_assignments[matching_action_variable_index] = intersection;
		}
		
		if (!terms_match)
		{
			continue;
		}
		
		// Check if no bindings are violated.
		bool bindings_violated = false;
		
		for (std::map<const Property*, std::vector<unsigned int>* >::const_iterator ci = precondition_mappings.begin(); ci != precondition_mappings.end(); ++ci)
		{
			const Property* all_ready_processed_property = (*ci).first;
			const std::vector<unsigned int>* bindings = (*ci).second;
			
			// Check if the invariables are identical.
			unsigned int variable_index = (*bindings)[all_ready_processed_property->getIndex()];
			if (variable_index != action_variable_mappings[property_to_process->getIndex()])
			{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
				std::cout << "Precondition bindings violated!" << std::endl;
				std::cout << *all_ready_processed_property << " is linked to " << variable_index << " while the new one is linked to " << action_variable_mappings[property_to_process->getIndex()] << std::endl;
#endif
				bindings_violated = true;
				break;
			}
		}
		
		for (std::map<const Property*, std::vector<unsigned int>* >::const_iterator ci = effect_mappings.begin(); ci != effect_mappings.end(); ++ci)
		{
			const Property* all_ready_processed_property = (*ci).first;
			const std::vector<unsigned int>* bindings = (*ci).second;
			
			// Check if the invariables are identical.
			unsigned int variable_index = (*bindings)[all_ready_processed_property->getIndex()];
			if (variable_index != action_variable_mappings[property_to_process->getIndex()])
			{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
				std::cout << "Effect bindings violated!" << std::endl;
				std::cout << *all_ready_processed_property << " is linked to " << variable_index << " while the new one is linked to " << action_variable_mappings[property_to_process->getIndex()] << std::endl;
#endif
				bindings_violated = true;
				break;
			}
		}
		
		if (bindings_violated)
		{
			continue;
		}
		
		std::map<const Property*, std::vector<unsigned int>* > new_precondition_mappings(precondition_mappings);
		std::map<const Property*, std::vector<unsigned int>* > new_effect_mappings(effect_mappings);
		
		if (is_precondition)
		{
			new_precondition_mappings[property_to_process] = &action_variable_mappings;
		}
		else
		{
			new_effect_mappings[property_to_process] = &action_variable_mappings;
		}
		
		FoundVariableMappings* fvm = getMappings(type_manager, precondition_properties, effects_properties, action, new_action_variable_assignments, property_index_to_process + 1, new_precondition_mappings, new_effect_mappings);
		if (fvm != NULL)
		{
			return fvm;
		}
	}
	return NULL;
}

std::ostream& operator<<(std::ostream& os, const PropertyState& property_state)
{
	os << "property state: ";
	for (std::vector<const Property*>::const_iterator ci = property_state.getProperties().begin(); ci != property_state.getProperties().end(); ci++)
	{
		os << **ci << ", ";
	}
	os << std::endl;
	
	for (std::vector<const PropertyStateTransition*>::const_iterator ci = property_state.getTransitions().begin(); ci != property_state.getTransitions().end(); ++ci)
	{
		const PropertyState& to_state = (*ci)->getToPropertyState();
		os << "\t >>>===" << (*ci)->getAction().getPredicate() << "-> ";
		for (std::vector<const Property*>::const_iterator ci = to_state.getProperties().begin(); ci != to_state.getProperties().end(); ci++)
		{
			os << **ci << ", ";
		}
		os << std::endl;
	}
	return os;
}

/*****************************
 * Property.
 ****************************/
Property::Property(const PropertyState& property_state, const Predicate& predicate, InvariableIndex index)
	: property_state_(&property_state), predicate_(&predicate), index_(index)
{
	addProperty(*this);
}
	
const PropertyState& Property::getPropertyState() const
{
	return *property_state_;
}
	
const Predicate& Property::getPredicate() const
{
	return *predicate_;
}

void Property::setPredicate(const Predicate& predicate)
{
	predicate_ = &predicate;
}

InvariableIndex Property::getIndex() const
{
	return index_;
}
	
bool Property::isMutexWith(const Property* property) const
{
	if (property == NULL)
	{
		return false;
	}
	
//	std::cout << "Is mutex: " << getPredicate() << "(" << index_ << ") [" << &property_state_->getPropertySpace() << "] v.s. " << property->getPredicate() << "(" << property->getIndex() << ") [" << &property->property_state_->getPropertySpace() << "]" << std::endl;
	
	if (&property_state_->getPropertySpace() == &property->property_state_->getPropertySpace() &&
			property_state_ != property->property_state_)
	{
		/**
		 * If a property state exists which contains both properties it cannot be mutex.
		 */
		for (std::vector<PropertyState*>::const_iterator ci = property_state_->getPropertySpace().getPropertyStates().begin(); ci != property_state_->getPropertySpace().getPropertyStates().end(); ci++)
		{
			const PropertyState* property_state = *ci;
			
			unsigned int counter = 0;
			
			for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ci++)
			{
				const Property* other_property = *ci;
				
				if (property->getIndex() == other_property->getIndex() && property->getPredicate().getName() == other_property->getPredicate().getName() && property->getPredicate().getArity() == other_property->getPredicate().getArity())
				{
					++counter;
				}
				
				if (getIndex() == other_property->getIndex() && getPredicate().getName() == other_property->getPredicate().getName() && getPredicate().getArity() == other_property->getPredicate().getArity())
				{
					++counter;
				}
			}
			
			if (counter == 2)
			{
				return false;
			}
		}
		
		return true;
	}
	
	return false;
}

bool Property::operator==(const MyPOP::SAS_Plus::Property& property) const
{
	return predicate_ == property.predicate_ && index_ == property.index_;
}

std::ostream& operator<<(std::ostream& os, const Property& property)
{
	os << property.getPredicate() << "(" << property.getIndex() << ")";
	return os;
}

void Property::getProperties(std::vector< const MyPOP::SAS_Plus::Property* >& result, const Atom& atom)
{
	for (std::vector<const Property*>::const_iterator ci = all_properties_.begin(); ci != all_properties_.end(); ci++)
	{
		const Predicate* predicate = (*ci)->predicate_;
		
		if (predicate->canSubstitute(atom.getPredicate()))
		{
			result.push_back(*ci);
		}
	}
}

const std::vector<const Property*>& Property::getAllProperties()
{
	return all_properties_;
}

void Property::addProperty(const MyPOP::SAS_Plus::Property& property)
{
	for (std::vector<const Property*>::const_iterator ci = all_properties_.begin(); ci != all_properties_.end(); ci++)
	{
		if (property == **ci) return;
	}
	
	all_properties_.push_back(&property);
}



/*****************************
 * Property space.
 ****************************/
PropertySpace::PropertySpace(const TermManager& term_manager, TIM::PropertySpace::OIterator begin, TIM::PropertySpace::OIterator end)
{
	for (TIM::PropertySpace::OIterator oi = begin; oi != end; ++oi)
	{
		objects_.push_back(&term_manager.getObject((*oi)->getName()));
	}
	
	all_property_spaces_.push_back(this);
}

PropertySpace::PropertySpace()
{
	all_property_spaces_.push_back(this);
}

PropertySpace::~PropertySpace()
{
	for (std::vector<PropertyState*>::const_iterator ci = property_states_.begin(); ci != property_states_.end(); ci++)
	{
		delete *ci;
	}
}

bool PropertySpace::isBalanced(InvariableIndex index, const Predicate& predicate) const
{
	for (std::vector<PropertyState*>::const_iterator ci = property_states_.begin(); ci != property_states_.end(); ci++)
	{
		const PropertyState* property_state = *ci;
		if (property_state->contains(index, predicate))
		{
			return true;
		}
	}
	return false;
}

void PropertySpace::addPropertyState(PropertyState& property_state)
{
	property_states_.push_back(&property_state);
}
	
const std::vector<PropertyState*>& PropertySpace::getPropertyStates() const
{
	return property_states_;
}

bool PropertySpace::contains(const Object& object) const
{
	return std::find(objects_.begin(), objects_.end(), &object) != objects_.end();
}

std::ostream& operator<<(std::ostream& os, const PropertySpace& property_space)
{
	std::cout << "The property space: [";
	for (std::vector<const Object*>::const_iterator ci = property_space.getObjects().begin(); ci != property_space.getObjects().end(); ++ci)
	{
		std::cout << **ci << ", ";
	}
	std::cout << "]" << std::endl;
	for (std::vector<PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
	{
		os << "* " << **ci << std::endl;
	}
	return os;
}

/*****************************
 * Static functions.
 ****************************/
std::vector<const PropertySpace*> PropertySpace::all_property_spaces_;

PropertySpace& PropertySpace::createPropertySpace(const TermManager& term_manager, TIM::PropertySpace::OIterator begin, TIM::PropertySpace::OIterator end)
{
	PropertySpace* ps = new PropertySpace(term_manager, begin, end);
	ps->is_property_space_ = true;
	return *ps;
}

PropertySpace& PropertySpace::createAttributeSpace()
{
	PropertySpace* ps = new PropertySpace();
	ps->is_property_space_ = false;
	return *ps;
}

void PropertySpace::removeAllPropertySpaces()
{
	for (std::vector<const PropertySpace*>::const_iterator ci = all_property_spaces_.begin(); ci != all_property_spaces_.end(); ci++)
	{
		delete *ci;
	}
	all_property_spaces_.clear();
}

void PropertySpace::copyMergedTransitions(const PropertySpace& property_space, std::map<const PropertyState*, unsigned int>& offsets, PropertySpace& new_property_space, const std::multimap<const PropertyState*, PropertyState*>& old_to_merged_property_state_mappings, const TypeManager& type_manager)
{
	for (std::vector<PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ++ci)
	{
		const PropertyState* org_property_state = *ci;
		
		std::pair<std::multimap<const PropertyState*, PropertyState*>::const_iterator, std::multimap<const PropertyState*, PropertyState*>::const_iterator> merged_property_states_ci = old_to_merged_property_state_mappings.equal_range(org_property_state);
		for (std::multimap<const PropertyState*, PropertyState*>::const_iterator ci = merged_property_states_ci.first; ci != merged_property_states_ci.second; ++ci)
		{
			PropertyState* merged_property_state = (*ci).second;
			
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
			std::cout << "Process the merged property state: FROM." << *merged_property_state << std::endl;
#endif
		
			std::vector<PropertyStateTransition*> all_merged_transition;
			for (std::vector<const PropertyStateTransition*>::const_iterator ci = org_property_state->getTransitions().begin(); ci != org_property_state->getTransitions().end(); ++ci)
			{
				const PropertyStateTransition* old_transition = *ci;
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
				std::cout << "New from node: " << std::endl << *merged_property_state << std::endl;
				std::cout << "Org transition: " << *old_transition << std::endl;
#endif
				
				// TODO: Check if no preconditions are violated ty the merged properties.
				unsigned int invariable_action_parameter_index = std::numeric_limits<unsigned int>::max();
				for (std::vector<const Property*>::const_iterator ci = org_property_state->getProperties().begin(); ci != org_property_state->getProperties().end(); ++ci)
				{
					const std::vector<unsigned int>* mappings = old_transition->getMappingsOfProperty(**ci, true);
					if (mappings != NULL && (*ci)->getIndex() != std::numeric_limits<unsigned int>::max())
					{
						invariable_action_parameter_index = (*mappings)[(*ci)->getIndex()];
					}
				}
				
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
				std::cout << "Invariable action variable: " << invariable_action_parameter_index << std::endl;
#endif

				// Now check if all the properties in the merged property state adhere to this index.
				std::vector<const Atom*> preconditions;
				Utility::convertFormula(preconditions, &old_transition->getAction().getPrecondition());
				
				bool contains_violating_precondition = false;
				
				// Check if the precondition is linked to the properties.
				for (std::vector<const Atom*>::const_iterator ci = preconditions.begin(); ci != preconditions.end(); ++ci)
				{
					const Atom* precondition = *ci;
					
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
					std::cout << "Precondition: ";
					precondition->print(std::cout);
					std::cout << "." << std::endl;
#endif
					
					if (violatesPrecondition(*precondition, invariable_action_parameter_index, *old_transition, *merged_property_state))
					{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
						std::cout << "Do not add the transition: " << *old_transition << std::endl;
						std::cout << "Because the precondition: ";
						precondition->print(std::cout);
						std::cout << " violates a property!" << std::endl;
						std::cout << *merged_property_state << std::endl;
#endif
						contains_violating_precondition = true;
						break;
					}
				}

				if (contains_violating_precondition)
				{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
						std::cout << "Precondition violated!" << std::endl;
#endif
					continue;
				}
				
				std::pair<std::multimap<const PropertyState*, PropertyState*>::const_iterator, std::multimap<const PropertyState*, PropertyState*>::const_iterator> merged_to_property_states_ci = old_to_merged_property_state_mappings.equal_range(&old_transition->getToPropertyState());
				
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
				std::cout << "The to property state: " << old_transition->getToPropertyState() << " maps to: " << std::endl;
				for (std::multimap<const PropertyState*, PropertyState*>::const_iterator ci = merged_to_property_states_ci.first; ci != merged_to_property_states_ci.second; ++ci)
				{
					std::cout << "* " << *(*ci).second << std::endl;
				}
#endif
				for (std::multimap<const PropertyState*, PropertyState*>::const_iterator ci = merged_to_property_states_ci.first; ci != merged_to_property_states_ci.second; ++ci)
				{
					PropertyState* merged_to_property_state = (*ci).second;
					
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
					std::cout << "New to node: " << std::endl << *merged_to_property_state << std::endl;
#endif
					
					// Now check if all the effects in the merged property state adhere to this index.
					bool contains_violating_effects = false;
					
					// Check if the precondition is linked to the properties.
					for (std::vector<const Atom*>::const_iterator ci = old_transition->getAction().getEffects().begin(); ci != old_transition->getAction().getEffects().end(); ++ci)
					{
						const Atom* effect = *ci;
						
						if (effect->isNegative())
						{
							continue;
						}
						
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
						std::cout << "Effect: ";
						effect->print(std::cout);
						std::cout << "." << std::endl;
#endif
						
						if (violatesPrecondition(*effect, invariable_action_parameter_index, *old_transition, *merged_to_property_state))
						{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
							std::cout << "Do not add the transition: " << *old_transition << std::endl;
							std::cout << "Because the effect: ";
							effect->print(std::cout);
							std::cout << " violates a property!" << std::endl;
							std::cout << *merged_to_property_state << std::endl;
#endif
							contains_violating_effects = true;
							break;
						}
					}

					if (contains_violating_effects)
					{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
						std::cout << "Effect violated!" << std::endl;
#endif
						continue;
					}
					
					// Check that each effect is either added or is part of the from node. Also check that each property that is part of the 
					// from node that is not part of the to node is removed.
					bool persistent_facts_are_violated = false;
					
					for (std::vector<const Property*>::const_iterator ci = merged_property_state->getProperties().begin(); ci != merged_property_state->getProperties().end(); ++ci)
					{
						const Property* from_property = *ci;
						
						// Check if it is part of the to node.
						bool is_part_of_to_node = false;
						for (std::vector<const Property*>::const_iterator ci = merged_to_property_state->getProperties().begin(); ci != merged_to_property_state->getProperties().end(); ++ci)
						{
							const Property* to_property = *ci;
							if (*from_property == *to_property)
							{
								is_part_of_to_node = true;
								break;
							}
						}
						
						std::vector<const Atom*> matching_preconditions;
						getMatchingFacts(matching_preconditions, *from_property, preconditions, type_manager);
						
						bool precondition_is_deleted = false;
						bool precondition_is_added = false;
						
						for (std::vector<const Atom*>::const_iterator ci = matching_preconditions.begin(); ci != matching_preconditions.end(); ++ci)
						{
							const Atom* precondition = *ci;

							// Check if there is an effect which removes this precondition.
							for (std::vector<const Atom*>::const_iterator ci = old_transition->getAction().getEffects().begin(); ci != old_transition->getAction().getEffects().end(); ++ci)
							{
								const Atom* effect = *ci;
								if (precondition->getPredicate().getName() != effect->getPredicate().getName() ||
										precondition->getPredicate().getArity() != effect->getPredicate().getArity())
								{
									continue;
								}
								
								bool terms_match = true;
								for (unsigned int term_index = 0; term_index < effect->getArity(); ++term_index)
								{
									if (precondition->getTerms()[term_index] != effect->getTerms()[term_index])
									{
										terms_match = false;
										break;
									}
								}
								
								if (terms_match)
								{
									if (effect->isNegative())
									{
										precondition_is_deleted = true;
									}
									else
									{
										precondition_is_added = true;
									}
								}
							}
						}
						
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
						std::cout << "Precondition: " << *from_property << ";Part of to node?" << is_part_of_to_node << ";Added=" << precondition_is_added << ";Deleted=" << precondition_is_deleted << "." << std::endl;
#endif
						
						// If a precondition is part of the to node than it must either not be deleted or added.
						//if (is_part_of_to_node && !(precondition_is_added || !precondition_is_deleted))
						if (is_part_of_to_node && precondition_is_deleted && !precondition_is_added)
						{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
							std::cout << *from_property << " is part of the to node but is deleted and not added!" << std::endl;
#endif
							
							// Check if there is an effect which adds a similar fact.
							std::vector<const Atom*> matching_effects;
							getMatchingFacts(matching_effects, *from_property, old_transition->getAction().getEffects(), type_manager);

							if (matching_effects.empty())
							{
								persistent_facts_are_violated = true;
								break;
							}
							else
							{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
								std::cout << "But there is an effect which does add it!" << std::endl;
#endif
							}
						}
						
						// A precondition that is not part of the to node must be deleted.
						if (!is_part_of_to_node && (precondition_is_added || !precondition_is_deleted))
						{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
							std::cout << *from_property << " is not part of the to node but is not added and is not deleted!" << std::endl;
#endif
							persistent_facts_are_violated = true;
							break;
						}
					}
					
					// Next we must do the same checks for the effects.
					for (std::vector<const Property*>::const_iterator ci = merged_to_property_state->getProperties().begin(); ci != merged_to_property_state->getProperties().end(); ++ci)
					{
						const Property* to_property = *ci;
						
						// Check if it is part of the to node.
						bool is_part_of_from_node = false;
						for (std::vector<const Property*>::const_iterator ci = merged_property_state->getProperties().begin(); ci != merged_property_state->getProperties().end(); ++ci)
						{
							const Property* from_property = *ci;
							
							if (*from_property == *to_property)
							{
								is_part_of_from_node = true;
								break;
							}
						}
						
						std::vector<const Atom*> matching_effects;
						getMatchingFacts(matching_effects, *to_property, old_transition->getAction().getEffects(), type_manager);
						
						bool effect_is_deleted = false;
						bool effect_is_added = false;
						
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
						std::cout << "To property: " << *to_property << " is added by: " << std::endl;
#endif
						for (std::vector<const Atom*>::const_iterator ci = matching_effects.begin(); ci != matching_effects.end(); ++ci)
						{
							const Atom* effect = *ci;
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
							std::cout << "* ";
							effect->print(std::cout);
							std::cout << "." << std::endl;
#endif
							if (effect->isNegative())
							{
								effect_is_deleted = true;
							}
							else
							{
								effect_is_added = true;
							}
						}
						
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
						std::cout << "Effect: " << *to_property << ";added=" << effect_is_added << ";deleted=" << effect_is_deleted << "." << std::endl;
#endif
						
						// If an effect is part of the from node than it must either not be deleted or added.
						//if (is_part_of_from_node && !(effect_is_added || !effect_is_deleted))
						if (is_part_of_from_node && effect_is_deleted && !effect_is_added)
						{
							
							// Check if there is an effect which adds a similar fact.
							std::vector<const Atom*> matching_effects;
							getMatchingFacts(matching_effects, *to_property, old_transition->getAction().getEffects(), type_manager);

#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
							std::cout << *to_property << " is part of the from node but deleted and not added!" << std::endl;
#endif
							
							if (matching_effects.empty())
							{
								persistent_facts_are_violated = true;
								break;
							}
							else
							{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
								std::cout << "But there is an effect which does add it!" << std::endl;
#endif
							}
						}
						// An effect that is not part of the from node must be added.
						if (!is_part_of_from_node && !effect_is_added)
						{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
							std::cout << *to_property << " is not part of the from and is not added!" << std::endl;
#endif
							persistent_facts_are_violated = true;
							break;
						}
					}
					
					if (persistent_facts_are_violated)
					{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
						std::cout << "Persistent fact violated!" << std::endl;
#endif
						continue;
					}
					
					const std::vector<const HEURISTICS::VariableDomain*>& action_variable_to_effect_mappings = old_transition->getActionVariableDomains();
					
					std::map<const Property*, std::vector<unsigned int>* >* precondition_property_mappings = new std::map<const Property*, std::vector<unsigned int>* >();
					std::map<const Property*, std::vector<unsigned int>* >* effect_property_mappings = new std::map<const Property*, std::vector<unsigned int>* >();
					std::vector<const HEURISTICS::VariableDomain*>* new_action_variable_to_effect_mappings = new std::vector<const HEURISTICS::VariableDomain*>();
					
					std::vector<const Property*>* new_preconditions = new std::vector<const Property*>();
					std::vector<const Property*>* new_effects = new std::vector<const Property*>();
					
					// Copy the action variables.
					for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_to_effect_mappings.begin(); ci != action_variable_to_effect_mappings.end(); ++ci)
					{
						new_action_variable_to_effect_mappings->push_back(new HEURISTICS::VariableDomain((*ci)->getVariableDomain()));
					}
					
					// Copy the mappings for the preconditions.
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
					std::cout << "Copy the mappings from: " << *old_transition << std::endl;
#endif
					for (std::vector<const Property*>::const_iterator ci = old_transition->getFromPropertyState().getProperties().begin(); ci != old_transition->getFromPropertyState().getProperties().end(); ++ci)
					{
						unsigned int from_node_property_index = std::distance(old_transition->getFromPropertyState().getProperties().begin(), ci);
						const Property* property = *ci;
						const std::vector<unsigned int>* mappings = old_transition->getMappingsOfProperty(*property, true);
						
						if (mappings != NULL)
						{
							const Property* precondition = merged_property_state->getProperties()[from_node_property_index + offsets[merged_property_state]];
							(*precondition_property_mappings)[precondition] = new std::vector<unsigned int>(*mappings);
							new_preconditions->push_back(precondition);
						}
					}
					
					// Copy the mappings for the effects.
					for (std::vector<const Property*>::const_iterator ci = old_transition->getToPropertyState().getProperties().begin(); ci != old_transition->getToPropertyState().getProperties().end(); ++ci)
					{
						unsigned int to_node_property_index = std::distance(old_transition->getToPropertyState().getProperties().begin(), ci);
						const Property* property = *ci;
						const std::vector<unsigned int>* mappings = old_transition->getMappingsOfProperty(*property, false);
						
						if (mappings != NULL)
						{
							const Property* effect = merged_to_property_state->getProperties()[to_node_property_index + offsets[merged_to_property_state]];
							(*effect_property_mappings)[effect] = new std::vector<unsigned int>(*mappings);
							new_effects->push_back(effect);
						}
					}

					PropertyStateTransition* merged_transition = new PropertyStateTransition(*merged_property_state, *merged_to_property_state, *new_preconditions, *new_effects, old_transition->getAction(), *precondition_property_mappings, *effect_property_mappings, *new_action_variable_to_effect_mappings);
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
					std::cout << "1New merged transition: " << *merged_transition << std::endl;
#endif
					all_merged_transition.push_back(merged_transition);
				}
			}
		
			for (std::vector<PropertyStateTransition*>::const_iterator ci = all_merged_transition.begin(); ci != all_merged_transition.end(); ++ci)
			{
				merged_property_state->addTransition(**ci);
			}
		}
	}
}

void PropertySpace::getMatchingFacts(std::vector<const Atom*>& matching_facts, const Property& property, const std::vector<const Atom*>& facts, const TypeManager& type_manager)
{
	for (std::vector<const Atom*>::const_iterator ci = facts.begin(); ci != facts.end(); ++ci)
	{
		const Atom* fact = *ci;
		
		if (fact->getPredicate().getName() != property.getPredicate().getName() ||
				fact->getArity() != property.getPredicate().getArity())
		{
			continue;
		}
		
		bool types_match = true;
		for (unsigned int term_index = 0; term_index < fact->getArity(); ++term_index)
		{
			const Type* precondition_type = fact->getPredicate().getTypes()[term_index];
			const Type* property_type = property.getPredicate().getTypes()[term_index];
			
			if (!precondition_type->isEqual(*property_type) &&
					!precondition_type->isSubtypeOf(*property_type) &&
					!precondition_type->isSupertypeOf(*property_type))
			{
				types_match = false;
				break;
			}
		}
		
		if (!types_match)
		{
			continue;
		}
		
		if (property.getIndex() != std::numeric_limits<unsigned int>::max())
		{
			std::vector<const Object*> objects;
			type_manager.getObjectsOfType(objects, *fact->getTerms()[property.getIndex()]->getType());
			
			// Check if this overlaps with the objects of the invariable.
			bool invariable_objects_overlap = false;
			for (std::vector<const Object*>::const_iterator ci = objects.begin(); ci != objects.end(); ++ci)
			{
				const Object* o = *ci;
				for (std::vector<const Object*>::const_iterator ci = property.getPropertyState().getPropertySpace().getObjects().begin(); ci != property.getPropertyState().getPropertySpace().getObjects().end(); ++ci)
				{
					if (*ci == o)
					{
						invariable_objects_overlap = true;
						break;
					}
				}
				
				if (invariable_objects_overlap)
				{
					break;
				}
			}
			
			if (!invariable_objects_overlap)
			{
				continue;
			}
		}
		
		matching_facts.push_back(fact);
	}
}

PropertySpace* PropertySpace::merge(const PropertySpace& lhs, const PropertySpace& rhs, const TypeManager& type_manager)
{
	// We can only merge property spaces iff
	// 1) The property spaces apply to the same objects.
	// 2) Both property spaces are property spaces (i.e. not attribute spaces).
	
	// Check if both property spaces apply to the same set of objects.
	bool shared = false;
	for (std::vector<const Object*>::const_iterator ci = lhs.objects_.begin(); ci != lhs.objects_.end(); ++ci)
	{
		const Object* lhs_objects = *ci;
		for (std::vector<const Object*>::const_iterator ci = rhs.objects_.begin(); ci != rhs.objects_.end(); ++ci)
		{
			const Object* rhs_objects = *ci;
			if (rhs_objects == lhs_objects)
			{
				shared = true;
				break;
			}
		}
		if (!shared) return NULL;
	}
	if (!shared) return NULL;

#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cout << "Merge the LHS: " << lhs << std::endl;
	std::cout << "and: " << rhs << std::endl;
#endif
	
	PropertySpace* new_property_space = new PropertySpace();
	new_property_space->objects_.insert(new_property_space->objects_.end(), lhs.objects_.begin(), lhs.objects_.end());
	
	std::multimap<const PropertyState*, PropertyState*> old_to_merged_property_state_mappings;
	std::map<const PropertyState*, unsigned int> lhs_offsets;
	std::map<const PropertyState*, unsigned int> rhs_offsets;
	
	// Merge all the property states.
	for (std::vector<PropertyState*>::const_iterator ci = lhs.property_states_.begin(); ci != lhs.property_states_.end(); ++ci)
	{
		const PropertyState* lhs_property_state = *ci;
		for (std::vector<PropertyState*>::const_iterator ci = rhs.property_states_.begin(); ci != rhs.property_states_.end(); ++ci)
		{
			const PropertyState* rhs_property_state = *ci;
			
			PropertyState* merged_property_state = new PropertyState(*new_property_space);
			old_to_merged_property_state_mappings.insert(std::make_pair(lhs_property_state, merged_property_state));
			old_to_merged_property_state_mappings.insert(std::make_pair(rhs_property_state, merged_property_state));

			for (std::vector<const Property*>::const_iterator ci = lhs_property_state->getProperties().begin(); ci != lhs_property_state->getProperties().end(); ++ci)
			{
				Property* new_property = new Property(*merged_property_state, (*ci)->getPredicate(), (*ci)->getIndex());
				merged_property_state->addProperty(*new_property);
			}
			lhs_offsets[merged_property_state] = 0;
			rhs_offsets[merged_property_state] = lhs_property_state->getProperties().size();
			for (std::vector<const Property*>::const_iterator ci = rhs_property_state->getProperties().begin(); ci != rhs_property_state->getProperties().end(); ++ci)
			{
				Property* new_property = new Property(*merged_property_state, (*ci)->getPredicate(), (*ci)->getIndex());
				merged_property_state->addProperty(*new_property);
			}

#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
			std::cout << "Mappings: (" << lhs_property_state << ")" << *lhs_property_state << "->" << *merged_property_state << "." << std::endl;
			std::cout << "Mappings: (" << rhs_property_state << ")" << *rhs_property_state << "->" << *merged_property_state << "." << std::endl;
#endif
			
			new_property_space->addPropertyState(*merged_property_state);
//			std::cout << *merged_property_state << std::endl;
		}
	}
	
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cout << "Merged property space: " << *new_property_space << std::endl;
#endif
	
	copyMergedTransitions(lhs, lhs_offsets, *new_property_space, old_to_merged_property_state_mappings, type_manager);
	copyMergedTransitions(rhs, rhs_offsets, *new_property_space, old_to_merged_property_state_mappings, type_manager);
	
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cout << "Merged property space after adding all the transitions:" << std::endl;
	for (std::vector<PropertyState*>::const_iterator ci = new_property_space->getPropertyStates().begin(); ci != new_property_space->getPropertyStates().end(); ++ci)
	{
		const PropertyState* property_state = *ci;
		std::cout << *property_state << std::endl;
		
		for (std::vector<const PropertyStateTransition*>::const_iterator ci = property_state->getTransitions().begin(); ci != property_state->getTransitions().end(); ++ci)
		{
			std::cout << **ci << std::endl;
		}
	}

	if (new_property_space != NULL)
	{
		std::cout << "Merged property space: " << *new_property_space << std::endl;
	}
#endif
	return new_property_space;
}



bool PropertySpace::violatesPrecondition(const Atom& precondition, unsigned int invariable_action_parameter_index, const PropertyStateTransition& old_transition, const PropertyState& merged_property_state)
{
/*
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cout << "Precondition: ";
	precondition.print(std::cout);
	std::cout << "." << std::endl;
#endif
*/
	unsigned int invariable_precondition_index = std::numeric_limits<unsigned int>::max();
	if (invariable_action_parameter_index != std::numeric_limits<unsigned int>::max())
	{
		for (unsigned int precondition_term_index = 0; precondition_term_index < precondition.getArity(); ++precondition_term_index)
		{
			if (precondition.getTerms()[precondition_term_index] == old_transition.getAction().getVariables()[invariable_action_parameter_index])
			{
				invariable_precondition_index = precondition_term_index;
				break;
			}
		}
	}
/*
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cout << "Invariable precondition term: " << invariable_precondition_index << "." << std::endl;
#endif
*/
	// Check if this precondition is part of this property state.
	for (std::vector<const Property*>::const_iterator ci = merged_property_state.getProperties().begin(); ci != merged_property_state.getProperties().end(); ++ci)
	{
		const Property* property = *ci;
/*
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
		std::cout << "Property: " << *property << "." << std::endl;
#endif
*/
		if (precondition.getArity() != property->getPredicate().getArity() ||
				precondition.getPredicate().getName() != property->getPredicate().getName() ||
				invariable_precondition_index != property->getIndex())
		{
/*
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
			std::cout << "Arity of name does not match. NEXT!" << std::endl;
#endif
*/
			continue;
		}
		
		bool types_match = true;
		for (unsigned int term_index = 0; term_index < property->getPredicate().getArity(); ++term_index)
		{
			const Type* property_type = property->getPredicate().getTypes()[term_index];
			const Type* precondition_type = precondition.getPredicate().getTypes()[term_index];
			
			if (!property_type->isEqual(*precondition_type) &&
					!property_type->isSubtypeOf(*precondition_type) &&
					!property_type->isSupertypeOf(*precondition_type))
			{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
//				std::cout << "The " << term_index << "th term does not match. NEXT!" << std::endl;
#endif
				types_match = false;
			}
		}
		
		if (types_match)
		{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
//			std::cout << "The precondition is part of the from node, no problem :)!" << std::endl;
#endif
			return false;
		}
	}
	
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
//	std::cout << "Precondition is not part of the merged property state!" << std::endl;
#endif
	
	// Check if it is part of another property state.
	for (std::vector<PropertyState*>::const_iterator ci = merged_property_state.getPropertySpace().getPropertyStates().begin(); ci != merged_property_state.getPropertySpace().getPropertyStates().end(); ++ci)
	{
		const PropertyState* property_state = *ci;
		if (&merged_property_state == property_state)
		{
			continue;
		}
		
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
//		std::cout << "Check the other property state: " << *property_state << "." << std::endl;
#endif
		
		for (std::vector<const Property*>::const_iterator ci = property_state->getProperties().begin(); ci != property_state->getProperties().end(); ++ci)
		{
			const Property* property = *ci;
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
//			std::cout << "Property: " << *property << "." << std::endl;
#endif
			if (precondition.getArity() != property->getPredicate().getArity() ||
					precondition.getPredicate().getName() != property->getPredicate().getName() ||
					invariable_precondition_index != property->getIndex())
			{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
//				std::cout << "Arity of name does not match!" << std::endl;
#endif
				continue;
			}
			
			bool types_match = true;
			for (unsigned int term_index = 0; term_index < property->getPredicate().getArity(); ++term_index)
			{
				const Type* property_type = property->getPredicate().getTypes()[term_index];
				const Type* precondition_type = precondition.getPredicate().getTypes()[term_index];
				
				if (!property_type->isEqual(*precondition_type) &&
						!property_type->isSubtypeOf(*precondition_type) &&
						!property_type->isSupertypeOf(*precondition_type))
				{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
//					std::cout << "The " << term_index << "th term does not match!" << std::endl;
#endif
					types_match = false;
				}
			}
			
			if (types_match)
			{
				return true;
			}
		}
	}
	
	return false;
}

bool PropertySpace::isPartOfPropertySpace(const Type& type)
{
	for (std::vector<const PropertySpace*>::const_iterator ci = all_property_spaces_.begin(); ci != all_property_spaces_.end(); ci++)
	{
		const PropertySpace* p_space = *ci;
		
		// Check if all the objects conform to the given type.
		bool all_objects_are_of_correct_type = true;
		for (std::vector<const Object*>::const_iterator ci = p_space->objects_.begin(); ci != p_space->objects_.end(); ci++)
		{
			const Object* object = *ci;
			if (!object->getType()->isEqual(type) && !object->getType()->isSubtypeOf(type))
			{
				all_objects_are_of_correct_type = false;
			}
		}
		
		if (all_objects_are_of_correct_type) return true;
	}
	return false;
}

bool PropertySpace::isBalanced(InvariableIndex index, const Predicate& predicate, const Type& type)
{
	for (std::vector<const PropertySpace*>::const_iterator ci = all_property_spaces_.begin(); ci != all_property_spaces_.end(); ci++)
	{
		const PropertySpace* p_space = *ci;
		
		// Check if all the objects conform to the given type.
		bool all_objects_are_of_correct_type = true;
		for (std::vector<const Object*>::const_iterator ci = p_space->objects_.begin(); ci != p_space->objects_.end(); ci++)
		{
			const Object* object = *ci;
			if (!object->getType()->isEqual(type) && !object->getType()->isSubtypeOf(type))
			{
				all_objects_are_of_correct_type = false;
			}
		}
		if (all_objects_are_of_correct_type && p_space->isBalanced(index, predicate)) return true;
	}
	return false;
}

const std::vector<const PropertySpace*>& PropertySpace::getAllPropertySpaces()
{
	return all_property_spaces_;
}

void PropertySpace::addTransitions(const PredicateManager& property_manager, const TypeManager& type_manager, const ActionManager& action_manager, const std::set<TIM::TransitionRule*>& rules)
{
#ifdef MYPOP_SAS_PLUS_PROPERTY_SPACE_COMMENT
	std::cout << "Add transitions to " << *this << std::endl;
#endif
	for (std::set<TIM::TransitionRule*>::const_iterator ci = rules.begin(); ci != rules.end(); ++ci)
	{
		const TIM::TransitionRule* tim_transition_rule = *ci;
		const Action& action = action_manager.getAction(*tim_transition_rule->byWhat());
		const TIM::PropertyState* tim_lhs_property_state = tim_transition_rule->getLHS();
		const TIM::PropertyState* tim_rhs_property_state = tim_transition_rule->getRHS();
		
		std::vector<PropertyState*> lhs_found_property_state;
		getPropertyStates(lhs_found_property_state, *tim_lhs_property_state);
		
		std::vector<PropertyState*> rhs_found_property_state;
		getPropertyStates(rhs_found_property_state, *tim_rhs_property_state);
		
		for (std::vector<PropertyState*>::const_iterator ci = lhs_found_property_state.begin(); ci != lhs_found_property_state.end(); ++ci)
		{
			PropertyState* lhs_property_state = *ci;
			
			std::vector<const Property*> unchanged_properties;
			std::vector<const Property*> preconditions;
			for (std::vector<const Property*>::const_iterator ci = lhs_property_state->getProperties().begin(); ci != lhs_property_state->getProperties().end(); ++ci)
			{
				const Property* property = *ci;
				bool is_present_in_lhs = false;
				for (TIM::PropertyState::PSIterator psi = tim_lhs_property_state->begin(); psi != tim_lhs_property_state->end(); ++psi)
				{
					if ((unsigned int)(*psi)->aPosn() == property->getIndex() && (*psi)->root()->getName() == property->getPredicate().getName())
					{
						is_present_in_lhs = true;
						break;
					}
				}
				
				if (!is_present_in_lhs)
				{
					unchanged_properties.push_back(property);
				}
				else
				{
					preconditions.push_back(property);
				}
			}
			
			for (std::vector<PropertyState*>::const_iterator ci = rhs_found_property_state.begin(); ci != rhs_found_property_state.end(); ++ci)
			{
				PropertyState* rhs_property_state = *ci;
				
				// Check that the properties which have not been removed are still there.
				std::vector<const Property*> effects;
				
				for (std::vector<const Property*>::const_iterator ci = rhs_property_state->getProperties().begin(); ci != rhs_property_state->getProperties().end(); ++ci)
				{
					const Property* effect = *ci;
					bool is_unchanged = false;
					for (std::vector<const Property*>::const_iterator ci = unchanged_properties.begin(); ci != unchanged_properties.end(); ++ci)
					{
						const Property* unchanged_property = *ci;
						if (*effect == *unchanged_property)
						{
							is_unchanged = true;
							break;
						}
					}
					
					if (!is_unchanged)
					{
						effects.push_back(effect);
					}
				}

				bool unchanged_properties_are_present = true;
				for (std::vector<const Property*>::const_iterator ci = unchanged_properties.begin(); ci != unchanged_properties.end(); ++ci)
				{
					const Property* unchanged_property = *ci;
					bool property_is_still_there = false;
					for (std::vector<const Property*>::const_iterator ci = rhs_property_state->getProperties().begin(); ci != rhs_property_state->getProperties().end(); ++ci)
					{
						if (*unchanged_property == **ci)
						{
							property_is_still_there = true;
							break;
						}
					}
					
					if (!property_is_still_there)
					{
						unchanged_properties_are_present = false;
					}
				}
				
				if (unchanged_properties_are_present)
				{
					lhs_property_state->addTransition(property_manager, type_manager, action, *rhs_property_state, preconditions, effects);
				}
			}
		}
	}
}

void PropertySpace::getPropertyStates(std::vector<PropertyState*>& found_property_state, const TIM::PropertyState& tim_property_state) const
{
	for (std::vector<PropertyState*>::const_iterator ci = property_states_.begin(); ci != property_states_.end(); ++ci)
	{
		PropertyState* property_state = *ci;
		
		std::vector<std::vector<const Property*> *> mapping;
		property_state->findMappings(mapping, tim_property_state);
		
		if (mapping.size() > 0)
		{
			found_property_state.push_back(property_state);
		}
	}
}

};

};
