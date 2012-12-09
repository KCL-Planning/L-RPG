#include "property_space.h"

#include <vector>
#include "predicate_manager.h"
#include "formula.h"
#include "term_manager.h"
#include "action_manager.h"
#include "type_manager.h"
#include <parser_utils.h>
#include <heuristics/fact_set.h>

namespace MyPOP {

namespace SAS_Plus {


PropertyStateTransition::PropertyStateTransition(MyPOP::SAS_Plus::PropertyState& lhs, MyPOP::SAS_Plus::PropertyState& rhs, const std::vector< const MyPOP::SAS_Plus::Property* >& preconditions, const std::vector< const MyPOP::SAS_Plus::Property* >& added_properties, const MyPOP::Action& action, std::pair< std::map< const MyPOP::SAS_Plus::Property*, std::vector< unsigned int >* >*, const std::vector< const MyPOP::HEURISTICS::VariableDomain* >* > mapping)
	: lhs_property_state_(&lhs), rhs_property_state_(&rhs), preconditions_(preconditions), added_properties_(added_properties), action_(&action), property_to_action_variable_index_(mapping.first), action_variable_domains_(mapping.second)
{
	
}
std::vector<const Property*> Property::all_properties_;
	
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

void PropertyState::addTransition(const PredicateManager& property_manager, const TypeManager& type_manager, const MyPOP::Action& action, PropertyState& rhs_property_state, const std::vector<const Property*>& preconditions, const std::vector<const Property*>& added_properties)
{
//	std::cout << "ADD TRANSITION: " << action.getPredicate() << std::endl << *this << std::endl << "=== TO ===" << std::endl << rhs_property_state << std::endl;
	for (std::vector<const PropertyStateTransition*>::const_iterator ci = transitions_.begin(); ci != transitions_.end(); ++ci)
	{
		if (&(*ci)->getAction() == &action && &(*ci)->getToPropertyState() == &rhs_property_state)
		{
			return;
		}
	}
	
	if (this == &rhs_property_state)
	{
		std::cout << "Cyclic transition!!!" << std::endl;
	}
	
	// Update the types.
	std::map<const Property*, std::vector<unsigned int>* > bindings_to_action_variables;
	std::vector<const HEURISTICS::VariableDomain*> action_variable_types;
	for (std::vector<const Variable*>::const_iterator ci = action.getVariables().begin(); ci != action.getVariables().end(); ++ci)
	{
		const Variable* variable = *ci;
		std::vector<const Object*> objects_of_type;
		type_manager.getObjectsOfType(objects_of_type, *variable->getType());
		action_variable_types.push_back(new HEURISTICS::VariableDomain(objects_of_type));
	}
	std::pair<std::map<const Property*, std::vector<unsigned int>* >*, const std::vector<const HEURISTICS::VariableDomain*>* > mapping = getMappings(type_manager, preconditions, added_properties, action, bindings_to_action_variables, action_variable_types, 0);
	assert (mapping.first != NULL);
	transitions_.push_back(new PropertyStateTransition(*this, rhs_property_state, preconditions, added_properties, action, mapping));
}

std::pair<std::map<const Property*, std::vector<unsigned int>* >*, const std::vector<const HEURISTICS::VariableDomain*>* > PropertyState::getMappings(const TypeManager& type_manager, const std::vector<const Property*>& precondition_properties, const std::vector<const Property*>& effects_properties, const Action& action, const std::map<const Property*, std::vector<unsigned int>* >& bindings_to_action_variables, const std::vector<const HEURISTICS::VariableDomain*>& action_variable_types, unsigned int property_index_to_process)
{
	std::cout << "[PropertyState::getMappings] " << bindings_to_action_variables.size() << std::endl;
	const Property* property_to_process = NULL;
//	bool is_precondition = true;
	
	std::vector<const Atom*> action_facts;
	
	// Found a complete assignment!
	if (property_index_to_process == precondition_properties.size() + effects_properties.size())
	{
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
			
			std::vector<unsigned int>* mappings_to_action_variable = (*bindings_to_action_variables.find(*ci)).second;
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
			
			std::vector<unsigned int>* mappings_to_action_variable = (*bindings_to_action_variables.find(*ci)).second;
			for (std::vector<unsigned int>::const_iterator ci = mappings_to_action_variable->begin(); ci != mappings_to_action_variable->end(); ++ci)
			{
				std::cout << *action_variable_types[*ci] << " ";
			}
			std::cout << "." << std::endl;
		}
		
		std::map<const Property*, std::vector<unsigned int>* >* bindings_to_action_variables_copy = new std::map<const Property*, std::vector<unsigned int>* >();
		for (std::map<const Property*, std::vector<unsigned int>* >::const_iterator ci = bindings_to_action_variables.begin(); ci != bindings_to_action_variables.end(); ++ci)
		{
			std::vector<unsigned int>* bindings = new std::vector<unsigned int>(*(*ci).second);
			(*bindings_to_action_variables_copy)[(*ci).first] = bindings;
		}
		
		return std::make_pair(bindings_to_action_variables_copy, new std::vector<const HEURISTICS::VariableDomain*>(action_variable_types));
	}
	else if (property_index_to_process < precondition_properties.size())
	{
		property_to_process = precondition_properties[property_index_to_process];
		Utility::convertFormula(action_facts, &action.getPrecondition());
	}
	else
	{
		property_to_process = effects_properties[property_index_to_process - precondition_properties.size()];
//		is_precondition = false;
		action_facts = action.getEffects();
	}
	
	for (std::vector<const Atom*>::const_iterator ci = action_facts.begin(); ci != action_facts.end(); ++ci)
	{
		const Atom* action_fact = *ci;
		if (action_fact->getArity() != property_to_process->getPredicate().getArity() ||
		    action_fact->getPredicate().getName() != property_to_process->getPredicate().getName())
		{
			continue;
		}
		
		// Can this be 'unified' with the property at hand.
		std::vector<unsigned int> action_variable_mappings;
		bool terms_match = true;
		
		// Update the varialbe domains of the action.
		std::vector<const HEURISTICS::VariableDomain*> new_action_variable_types;
		for (std::vector<const HEURISTICS::VariableDomain*>::const_iterator ci = action_variable_types.begin(); ci != action_variable_types.end(); ++ci)
		{
			new_action_variable_types.push_back(new HEURISTICS::VariableDomain(**ci));
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
			
			// Can this term unify with the term_index's index of the property.
			const Type& action_type = *action_term->getType();
			const Type& property_type = *property_to_process->getPredicate().getTypes()[term_index];
			
			if (!action_type.isEqual(property_type) && !action_type.isSubtypeOf(property_type) && !action_type.isSupertypeOf(property_type))
			{
				terms_match = false;
				break;
			}
			
			// Update the variable domain.
			std::vector<const Object*> objects_of_type;
			type_manager.getObjectsOfType(objects_of_type, property_type);
			HEURISTICS::VariableDomain type_variable_domain(objects_of_type);
			
			HEURISTICS::VariableDomain* intersection = new HEURISTICS::VariableDomain();
			type_variable_domain.getIntersection(*intersection, *new_action_variable_types[matching_action_variable_index]);
			delete new_action_variable_types[matching_action_variable_index];
			new_action_variable_types[matching_action_variable_index] = intersection;
		}
		
		if (!terms_match)
		{
			continue;
		}
		
		// Check if no bindings are violated.
		bool bindings_violated = false;
		for (std::map<const Property*, std::vector<unsigned int>* >::const_iterator ci = bindings_to_action_variables.begin(); ci != bindings_to_action_variables.end(); ++ci)
		{
			const Property* all_ready_processed_property = (*ci).first;
			const std::vector<unsigned int>* bindings = (*ci).second;
			
			// Check if the invariables are identical.
			unsigned int variable_index = (*bindings)[all_ready_processed_property->getIndex()];
			if (variable_index != action_variable_mappings[property_to_process->getIndex()])
			{
				bindings_violated = true;
				break;
			}
		}
		
		if (bindings_violated)
		{
			continue;
		}
		
		std::map<const Property*, std::vector<unsigned int>* > new_bindings_to_action_variables(bindings_to_action_variables);
//		std::map<const Property*, std::vector<unsigned int>* >::const_iterator iterator = new_bindings_to_action_variables.find(property_to_process);
		new_bindings_to_action_variables[property_to_process] = &action_variable_mappings;
		
		std::pair<std::map<const Property*, std::vector<unsigned int>* >*, const std::vector<const HEURISTICS::VariableDomain*>* > mapping = getMappings(type_manager, precondition_properties, effects_properties, action, new_bindings_to_action_variables, new_action_variable_types, property_index_to_process + 1);
		if (mapping.first != NULL)
		{
			return mapping;
		}
	}
	return std::make_pair(static_cast<std::map<const Property*, std::vector<unsigned int>* >*>(NULL), static_cast<const std::vector<const HEURISTICS::VariableDomain*>*>(NULL));
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
	std::cout << "The property space: ";
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

PropertySpace* PropertySpace::merge(const PropertySpace& lhs, const PropertySpace& rhs)
{
	// We can only merge property spaces iff
	// 1) The property spaces apply to the same objects.
	// 2) Both property spaces are property spaces (i.e. not attribute spaces).
	
	// Check if both property spaces apply to the same set of objects.
	for (std::vector<const Object*>::const_iterator ci = lhs.objects_.begin(); ci != lhs.objects_.end(); ++ci)
	{
		const Object* lhs_objects = *ci;
		bool shared = false;
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
	
/*
	PropertySpace* new_property_space = new PropertySpace();
	new_property_space->objects_.insert(new_property_space->objects_.end(), lhs.objects_.begin(), lhs.objects_.end());
	
	std::map<const PropertyState*, PropertyState*> old_to_merged_property_state_mappings;
	
	// Merge all the property states.
	for (std::vector<PropertyState*>::const_iterator ci = lhs.property_states_.begin(); ci != lhs.property_states_.end(); ++ci)
	{
		const PropertyState* lhs_property_state = *ci;
		for (std::vector<PropertyState*>::const_iterator ci = rhs.property_states_.begin(); ci != rhs.property_states_.end(); ++ci)
		{
			const PropertyState* rhs_property_state = *ci;
			
			PropertyState* merged_property_state = new PropertyState(*new_property_space);
			old_to_merged_property_state_mappings[lhs_property_state] = merged_property_state;
			old_to_merged_property_state_mappings[rhs_property_state] = merged_property_state;
			for (std::vector<const Property*>::const_iterator ci = lhs_property_state->getProperties().begin(); ci != lhs_property_state->getProperties().end(); ++ci)
			{
				Property* new_property = new Property(*merged_property_state, (*ci)->getPredicate(), (*ci)->getIndex());
				merged_property_state->addProperty(*new_property);
			}
			for (std::vector<const Property*>::const_iterator ci = rhs_property_state->getProperties().begin(); ci != rhs_property_state->getProperties().end(); ++ci)
			{
				Property* new_property = new Property(*merged_property_state, (*ci)->getPredicate(), (*ci)->getIndex());
				merged_property_state->addProperty(*new_property);
			}
			
			new_property_space->addPropertyState(*merged_property_state);
		}
	}
	
	// Copy the transitions.
	for (std::vector<PropertyState*>::const_iterator ci = lhs.property_states_.begin(); ci != lhs.property_states_.end(); ++ci)
	{
		const PropertyState* org_property_state = *ci;
		PropertyState* merged_property_state = old_to_merged_property_state_mappings[org_property_state];
		
		for (std::vector<const PropertyStateTransition*>::const_iterator ci = org_property_state->getTransitions().begin(); ci != org_property_state->getTransitions().end(); ++ci)
		{
			merged_property_state->addTransition((*ci)->getAction(), *old_to_merged_property_state_mappings[&(*ci)->getToPropertyState()]);
		}
	}
	
	for (std::vector<PropertyState*>::const_iterator ci = rhs.property_states_.begin(); ci != rhs.property_states_.end(); ++ci)
	{
		const PropertyState* org_property_state = *ci;
		PropertyState* merged_property_state = old_to_merged_property_state_mappings[org_property_state];
		
		for (std::vector<const PropertyStateTransition*>::const_iterator ci = org_property_state->getTransitions().begin(); ci != org_property_state->getTransitions().end(); ++ci)
		{
			merged_property_state->addTransition((*ci)->getAction(), *old_to_merged_property_state_mappings[&(*ci)->getToPropertyState()]);
		}
	}
	
	return new_property_space;
*/
	return NULL;
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
//	std::cout << "Add transitions to " << *this << std::endl;
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
