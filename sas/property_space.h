#ifndef SAS_PLUS_PROPERTY_SPACE_H
#define SAS_PLUS_PROPERTY_SPACE_H

#include <vector>
#include <iostream>

#include "VALfiles/TimSupport.h"
#include "dtg_types.h"
#include <plan_types.h>

namespace MyPOP {

class Action;
class ActionManager;
class Atom;
class Bindings;
class Object;
class Predicate;
class PredicateManager;
class TermManager;
class Type;
class TypeManager;

namespace HEURISTICS {
class VariableDomain;
};

namespace SAS_Plus {

class Property;
class PropertyState;
class PropertySpace;

class PropertyStateTransition
{
public:
	PropertyStateTransition(PropertyState& lhs, PropertyState& rhs, const std::vector<const Property*>& preconditions, const std::vector<const Property*>& added_properties, const Action& action, const std::map<const Property*, std::vector<unsigned int>* >& precondition_properties_to_action_variable_mappings, const std::map<const Property*, std::vector<unsigned int>* >& effect_properties_to_action_variable_mappings, const std::vector<const HEURISTICS::VariableDomain*>& action_variable_to_effect_mappings);
	
	PropertyState& getFromPropertyState() const { return *lhs_property_state_; }
	PropertyState& getToPropertyState() const { return *rhs_property_state_; }
	const std::vector<const Property*>& getPreconditions() const { return preconditions_; }
	const std::vector<const Property*>& getAddedProperties() const { return added_properties_; }
	
//	const std::map<const Property*, std::vector<unsigned int>* >& getMappingToActionVariables() const { return *property_to_action_variable_index_; }
	const std::vector<const HEURISTICS::VariableDomain*>& getActionVariableDomains() const { return *action_variable_domains_; }
	
	const std::vector<unsigned int>* getMappingsOfProperty(const Property& property, bool is_precondition) const;
	
	const Action& getAction() const { return *action_; }
	
private:
	PropertyState* lhs_property_state_;
	PropertyState* rhs_property_state_;
	
	std::vector<const Property*> preconditions_;
	std::vector<const Property*> added_properties_;

	const Action* action_;
	
	const std::map<const Property*, std::vector<unsigned int>* >* precondition_properties_to_action_variable_index_;
	const std::map<const Property*, std::vector<unsigned int>* >* effect_properties_to_action_variable_index_;
	const std::vector<const HEURISTICS::VariableDomain*>* action_variable_domains_;
	
	friend std::ostream& operator<<(std::ostream& os, const PropertyStateTransition& transition);
};

std::ostream& operator<<(std::ostream& os, const PropertyStateTransition& transition);

struct FoundVariableMappings
{
	FoundVariableMappings(std::vector<const HEURISTICS::VariableDomain*>& action_variable_assignments, std::map<const Property*, std::vector<unsigned int>* >& precondition_mappings, std::map<const Property*, std::vector<unsigned int>* >& effect_mappings)
		: action_variable_assignments_(&action_variable_assignments), precondition_mappings_(&precondition_mappings), effect_mappings_(&effect_mappings)
	{
		
	}
	
	std::vector<const HEURISTICS::VariableDomain*>* action_variable_assignments_;
	std::map<const Property*, std::vector<unsigned int>* >* precondition_mappings_;
	std::map<const Property*, std::vector<unsigned int>* >* effect_mappings_;
};

/**
 * Property state.
 */
class PropertyState
{
public:
	PropertyState(const PropertySpace& property_space);
	
	PropertyState(const PropertySpace& property_space, const std::vector<std::pair<const Predicate*, InvariableIndex> >& properties);
	
	~PropertyState();
	
	void findMappings(std::vector<std::vector<const Property*>* >& mappings, const TIM::PropertyState& tim_property_state) const;
	void findMappings(std::vector<std::vector<const Property*>* >& mappings, std::vector<const Property*>& current_mapping, const TIM::PropertyState& tim_property_state, unsigned int index) const;
	
	bool contains(InvariableIndex index, const Predicate& predicate) const;
	
	const std::vector<const Property*>& getProperties() const;
	
	const PropertySpace& getPropertySpace() const;
	
	void addProperty(const Property& property) { property_.push_back(&property); }
	
	void addTransition(const PropertyStateTransition& transition);
	
	void addTransition(const PredicateManager& property_manager, const TypeManager& type_manager, const MyPOP::Action& action, PropertyState& rhs_property_state, const std::vector<const Property*>& preconditions, const std::vector<const Property*>& added_properties);
	
	const std::vector<const PropertyStateTransition*>& getTransitions() const { return transitions_; }
	
private:
	
	FoundVariableMappings* getMappings(const TypeManager& type_manager, const std::vector<const Property*>& precondition_properties, const std::vector<const Property*>& effects_properties, const Action& action, const std::vector<const HEURISTICS::VariableDomain*>& action_variable_assignemnts, unsigned int property_index_to_process, std::map<const Property*, std::vector<unsigned int>* >& precondition_mappings, std::map<const Property*, std::vector<unsigned int>* >& effect_mappings);
	
	const PropertySpace* property_space_;
	std::vector<const Property*> property_;
	std::vector<const PropertyStateTransition*> transitions_;
};

class Property
{
public:
	Property(const PropertyState& property_state, const Predicate& predicate, InvariableIndex index);
	
	const PropertyState& getPropertyState() const;
	
	const Predicate& getPredicate() const;
	
	void setPredicate(const Predicate& predicate);
	
	/**
	 * Return the index which is marked as invariable.
	 */
	InvariableIndex getIndex() const;
	
	bool isMutexWith(const Property* property) const;
	
	bool operator==(const Property& property) const;
	
	static void getProperties(std::vector<const Property*>& result, const Atom& atom);
	
	static const std::vector<const Property*>& getAllProperties();
	
private:
	const PropertyState* property_state_;
	const Predicate* predicate_;
	InvariableIndex index_;
	
	static std::vector<const Property*> all_properties_;
	
	static void addProperty(const Property& property);
};

/**
 * The property space holds a balanced et of property states.
 */
class PropertySpace
{
public:
	
	static PropertySpace& createPropertySpace(const TermManager& term_manager, TIM::PropertySpace::OIterator begin, TIM::PropertySpace::OIterator end);
	static PropertySpace& createAttributeSpace();
	
	~PropertySpace();
	
	void addPropertyState(PropertyState& property_state);
	
	const std::vector<PropertyState*>& getPropertyStates() const;
	void getPropertyStates(std::vector<PropertyState*>& found_property_state, const TIM::PropertyState& tim_property_state) const;
	
	bool isPropertySpace() const { return is_property_space_; }
	
	static void removeAllPropertySpaces();
	
	/**
	 * Merge the given property space with this property space.
	 */
	static PropertySpace* merge(const PropertySpace& lhs, const PropertySpace& rhs);
	
	/**
	 * Check if there is a property space this type is a part of.
	 */
	static bool isPartOfPropertySpace(const Type& type);
	
	static bool isBalanced(InvariableIndex index, const Predicate& predicate, const Type& type);
	
	const std::vector<const Object*>& getObjects() const { return objects_; }
	
	static const std::vector<const PropertySpace*>& getAllPropertySpaces();
	void addTransitions(const PredicateManager& property_manager, const TypeManager& type_manager, const ActionManager& action_manager, const std::set<TIM::TransitionRule*>& rules);
	
private:
	
	bool isBalanced(InvariableIndex index, const Predicate& predicate) const;
	
	bool contains(const Object& object) const;
	
	/**
	 * Create a property space which transition contains rules for the given objects.
	 */
	PropertySpace(const TermManager& term_manager, TIM::PropertySpace::OIterator begin, TIM::PropertySpace::OIterator end);
	
	/**
	 * Create an attribute space.
	 */
	PropertySpace();
	
	// Flag which tells us if this is a property or attribute space.
	bool is_property_space_;
	
	std::vector<PropertyState*> property_states_;
	std::vector<const Object*> objects_;
	
	static std::vector<const PropertySpace*> all_property_spaces_;
};

std::ostream& operator<<(std::ostream& os, const Property& property);
std::ostream& operator<<(std::ostream& os, const PropertySpace& property_space);
std::ostream& operator<<(std::ostream& os, const PropertyState& property_state);

};

};

#endif
