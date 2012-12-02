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
class TermManager;
class Type;

namespace SAS_Plus {

class Property;
class PropertyState;
class PropertySpace;

class PropertyStateTransition
{
public:
	PropertyStateTransition(PropertyState& lhs, PropertyState& rhs, const Action& action);
	
	PropertyState& getFromPropertyState() const { return *lhs_property_state_; }
	PropertyState& getToPropertyState() const { return *rhs_property_state_; }
	const Action& getAction() const { return *action_; }
	
private:
	PropertyState* lhs_property_state_;
	PropertyState* rhs_property_state_;
	const Action* action_;
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
	
	void addTransition(const MyPOP::Action& action, PropertyState& rhs_property_state);
	
	const std::vector<const PropertyStateTransition*>& getTransitions() const { return transitions_; }
	
private:
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
	void addTransitions(const ActionManager& action_manager, const std::set<TIM::TransitionRule*>& rules);
	
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
