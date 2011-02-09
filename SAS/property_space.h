#ifndef SAS_PLUS_PROPERTY_SPACE_H
#define SAS_PLUS_PROPERTY_SPACE_H

#include <vector>

#include "dtg_types.h"

namespace MyPOP {

class Predicate;

namespace SAS_Plus {

class Property;
class PropertySpace;

/**
 * Property state.
 */
class PropertyState
{
public:
	PropertyState(const PropertySpace& property_space, Property& property);
	
	//PropertyState(const PropertySpace& property_space, const std::vector<const Property*>& properties);
	
	PropertyState(const PropertySpace& property_space, const std::vector<std::pair<const Predicate*, InvariableIndex> >& properties);
	
	bool contains(InvariableIndex index, const Predicate& predicate) const;
	
	const std::vector<Property*>& getProperties() const;
	
	const PropertySpace& getPropertySpace() const;
	
private:
	const PropertySpace* property_space_;
	std::vector<Property*> property_;
};

class Property
{
public:
	Property(const PropertyState& property_state, const Predicate& predicate, InvariableIndex index);
	
	const PropertyState& getPropertyState() const;
	
	const Predicate& getPredicate() const;
	
	void setPredicate(const Predicate& predicate);
	
	InvariableIndex getIndex() const;
	
	bool isMutexWith(const Property* property) const;
	
private:
	const PropertyState* property_state_;
	const Predicate* predicate_;
	InvariableIndex index_;
};

/**
 * The property space holds a balanced et of property states.
 */
class PropertySpace
{
public:
	PropertySpace();
	
	void addPropertyState(const PropertyState& property_state);
	
	const std::vector<const PropertyState*>& getPropertyStates() const;
	
	bool contains(InvariableIndex index, const Predicate& predicate) const;
	
private:
	std::vector<const PropertyState*> property_states_;
};

//std::ostream& operator<<(std::ostream& os, const PropertyState& property_state);

};

};

#endif
