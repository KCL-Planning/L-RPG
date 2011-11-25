#ifndef SAS_PLUS_PROPERTY_SPACE_H
#define SAS_PLUS_PROPERTY_SPACE_H

#include <vector>
#include <iostream>

#include "dtg_types.h"
#include <plan_types.h>

namespace MyPOP {

class Atom;
class Bindings;
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
	PropertyState(const PropertySpace& property_space, const Property& property);
	
	PropertyState(const PropertySpace& property_space, const std::vector<std::pair<const Predicate*, InvariableIndex> >& properties);
	
	~PropertyState();
	
	bool contains(InvariableIndex index, const Predicate& predicate) const;
	
	const std::vector<const Property*>& getProperties() const;
	
	const PropertySpace& getPropertySpace() const;
	
private:
	const PropertySpace* property_space_;
	std::vector<const Property*> property_;
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
	PropertySpace();
	
	~PropertySpace();
	
	void addPropertyState(const PropertyState& property_state);
	
	const std::vector<const PropertyState*>& getPropertyStates() const;
	
	bool contains(InvariableIndex index, const Predicate& predicate) const;
	
private:
	std::vector<const PropertyState*> property_states_;
};

std::ostream& operator<<(std::ostream& os, const Property& property);
std::ostream& operator<<(std::ostream& os, const PropertySpace& property_space);
std::ostream& operator<<(std::ostream& os, const PropertyState& property_state);

};

};

#endif
