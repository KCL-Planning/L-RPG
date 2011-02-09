#include "property_space.h"

#include <vector>
#include "../predicate_manager.h"

namespace MyPOP {

namespace SAS_Plus {

/*****************************
 * Property state.
 ****************************/
PropertyState::PropertyState(const PropertySpace& property_space, Property& property)
	: property_space_(&property_space)
{
	property_.push_back(&property);
}

/*PropertyState::PropertyState(const PropertySpace& property_space, const std::vector<const Property*>& properties)
	: property_space_(&property_space)
{
	property_.insert(property_.end(), properties.begin(), properties.end());
}*/

PropertyState::PropertyState(const PropertySpace& property_space, const std::vector<std::pair<const Predicate*, InvariableIndex> >& properties)
	: property_space_(&property_space)
{
	for (std::vector<std::pair<const Predicate*, InvariableIndex> >::const_iterator ci = properties.begin(); ci != properties.end(); ci++)
	{
		property_.push_back(new Property(*this, *(*ci).first, (*ci).second));
	}
}

bool PropertyState::contains(InvariableIndex index, const Predicate& predicate) const
{
	for (std::vector<Property*>::const_iterator ci = property_.begin(); ci != property_.end(); ci++)
	{
		const Property* property = *ci;
		if (property->getPredicate().getName() == predicate.getName() && property->getPredicate().getArity() == predicate.getArity() && property->getIndex() == index)
		{
			return true;
		}
	}
	return false;
}

const std::vector<Property*>& PropertyState::getProperties() const
{
	return property_;
}

const PropertySpace& PropertyState::getPropertySpace() const
{
	return *property_space_;
}


/*****************************
 * Property.
 ****************************/
Property::Property(const PropertyState& property_state, const Predicate& predicate, InvariableIndex index)
	: property_state_(&property_state), predicate_(&predicate), index_(index)
{

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
	
	if (&property_state_->getPropertySpace() == &property->property_state_->getPropertySpace() &&
			property_state_ != property->property_state_)
	{
		return true;
	}
	
	return false;
}

/*****************************
 * Property space.
 ****************************/
PropertySpace::PropertySpace()
{

}

bool PropertySpace::contains(InvariableIndex index, const Predicate& predicate) const
{
	for (std::vector<const PropertyState*>::const_iterator ci = property_states_.begin(); ci != property_states_.end(); ci++)
	{
		const PropertyState* property_state = *ci;
		if (property_state->contains(index, predicate))
		{
			return true;
		}
	}
	return false;
}

void PropertySpace::addPropertyState(const PropertyState& property_state)
{
	property_states_.push_back(&property_state);
}
	
const std::vector<const PropertyState*>& PropertySpace::getPropertyStates() const
{
	return property_states_;
}

//std::ostream& operator<<(std::ostream& os, const PropertyState& property_state);

};

};
