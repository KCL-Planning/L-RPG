#include "property_space.h"

#include <vector>
#include "../predicate_manager.h"
#include "../formula.h"

namespace MyPOP {

namespace SAS_Plus {

std::vector<const Property*> Property::all_properties_;
	
/*****************************
 * Property state.
 ****************************/
/*PropertyState::PropertyState(const PropertySpace& property_space, const Property& property)
	: property_space_(&property_space)
{
	property_.push_back(&property);
}*/

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

std::ostream& operator<<(std::ostream& os, const PropertyState& property_state)
{
	os << "property state: ";
	for (std::vector<const Property*>::const_iterator ci = property_state.getProperties().begin(); ci != property_state.getProperties().end(); ci++)
	{
		os << **ci << ", ";
	}
	os << std::endl;
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
		for (std::vector<const PropertyState*>::const_iterator ci = property_state_->getPropertySpace().getPropertyStates().begin(); ci != property_state_->getPropertySpace().getPropertyStates().end(); ci++)
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
PropertySpace::PropertySpace()
{

}

PropertySpace::~PropertySpace()
{
	for (std::vector<const PropertyState*>::const_iterator ci = property_states_.begin(); ci != property_states_.end(); ci++)
	{
		delete *ci;
	}
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

std::ostream& operator<<(std::ostream& os, const PropertySpace& property_space)
{
	std::cout << "The property space: ";
	for (std::vector<const PropertyState*>::const_iterator ci = property_space.getPropertyStates().begin(); ci != property_space.getPropertyStates().end(); ci++)
	{
		os << "* " << **ci << std::endl;
	}
	return os;
}

};

};
