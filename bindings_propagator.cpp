#include "bindings_propagator.h"
#include "plan_bindings.h"
#include "pointers.h"
#include "plan.h"
#include "term_manager.h"

namespace MyPOP {

bool SimpleBindingsPropagator::removeObjectFromUnequalDomains(Bindings& bindings, VariableDomain& variable_domain, const Object& object) const
{
	assert (variable_domain.getDomain().size() == 1);
	assert (variable_domain.getDomain()[0] == &object);
	const std::vector<VariableDomain*>& unequal_variables = variable_domain.getUnequalVariables();

	for (std::vector<VariableDomain*>::const_iterator ci = unequal_variables.begin(); ci != unequal_variables.end(); ci++)
	{
		const std::vector<std::pair<StepID, const Variable*> >& equal_variables = (*ci)->getEqualVariables();
//		ObjectBinding ob(equal_variables[0].first, *equal_variables[0].second, object, false);
		if (!equal_variables[0].second->makeDomainUnequalTo(equal_variables[0].first, object, Step::INVALID_STEP, bindings))
		{
			return false;
		}
/*		if (!bindings.addBinding(ob))
		{
			return false;
		}
*/
	}

	return true;
}

bool SimpleBindingsPropagator::propagateAfterMakeEqual(Bindings& bindings, VariableDomain& variable_domain, const VariableDomain& ) const
{
	if (variable_domain.getDomain().size() == 0)
	{
		return false;
	}
	assert (variable_domain.getDomain().size() != 0);
	// If a domain is made unequal, check if either has only a single object in their variable domain and propagate this.
	if (variable_domain.getDomain().size() == 1)
	{
		return propagateAfterMakeEqual(bindings, variable_domain, *variable_domain.getDomain()[0]);
	}
	
	return true;
}

bool SimpleBindingsPropagator::propagateAfterMakeEqual(Bindings& bindings, VariableDomain& variable_domain, const Object& object) const
{
	if (variable_domain.getDomain().size() == 0)
	{
		return false;
	}
	// After a domain is made equal to a single object, remove this value from all variable domains which are unequal to
	// this one.
	if (!removeObjectFromUnequalDomains(bindings, variable_domain, object))
	{
		return false;
	}
	return true;
}

bool SimpleBindingsPropagator::propagateAfterMakeEqual(Bindings& bindings, VariableDomain& variable_domain, const std::vector<const Object*>& objects) const
{
	if (variable_domain.getDomain().size() == 0)
	{
		return false;
	}

	// After a domain is made equal to a single object, remove this value from all variable domains which are unequal to
	// this one.
	if ((variable_domain.getDomain().size() == 1))
	{
		if (!removeObjectFromUnequalDomains(bindings, variable_domain, *variable_domain.getDomain()[0]))
		{
			return false;
		}
	}
	return true;
}

bool SimpleBindingsPropagator::propagateAfterMakeUnequal(Bindings& bindings, VariableDomain& variable_domain1, VariableDomain& variable_domain2) const
{
	if (variable_domain1.getDomain().size() == 0 || variable_domain2.getDomain().size() == 0)
	{
		return false;
	}
	
	// If a domain is made unequal, check if either has only a single object in their variable domain and propagate this.
	if (variable_domain1.getDomain().size() == 1)
	{
		//ObjectBinding ob(variable_domain2.getStep(), variable_domain2.getVariable(), *variable_domain1.getDomain()[0], false);
		//if (!bindings.addBinding(ob))
		if (!removeObjectFromUnequalDomains(bindings, variable_domain1, *variable_domain1.getDomain()[0]))
		{
			return false;
		}
	}

	if (variable_domain2.getDomain().size() == 1)
	{
//		ObjectBinding ob(variable_domain1.getStep(), variable_domain1.getVariable(), *variable_domain2.getDomain()[0], false);
//		if (!bindings.addBinding(ob))
		if (!removeObjectFromUnequalDomains(bindings, variable_domain2, *variable_domain2.getDomain()[0]))
		{
			return false;
		}
	}
	
	return true;
}

bool SimpleBindingsPropagator::propagateAfterMakeUnequal(Bindings& bindings, VariableDomain& variable_domain, const Object& object) const
{
	if (variable_domain.getDomain().size() == 0)
	{
		return false;
	}

	// If the domain only has a single object remaining, prune this from the variable domains which are unequal to it.
	if (variable_domain.getDomain().size() == 1)
	{
//		ObjectBinding ob(variable_domain.getStep(), variable_domain.getVariable(), object, false);
//		if (!bindings.addBinding(ob))
//		if (!removeObjectFromUnequalDomains(bindings, variable_domain, object))
		if (!removeObjectFromUnequalDomains(bindings, variable_domain, *variable_domain.getDomain()[0]))
		{
			return false;
		}
	}
	return true;
}

bool SimpleBindingsPropagator::propagateAfterMakeUnequal(Bindings& bindings, VariableDomain& variable_domain, const std::vector<const Object*>& objects) const
{
	if (variable_domain.getDomain().size() == 0)
	{
		return false;
	}

	// If the domain only has a single object remaining, prune this from the variable domains which are unequal to it.
	if (variable_domain.getDomain().size() == 1)
	{
//		ObjectBinding ob(variable_domain.getStep(), variable_domain.getVariable(), object, false);
//		if (!bindings.addBinding(ob))
//		if (!removeObjectFromUnequalDomains(bindings, variable_domain, object))
		if (!removeObjectFromUnequalDomains(bindings, variable_domain, *variable_domain.getDomain()[0]))
		{
			return false;
		}
	}
	return true;
}

};
