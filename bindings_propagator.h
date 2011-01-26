#ifndef MYPOP_BINDINGS_PROPAGATOR_H
#define MYPOP_BINDINGS_PROPAGATOR_H

#include <vector>

namespace MyPOP {

class Bindings;
class VariableDomain;
class Object;

/**
 * It is the sole purpose of the propagator to check if the imposed bindings are valid. No other part of the
 * planner does that. After the bindings have been added the functions below will be called appropriately. If,
 * during the pruning stage, a domain becomes empty the function must return false, true otherwise.
 */
class BindingsPropagator
{
public:
	// Called after the Bindings::merge function.
	virtual bool propagateAfterMakeEqual(Bindings& bindings, VariableDomain& vd, const VariableDomain& vd2) const = 0;
	
	// Called after the Bindings::assign function.
	virtual bool propagateAfterMakeEqual(Bindings& bindings, VariableDomain& vd, const Object& object) const = 0;

	// Called after the Bindings::assign function.
	virtual bool propagateAfterMakeEqual(Bindings& bindings, VariableDomain& vd, const std::vector<const Object*>& objects) const = 0;
	
	// Called after the Bindings::makeDistinct function.
	virtual bool propagateAfterMakeUnequal(Bindings& bindings, VariableDomain& vd, VariableDomain& vd2) const = 0;
	
	// Called after the Bindings::unassign function.
	virtual bool propagateAfterMakeUnequal(Bindings& bindings, VariableDomain& vd, const Object& object) const = 0;

	// Called after the Bindings::unassign function.
	virtual bool propagateAfterMakeUnequal(Bindings& bindings, VariableDomain& vd, const std::vector<const Object*>& objects) const = 0;
};

/**
 * Simple propagator which does only prune when a domain either becomes empty or only has a single object left in it.
 */
class SimpleBindingsPropagator : public BindingsPropagator
{
	virtual bool propagateAfterMakeEqual(Bindings& bindings, VariableDomain& vd, const VariableDomain& vd2) const;
	
	virtual bool propagateAfterMakeEqual(Bindings& bindings, VariableDomain& vd, const Object& object) const;

	virtual bool propagateAfterMakeEqual(Bindings& bindings, VariableDomain& vd, const std::vector<const Object*>& objects) const;
	
	virtual bool propagateAfterMakeUnequal(Bindings& bindings, VariableDomain& vd, VariableDomain& vd2) const;
	
	virtual bool propagateAfterMakeUnequal(Bindings& bindings, VariableDomain& vd, const Object& object) const;

	virtual bool propagateAfterMakeUnequal(Bindings& bindings, VariableDomain& vd, const std::vector<const Object*>& objects) const;

private:
	bool removeObjectFromUnequalDomains(Bindings& bindings, VariableDomain& vd, const Object& object) const;
};

};

#endif
