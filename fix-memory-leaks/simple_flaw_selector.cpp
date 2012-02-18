#include "simple_flaw_selector.h"

#include <vector>

#include "plan.h"
#include "plan_flaws.h"
#include "pointers.h"

namespace MyPOP {

const Flaw& SimpleFlawSelectionStrategy::selectFlaw(const Plan& plan) const
{
	// First handle all unsafes in a plan before doing anything else.
	const std::vector<UnsafePtr> unsafes = plan.getUnsafes();

	if (unsafes.size() > 0)
		return *unsafes[0];
	
	// Check which flaws exist in this plan and select one. For now we just
	// consider open conditions.
	const std::vector<OpenConditionPtr> open_conditions = plan.getOpenConditions();

	// Simply select the first one.
	return *open_conditions[0];
}
	
};
