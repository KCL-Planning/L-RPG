#ifndef SIMPLE_FLAW_SELECTOR_H
#define SIMPLE_FLAW_SELECTOR_H

#include "flaw_selector.h"

namespace MyPOP {

/**
 * Select unsafes before open conditions in a FIFO ordering.
 */
class SimpleFlawSelectionStrategy : public FlawSelectionStrategy
{
public:
	SimpleFlawSelectionStrategy() {}
	
	const Flaw& selectFlaw(const Plan& plan) const;	
};

};

#endif // SIMPLE_FLAW_SELECTOR_H
