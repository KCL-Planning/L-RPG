#ifndef MYPOP_FLAW_SELECTION_STRATEGY_H
#define MYPOP_FLAW_SELECTION_STRATEGY_H

namespace MyPOP {

class Plan;
class Flaw;
	
/**
 * Interface for all classes which define a flaw selection strategy.
 */
class FlawSelectionStrategy
{
public:
	virtual const Flaw& selectFlaw(const Plan& plan)const = 0;
};
	
};

#endif
