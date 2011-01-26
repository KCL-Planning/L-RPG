#ifndef MYPOP_SAS_RELAXED_REACHABILITY_ANALIST_H
#define MYPOP_SAS_RELAXED_REACHABILITY_ANALIST_H

#include <vector>

namespace MyPOP {

class Atom;

namespace SAS_Plus {
	
class DomainTransitionGraphManager;
	
/**
 * Take the DTG nodes constructed and perform the same analyse as done by the relaxed planning graph.
 */
class RelaxedReachabilityAnalyst
{
public:
	RelaxedReachabilityAnalyst(const DomainTransitionGraphManager& dtg_manager);
	
	void performReachabilityAnalysis(const std::vector<const Atom*>& initial_facts);
	
private:
	const DomainTransitionGraphManager* dtg_manager_;
};

};

};

#endif // RELAXED_REACHABILITY_ANALIST_H
