#ifndef MYPOP_SAS_PLUS_DTG_REACHABLITY_H
#define MYPOP_SAS_PLUS_DTG_REACHABLITY_H

#include <map>
#include <vector>

namespace MyPOP {
	
class Object;
	
namespace SAS_Plus {

class BoundedAtom;
class DomainTransitionGraph;
class DomainTransitionGraphNode;
	
/**
 * Utility class to perform relaxed reachability analysis on a given DTG.
 */
class DTGReachability
{
public:
	/**
	 * Constructor.
	 */
	DTGReachability(const DomainTransitionGraph& dtg_graph);
	
	void performReachabilityAnalsysis(const std::vector<const BoundedAtom*>& initial_facts);
	
private:
	
	/** 
	 * Find all possible supports for @ref(atoms_to_achieve) from all the facts in @ref(initial_facts). Whilst working
	 * though this list all variable assignments are recorded in @ref(variable_assignments), all facts choosen for supporting the facts
	 * are stored in @ref(initial_supporting_facts). Each full valid assignment is stored in @ref(supporting_tupples).
	 * @param supporting_tupples All found sets which can be unified with all the items of @ref(atoms_to_achieve)
	 * are inserted in this vector.
	 * @param variable_assignments Maps variable domains to a set of objects which has been assigned to that domain. As the
	 * algorithm works through all the facts to be achieved it stores the assignments made so far and if an assignment
	 * cannot be made - there is a conflict - the algorithm will backtrack and try other assignments until it finds one
	 * which supports all the facts in @ref(atoms_to_achieve). This assignment is then added to @ref(supporting_tupples).
	 * @param atoms_to_achieve The set of facts we want to achieve.
	 * @param initial_supporting_facts Set of facts which support the atoms to achieve. This list will 
	 * progressively be filled with supporting facts. The size of this list determines which fact from
	 * @ref(atoms_to_achieve) to work on next (the initial_supporting_facts.size()'th fact to be precise).
	 * @param initial_facts List of facts which we know to be true. From this set the supporting facts will
	 * be drawn.
	 */
	void getSupportingFacts(std::vector<std::vector<const BoundedAtom*>* >& supporting_tupples, const std::map<const std::vector<const Object*>*, const std::vector<const Object*>* >& variable_assignments, const std::vector<BoundedAtom*>& atoms_to_achieve, const std::vector<const BoundedAtom*>& initial_supporting_facts, const std::vector<const BoundedAtom*>& initial_facts);
	
	
	const DomainTransitionGraph* dtg_graph_;
	
	std::map<const DomainTransitionGraphNode*, std::vector<std::vector<const BoundedAtom*>* >* > supported_facts_;
};

};

};

#endif // MYPOP_SAS_PLUS_DTG_REACHABLITY_H