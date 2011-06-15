#ifndef MYPOP_SAS_RELAXED_REACHABILITY_ANALIST_H
#define MYPOP_SAS_RELAXED_REACHABILITY_ANALIST_H

#include <vector>
#include <map>

namespace MyPOP {

class Atom;
class Bindings;
class Object;

namespace SAS_Plus {

class BoundedAtom;
class DomainTransitionGraphManager;
class DomainTransitionGraphNode;
	
/**
 * Take the DTG nodes constructed and perform the same analyse as done by the relaxed planning graph.
 */
class RelaxedReachabilityAnalyst
{
public:
	RelaxedReachabilityAnalyst(const DomainTransitionGraphManager& dtg_manager);
	
	void performReachabilityAnalysis(const std::vector<const Atom*>& initial_facts, Bindings initial_bindings);
	
private:
	
	/** 
	 * Find all possible supports for @ref(atoms_to_achieve) from all the facts in @ref(initial_facts). Whilst working
	 * though this list all variable assignments are recorded in @ref(variable_assignments), all facts choosen for supporting the facts
	 * are stored in @ref(initial_supporting_facts). Each full valid assignment is stored in @ref(supporting_tupples).
	 * @param supporting_tupples All found sets which can be unified with all the items of @ref(atoms_to_achieve)
	 * are inserted in this vector.
	 * @param variable_assignments Maps variable domains to a single object which has been assigned to that domain. As the
	 * algorithm works through all the facts to be achieved it stores the assignments made so far and if an assignment
	 * cannot be made - there is a conflict - the algorithm will backtrack and try other assignments until it finds one
	 * which supports all the facts in @ref(atoms_to_achieve). This assignment is then added to @ref(supporting_tupples).
	 * @param atoms_to_achieve The set of facts we want to achieve.
	 * @param atoms_to_achieve_bindings The bindings of the set of facts we want to achieve.
	 * @param initial_supporting_facts Set of facts which support the atoms to achieve. This list will 
	 * progressively be filled with supporting facts. The size of this list determines which fact from
	 * @ref(atoms_to_achieve) to work on next (the initial_supporting_facts.size()'th fact to be precise).
	 * @param initial_facts List of facts which we know to be true. From this set the supporting facts will
	 * be drawn.
	 * @param established_facts_bindings The bindings of all the facts achieved so far.
	 */
	void getSupportingFacts(std::vector< std::vector< const MyPOP::SAS_Plus::BoundedAtom* >* >& supporting_tupples, const std::map< const std::vector< const MyPOP::Object* >*, const MyPOP::Object* >& variable_assignments, const std::vector< MyPOP::SAS_Plus::BoundedAtom* >& atoms_to_achieve, const MyPOP::Bindings& atoms_to_achieve_bindings, const std::vector< const MyPOP::SAS_Plus::BoundedAtom* >& initial_supporting_facts, const std::vector< const MyPOP::SAS_Plus::BoundedAtom* >& initial_facts, const MyPOP::Bindings& established_facts_bindings);
	
	
	void initialisePossibleAssignmentsToDTGNodes(const std::vector<const Atom*>& initial_facts, const std::vector<const BoundedAtom*>& established_facts, const Bindings& initial_bindings);
	
	const DomainTransitionGraphManager* dtg_manager_;
	
	std::map<const DomainTransitionGraphNode*, std::vector<std::vector<const BoundedAtom*>* >* > supported_facts_;
};

};

};

#endif // RELAXED_REACHABILITY_ANALIST_H
