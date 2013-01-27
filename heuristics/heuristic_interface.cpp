#ifndef MYPOP_HEURISTICS_HEURISTIC_INTERFACE_H
#define MYPOP_HEURISTICS_HEURISTIC_INTERFACE_H

#include "heuristic_interface.h"

namespace MyPOP {

class GroundedAtom;
class State;

namespace HEURISTICS {

HeuristicInterface::~HeuristicInterface()
{
	
}

void HeuristicInterface::getFunctionalSymmetricSets(std::multimap<const Object*, const Object*>& symmetrical_groups, const State& state, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager)
{
	
}

};

};

#endif
