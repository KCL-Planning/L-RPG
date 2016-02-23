#ifndef MYPOP_HEURISTICS_HEURISTIC_INTERFACE_H
#define MYPOP_HEURISTICS_HEURISTIC_INTERFACE_H

#include <iostream>

#include "heuristic_interface.h"
#include "dtg_reachability.h"
#include "fact_set.h"

namespace MyPOP {

class GroundedAtom;
class State;

namespace HEURISTICS {

HeuristicInterface::~HeuristicInterface()
{
	
}

void HeuristicInterface::getFunctionalSymmetricSets(std::multimap<const Object*, const Object*>& symmetrical_groups, const State& state, const std::vector<const GroundedAtom*>& initial_facts, const std::vector<const GroundedAtom*>& goal_facts, const TermManager& term_manager) const
{
	
}

void HeuristicInterface::deleteHelpfulActions()
{
	for (std::vector<std::pair<const REACHABILITY::AchievingTransition*, const std::vector<HEURISTICS::VariableDomain*>* > >::const_iterator ci = helpful_actions_.begin(); ci != helpful_actions_.end(); ++ci)
	{
		delete (*ci).first;
		const std::vector<HEURISTICS::VariableDomain*>* variable_domain = (*ci).second;
		for (std::vector<HEURISTICS::VariableDomain*>::const_iterator ci = variable_domain->begin(); ci != variable_domain->end(); ++ci)
		{
			delete *ci;
		}
		delete variable_domain;
	}
	helpful_actions_.clear();
}

};

};

#endif
