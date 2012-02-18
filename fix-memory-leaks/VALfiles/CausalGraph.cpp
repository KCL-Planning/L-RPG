/************************************************************************
 * Copyright 2008, Strathclyde Planning Group,
 * Department of Computer and Information Sciences,
 * University of Strathclyde, Glasgow, UK
 * http://planning.cis.strath.ac.uk/
 *
 * Maria Fox, Richard Howey and Derek Long - VAL
 * Stephen Cresswell - PDDL Parser
 *
 * This file is part of VAL, the PDDL validator.
 *
 * VAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *
 * VAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with VAL.  If not, see <http://www.gnu.org/licenses/>.
 *
 ************************************************************************/

#include "CausalGraph.h"

#include "VisitController.h"

namespace VAL {

class CGAnalyser : public VisitController {
private: 
	CausalGraph & cg;
public:
	CGAnalyser(CausalGraph & c) : cg(c) {};
	
	virtual void visit_simple_goal(VAL::simple_goal * p);
	virtual void visit_qfied_goal(VAL::qfied_goal * p) 
	{OUTPUT cout << "Quantified goal\n";};
	virtual void visit_conj_goal(VAL::conj_goal * p) 
	{p->getGoals()->visit(this);};
	virtual void visit_disj_goal(VAL::disj_goal * p) 
	{OUTPUT cout << "Disjunctive goal\n";};
	virtual void visit_timed_goal(VAL::timed_goal * p) 
	{
		p->getGoal()->visit(this);
	};	
	virtual void visit_imply_goal(VAL::imply_goal * p) 
	{
		OUTPUT cout << "Implication goal\n";
	};
	virtual void visit_neg_goal(VAL::neg_goal * p) 
	{
		OUTPUT cout << "Negative goal\n";
	};
	virtual void visit_simple_effect(VAL::simple_effect * p);
	virtual void visit_forall_effect(VAL::forall_effect * p) 
	{
		OUTPUT cout << "Quantified effect\n";
	};
	virtual void visit_cond_effect(VAL::cond_effect * p) 
	{
		OUTPUT cout << "Conditional effect\n";
	};
	virtual void visit_timed_effect(VAL::timed_effect * p) 
	{
		p->effs->visit(this);
	};
	virtual void visit_effect_lists(VAL::effect_lists * p) 
	{
		p->add_effects.pc_list<simple_effect*>::visit(this);
		p->forall_effects.pc_list<forall_effect*>::visit(this);
		p->cond_effects.pc_list<cond_effect*>::visit(this);
		p->timed_effects.pc_list<timed_effect*>::visit(this);
		p->del_effects.pc_list<simple_effect*>::visit(this);
	};
	virtual void visit_operator_(VAL::operator_ * p) 
	{
		p->precondition->visit(this);
		p->effects->visit(this);
	};
	virtual void visit_action(VAL::action * p)
	{
		visit_operator_(p);
	}
	virtual void visit_durative_action(VAL::durative_action * p) 
	{
		visit_operator_(p);
	};
	virtual void visit_domain(VAL::domain * p) 
	{
		visit_operator_list(p->ops);
	};
}

CausalGraph::CausalGraph()
{
	CGAnalyser cga(*this);
	the_domain->visit(&cga);

};

}
