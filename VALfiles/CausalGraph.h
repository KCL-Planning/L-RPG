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

#ifndef __CGA
#define __CGA

#include <map>
#include <set>


namespace VAL {
class pddl_type;

class CausalGraph {
public:
	typedef std::map<const pddl_type *,std::set<const pddl_type *> > Graph;

private:
	Graph dependencies;
	Graph dependents;
	
public:
	CausalGraph();
	const std::set<const pddl_type *> & getDependencies(const pddl_type * p)
	{
		return dependencies[p];
	};
	const std::set<const pddl_type *> & getDependents(const pddl_type * p)
	{
		return dependents[p];
	};
};


};

}

#endif
