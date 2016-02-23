#include "coloured_graph.h"
#include "predicate_manager.h"
#include "term_manager.h"
#include "fc_planner.h"

namespace MyPOP
{

ColouredGraphNodeGoal::ColouredGraphNodeGoal(const GroundedAtom& grounded_atom)
	: grounded_atom_(&grounded_atom)
{
	
}

bool ColouredGraphNodeGoal::isEquivalentTo(const GroundedAtom& grounded_atom) const
{
	return &grounded_atom == grounded_atom_;
}

bool ColouredGraphNodeGoal::isEquivalentTo(const ColouredGraphNodeGoal& atom) const
{
	return isEquivalentTo(*atom.grounded_atom_);
}

ColouredGraphNodePredicates::ColouredGraphNodePredicates(const Predicate& predicate, int invariable_index, const std::vector<const Object*>& objects)
	: predicates_(&predicate), invariables_(invariable_index)
{
	objects_.insert(objects_.end(), objects.begin(), objects.end());
}

bool ColouredGraphNodePredicates::isEquivalentTo(const Predicate& predicate, int invariables, const std::vector<const Object*>& objects) const
{
	if (predicate.getName() != predicates_->getName() || predicate.getArity() != predicates_->getArity() || invariables != invariables_ || objects_.size() != objects.size())
	{
		return false;
	}
	
	for (unsigned int i = 0; i < objects.size(); ++i)
	{
		if ((int)i != invariables && objects[i] != objects_[i])
		{
			return false;
		}
	}
	return true;
}

bool ColouredGraphNodePredicates::isEquivalentTo(const ColouredGraphNodePredicates& other) const
{
	return isEquivalentTo(*other.predicates_, other.invariables_, other.objects_);
}

void ColouredGraphNodeObjects::addObject(const Object& object)
{
	objects_.push_back(&object);
}

void ColouredGraphNodeObjects::addEdge(const ColouredGraphNodePredicates& edge)
{
	for (std::vector<const ColouredGraphNodePredicates*>::const_iterator ci = predicate_edges_.begin(); ci != predicate_edges_.end(); ++ci)
	{
		const ColouredGraphNodePredicates* cgn = *ci;
		if (cgn == &edge)
		{
			return;
		}
	}
	
	predicate_edges_.push_back(&edge);
}

void ColouredGraphNodeObjects::addEdge(const ColouredGraphNodeGoal& edge)
{
	for (std::vector<const ColouredGraphNodeGoal*>::const_iterator ci = goal_edges_.begin(); ci != goal_edges_.end(); ++ci)
	{
		const ColouredGraphNodeGoal* cgn = *ci;
		if (cgn == &edge)
		{
			return;
		}
	}
	
	goal_edges_.push_back(&edge);
}

ColouredGraphNodeObjects* ColouredGraph::getNode(const Object& object) const
{
	std::map<const Object*, ColouredGraphNodeObjects*>::const_iterator ci = mapped_objects_.find(&object);
	if (ci == mapped_objects_.end())
	{
		return NULL;
	}
	
	return (*ci).second;
}

bool ColouredGraphNodeObjects::isSymmetricalTo(const ColouredGraphNodeObjects& other) const
{
	if (predicate_edges_.size() != other.predicate_edges_.size() || goal_edges_.size() != other.goal_edges_.size())
	{
		return false;
	}
	
	for (std::vector<const ColouredGraphNodePredicates*>::const_iterator ci = predicate_edges_.begin(); ci != predicate_edges_.end(); ++ci)
	{
		const ColouredGraphNodePredicates* lhs_cgnp = *ci;
		bool found_match = false;
		for (std::vector<const ColouredGraphNodePredicates*>::const_iterator ci = other.predicate_edges_.begin(); ci != other.predicate_edges_.end(); ++ci)
		{
			const ColouredGraphNodePredicates* rhs_cgnp = *ci;
			if (lhs_cgnp->isEquivalentTo(*rhs_cgnp))
			{
				found_match = true;
				break;
			}
		}
		
		if (!found_match)
		{
			return false;
		}
	}
	
	for (std::vector<const ColouredGraphNodeGoal*>::const_iterator ci = goal_edges_.begin(); ci != goal_edges_.end(); ++ci)
	{
		const ColouredGraphNodeGoal* lhs_cgng = *ci;
		bool found_match = false;
		for (std::vector<const ColouredGraphNodeGoal*>::const_iterator ci = other.goal_edges_.begin(); ci != other.goal_edges_.end(); ++ci)
		{
			const ColouredGraphNodeGoal* rhs_cgng = *ci;
			if (lhs_cgng->isEquivalentTo(*rhs_cgng))
			{
				found_match = true;
				break;
			}
		}
		
		if (!found_match)
		{
			return false;
		}
	}
	
	return true;
}

std::ostream& operator<<(std::ostream& os, const ColouredGraphNodeObjects& coloured_graph_node_object)
{
	os << "{";
	for (std::vector<const Object*>::const_iterator ci = coloured_graph_node_object.getObjects().begin(); ci != coloured_graph_node_object.getObjects().end(); ++ci)
	{
		os << **ci << ", ";
	}
	os << "}";
	return os;
}

ColouredGraph::ColouredGraph(const std::multimap<const Object*, const Object*>& symmetrical_objects)
{
	std::set<const Object*> processed_objects;
	
	for (std::multimap<const Object*, const Object*>::const_iterator ci =  symmetrical_objects.begin(); ci != symmetrical_objects.end(); ++ci)
	{
		const Object* lhs_object = (*ci).first;
		
		if (processed_objects.count(lhs_object) != 0)
		{
			continue;
		}
		processed_objects.insert(lhs_object);
		
		ColouredGraphNodeObjects* cgno = new ColouredGraphNodeObjects();
		all_object_edges_.push_back(cgno);
		
		std::pair<std::multimap<const Object*, const Object*>::const_iterator, std::multimap<const Object*, const Object*>::const_iterator> m_ci = symmetrical_objects.equal_range(lhs_object);
		for (std::multimap<const Object*, const Object*>::const_iterator ci = m_ci.first; ci != m_ci.second; ++ci)
		{
			cgno->addObject(*(*ci).second);
			mapped_objects_.insert(std::make_pair((*ci).second, cgno));
		}
	}
}

ColouredGraph::~ColouredGraph()
{
	for (std::vector<ColouredGraphNodeObjects*>::const_iterator ci = all_object_edges_.begin(); ci != all_object_edges_.end(); ++ci)
	{
		delete *ci;
	}
	
	for (std::vector<ColouredGraphNodePredicates*>::const_iterator ci = predicate_nodes_.begin(); ci != predicate_nodes_.end(); ++ci)
	{
		delete *ci;
	}
	
	for (std::vector<ColouredGraphNodeGoal*>::const_iterator ci = goal_nodes_.begin(); ci != goal_nodes_.end(); ++ci)
	{
		delete *ci;
	}
}

ColouredGraphNodePredicates& ColouredGraph::createPredicateNode(const Predicate& predicate, int invariable, const std::vector<const Object*>& objects)
{
	for (std::vector<ColouredGraphNodePredicates*>::const_iterator ci = predicate_nodes_.begin(); ci != predicate_nodes_.end(); ++ci)
	{
		ColouredGraphNodePredicates* cgnp = *ci;
		if (cgnp->isEquivalentTo(predicate, invariable, objects))
		{
			return *cgnp;
		}
	}
	
	ColouredGraphNodePredicates* cgnp = new ColouredGraphNodePredicates(predicate, invariable, objects);
	predicate_nodes_.push_back(cgnp);
	return *cgnp;
}

ColouredGraphNodeGoal& ColouredGraph::createGoalNode(const GroundedAtom& goal_atom)
{
	for (std::vector<ColouredGraphNodeGoal*>::const_iterator ci = goal_nodes_.begin(); ci != goal_nodes_.end(); ++ci)
	{
		ColouredGraphNodeGoal* cgnp = *ci;
		if (cgnp->isEquivalentTo(goal_atom))
		{
			return *cgnp;
		}
	}
	
	ColouredGraphNodeGoal* cgnp = new ColouredGraphNodeGoal(goal_atom);
	goal_nodes_.push_back(cgnp);
	return *cgnp;
}

bool ColouredGraph::isSymmetricalTo(const ColouredGraph& other) const
{
	if (other.mapped_objects_.size() != mapped_objects_.size())
	{
		return false;
	}
	
	std::set<const ColouredGraphNodeObjects*> rhs_mapped_objects;
	
	//std::map<const ColouredGraphNodeObjects*, const ColouredGraphNodeObjects*> mappings, dummy_mappings;
	
	bool are_symmetrical = findSymmetry(rhs_mapped_objects, other);//, mappings, dummy_mappings);
/*
 	if (are_symmetrical)
	{
		for (std::map<const ColouredGraphNodeObjects*, const ColouredGraphNodeObjects*>::const_iterator ci = mappings.begin(); ci != mappings.end(); ++ci)
		{
			std::cout << *(*ci).first << " >>>>-----> " << *(*ci).second << std::endl;
		}
	}
*/
	return are_symmetrical;
}

bool ColouredGraph::findSymmetry(const std::set<const ColouredGraphNodeObjects*>& rhs_object_mappings, const ColouredGraph& other) const//, std::map<const ColouredGraphNodeObjects*, const ColouredGraphNodeObjects*>& mappings, const std::map<const ColouredGraphNodeObjects*, const ColouredGraphNodeObjects*>& tmp_mappings) const
{
	if (rhs_object_mappings.size() == mapped_objects_.size())
	{
//		mappings = tmp_mappings;
		return true;
	}
	
	// Find an object that has not been mapped yet.
	 
	std::map<const Object*, ColouredGraphNodeObjects*>::const_iterator ci = mapped_objects_.begin();
	for (unsigned int i = 0; i < rhs_object_mappings.size(); ++i)
	{
		++ci;
	}
	const ColouredGraphNodeObjects* lhs_object = (*ci).second;
		
	// Find a set of objects that have the same number of objects and the same references.
	for (std::map<const Object*, ColouredGraphNodeObjects*>::const_iterator ci = other.mapped_objects_.begin(); ci != other.mapped_objects_.end(); ++ci)
	{
		const ColouredGraphNodeObjects* rhs_object = (*ci).second;
		
		if (rhs_object_mappings.count(rhs_object) != 0)
		{
			continue;
		}
		
		if (lhs_object->getObjects().size() != rhs_object->getObjects().size())
		{
			continue;
		}
		
		if (lhs_object->isSymmetricalTo(*rhs_object))
		{
			//std::set<const ColouredGraphNodeObjects*> new_lhs_object_mappings(lhs_object_mappings);
			//new_lhs_object_mappings.insert(lhs_object);
			
			std::set<const ColouredGraphNodeObjects*> new_rhs_object_mappings(rhs_object_mappings);
			new_rhs_object_mappings.insert(rhs_object);
			
			//std::map<const ColouredGraphNodeObjects*, const ColouredGraphNodeObjects*> new_mappings(tmp_mappings);
			//new_mappings[lhs_object] = rhs_object;
			
			//if (findSymmetry(new_lhs_object_mappings, new_rhs_object_mappings, other, mappings, new_mappings))
			if (findSymmetry(new_rhs_object_mappings, other))
			{
				return true;
			}
		}
	}
	return false;
}

std::ostream& operator<<(std::ostream& os, const ColouredGraph& coloured_graph)
{
	for (std::map<const Object*, ColouredGraphNodeObjects*>::const_iterator ci = coloured_graph.mapped_objects_.begin(); ci != coloured_graph.mapped_objects_.end(); ++ci)
	{
		ColouredGraphNodeObjects* cgno = (*ci).second;
		
		os << "{";
		for (std::vector<const Object*>::const_iterator ci = cgno->getObjects().begin(); ci != cgno->getObjects().end(); ++ci)
		{
			os << **ci << ", ";
		}
		os <<"}";
		
		os << std::endl << "Predicates: " << std::endl;
		
		for (std::vector<const ColouredGraphNodePredicates*>::const_iterator ci = cgno->getPredicateEdges().begin(); ci != cgno->getPredicateEdges().end(); ++ci)
		{
			const ColouredGraphNodePredicates* cgnp = *ci;
			os << "* "<< cgnp->getPredicate() << "(" << cgnp->getInvariables() << ")" << std::endl;
			os << "{";
			for (std::vector<const Object*>::const_iterator ci = cgnp->getObjects().begin(); ci != cgnp->getObjects().end(); ++ci)
			{
				os << **ci << ",";
			}
			os << "}" << std::endl;
		}
		
		os << std::endl << "Goals: " << std::endl;
		for (std::vector<const ColouredGraphNodeGoal*>::const_iterator ci = cgno->getGoalEdges().begin(); ci != cgno->getGoalEdges().end(); ++ci)
		{
			os << "* "<< (*ci)->getGroundedAtom() << std::endl;
		}
	}
	
	return os;
}

};
