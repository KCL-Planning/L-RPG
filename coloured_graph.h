#ifndef MYPOP_COLOURED_GRAPH_H
#define MYPOP_COLOURED_GRAPH_H

#include <map>
#include <set>
#include <vector>
#include "action_manager.h"

namespace MyPOP
{

class ColouredGraphNodeGoal;
class ColouredGraphNodePredicates;

class GroundedAtom;
class Predicate;
class Object;

/*
class ColouredGraphNode
{
public:
	virtual bool isEqualTo(const ColouredGraphNodeGoal& other) const = 0;
	virtual bool isEqualTo(const ColouredGraphNodePredicates& other) const = 0;
private:
	
};
*/

class ColouredGraphNodeGoal// : ColouredGraphNode
{
public:
	ColouredGraphNodeGoal(const GroundedAtom& grounded_atom);
	
	//bool isEqualTo(const ColouredGraphNodeGoal& other) const;
	//bool isEqualTo(const ColouredGraphNodePredicates& other) const;
	
	bool isEquivalentTo(const GroundedAtom& atom) const;
	bool isEquivalentTo(const ColouredGraphNodeGoal& atom) const;
	
	const GroundedAtom& getGroundedAtom() const { return *grounded_atom_; }
	
private:
	const GroundedAtom* grounded_atom_;
};

class ColouredGraphNodePredicates// : ColouredGraphNode
{
public:
	ColouredGraphNodePredicates(const Predicate& predicate, int invariable_index, const std::vector<const Object*>& objects);
	
	//bool isEqualTo(const ColouredGraphNodeGoal& other) const;
	//bool isEqualTo(const ColouredGraphNodePredicates& other) const;
	
	bool isEquivalentTo(const Predicate& predicate, int invariables, const std::vector<const Object*>& objects) const;
	bool isEquivalentTo(const ColouredGraphNodePredicates& other) const;
	
	const Predicate& getPredicate() const { return *predicates_; }
	int getInvariables() const { return invariables_; }
	const std::vector<const Object*>& getObjects() const { return objects_; }
	
private:
	
	bool isEqualTo(const ColouredGraphNodePredicates& other, int* mapping) const;
	
	const Predicate* predicates_;
	int invariables_;
	std::vector<const Object*> objects_;
};

class ColouredGraphNodeObjects
{
public:
	void addObject(const Object& object);
	
	void addEdge(const ColouredGraphNodePredicates& edge);
	void addEdge(const ColouredGraphNodeGoal& edge);
	
	const std::vector<const Object*>& getObjects() const { return objects_; }
	
	const std::vector<const ColouredGraphNodePredicates*>& getPredicateEdges() const { return predicate_edges_; }
	const std::vector<const ColouredGraphNodeGoal*>& getGoalEdges() const { return goal_edges_; }
	
	bool isSymmetricalTo(const ColouredGraphNodeObjects& other) const;
	
private:
	std::vector<const Object*> objects_;
	std::vector<const ColouredGraphNodePredicates*> predicate_edges_;
	std::vector<const ColouredGraphNodeGoal*> goal_edges_;
};

std::ostream& operator<<(std::ostream& os, const ColouredGraphNodeObjects& coloured_graph_node_object);

class ColouredGraph
{
public:
	ColouredGraph(const std::multimap<const Object*, const Object*>& symmetrical_objects);
	~ColouredGraph();
	ColouredGraphNodeObjects* getNode(const Object& object) const;
	ColouredGraphNodePredicates& createPredicateNode(const Predicate&, int invariable, const std::vector<const Object*>& objects);
	ColouredGraphNodeGoal& createGoalNode(const GroundedAtom& goal_atom);
	bool isSymmetricalTo(const ColouredGraph& other) const;
	
private:
	
	//bool findSymmetry(const std::set<const ColouredGraphNodeObjects*>& lhs_object_mappings, const std::set<const ColouredGraphNodeObjects*>& rhs_object_mappings, const ColouredGraph& other, std::map<const ColouredGraphNodeObjects*, const ColouredGraphNodeObjects*>& mappings, const std::map<const ColouredGraphNodeObjects*, const ColouredGraphNodeObjects*>& tmp_mappings) const;
	bool findSymmetry(const std::set<const ColouredGraphNodeObjects*>& rhs_object_mappings, const ColouredGraph& other) const;
	
	std::map<const Object*, ColouredGraphNodeObjects*> mapped_objects_;
	//std::vector<ColouredGraphNode*> nodes_;
	std::vector<ColouredGraphNodePredicates*> predicate_nodes_;
	std::vector<ColouredGraphNodeGoal*> goal_nodes_;
	std::vector<ColouredGraphNodeObjects*> all_object_edges_;
	
	friend std::ostream& operator<<(std::ostream& os, const ColouredGraph& coloured_graph);
};

std::ostream& operator<<(std::ostream& os, const ColouredGraph& coloured_graph);

};

#endif
