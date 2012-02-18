#ifndef MYPOP_SAS_PLUS_REACHABLE_TREE_H
#define MYPOP_SAS_PLUS_REACHABLE_TREE_H

#include <list>
#include <vector>
#include <assert.h>
#include <iosfwd>
#include "dtg_reachability.h"

namespace MyPOP {

namespace SAS_Plus {

class ReachableSet;


class ReachableFact;
class ReachableTree;
class ReachableTreeIterator;
class ConstReachableTreeIterator;

class ReachableTreeNode
{
public:
	ReachableTreeNode(ReachableTree& tree, ReachableTreeNode* parent, unsigned int level, const ReachableFact& reachable_fact);
	
	~ReachableTreeNode();
	
	ReachableTreeNode* getParent() const { return parent_; }
	
	unsigned int getLevel() const { return level_; }
	
	const ReachableFact& getReachableFact() const { return *reachable_fact_; }
	bool updateReachableFact();
	
//	bool removeOldNodes();
	
	ConstReachableTreeIterator cbegin() const;
	ConstReachableTreeIterator cend() const;
	
	ReachableTreeIterator begin();
	ReachableTreeIterator end() const;
	
	const std::vector<ReachableTreeNode*>& getChildren() const { return children_; }
	
	unsigned int addFact(unsigned int level, const ReachableFact& reachable_fact, const std::vector<std::vector<std::pair<unsigned int, unsigned int> >** >& constraints_set);
	void addChild(ReachableTreeNode* reachable_tree_node);
	
	void sanityCheck() const;
	
	unsigned int getLastIterationUpdated() const { return last_iteration_updated_; }
	void setLastIterationUpdated(unsigned int iteration) { last_iteration_updated_ = iteration; }
	
	/**
	 * When the equivalences are updated, we need to 'merge' trees together by replacing all the nodes which contain 
	 * reachable facts which are due to be removed with the up to date versions of the same reachable fact. This 
	 * function compares the children of both nodes and checks if any of its children which are out-of-date can be 
	 * replaced with the up-to-date children of the given node.
	 * 
	 * Even if the children of the given node are not up-to-date we will check the children of its children until we have
	 * updated the entire tree. Some out-of-date nodes might be added if no replacement can be found in the current tree. 
	 * When this happens the method needs to be called again, this time with a different tree node which does contain an 
	 * up-to-date version.
	 * 
	 * The way this is done is by starting with a root node of a tree which is up-to-date and update all its children with 
	 * all other trees whose root is out-of-date, but its updated fact is identical to said tree. This will replace all 
	 * children of the up-to-date root with those which are up-to-date.
	 * 
	 * @param reachable_tree_node A node of another tree, the path from the root to the given node is identical to the 
	 * path from the root of this tree to this node (I.E. the updated version of every node passed is identical in both 
	 * paths).
	 */
	void updateChildren(const ReachableSet& reachable_set, const std::vector<std::vector<std::pair<unsigned int, unsigned int> >** >& constraints_set);
	
	void printCompleteTree(std::ostream& os) const;
	
	void markAsProcessed() { has_been_processed_ = true; }
	bool hasBeenProcessed() const { return has_been_processed_; }
	
	// DEBUG.
	const ReachableTree& getTree() const { assert (tree_ != NULL); return *tree_; }
	
private:
	
	bool canSatisfyConstraints(const ReachableFact& reachable_fact, unsigned int level, const std::vector<std::vector<std::pair<unsigned int, unsigned int> >** >& constraints_set) const;
	
	ReachableTree* tree_;
	
	ReachableTreeNode* parent_;
	
	std::vector<ReachableTreeNode*> children_;
	
	// The distance from the root to this node.
	unsigned int level_;
	
	unsigned int max_level_of_children_;

	// The value stored in this node.
	const ReachableFact* reachable_fact_;
	
	// The iteration where the EOGs of the reachable fact of this node was updated.
	unsigned int last_iteration_updated_;
	
	// Boolean to mark that this leaf node has been processed to generate new facts.
	bool has_been_processed_;
	
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableTreeNode& reachable_tree_node);
};

std::ostream& operator<<(std::ostream& os, const ReachableTreeNode& reachable_tree_node);

/**
 * Custom iterator to iterate from a leaf node to the root node. Its name is a little counter intuitive, but I couldn't be
 * bothered with a reverse_iterator.
 */
class ReachableTreeIterator : public std::iterator<std::forward_iterator_tag, ReachableTreeNode>
{
public:
	ReachableTreeIterator(ReachableTreeNode* node) : value_(node) {}
	ReachableTreeIterator(const ReachableTreeIterator& rti) : value_(rti.value_) {}
	
	ReachableTreeIterator& operator++() { value_ = value_->getParent(); return *this; }
	ReachableTreeIterator operator++(int) {ReachableTreeIterator tmp(*this); operator++(); return tmp;}
	
	ReachableTreeIterator operator+(unsigned int increment)
	{
		ReachableTreeNode* rtn = value_;
		for (unsigned int i = 0; i < increment; i++)
		{
			assert (rtn != NULL);
			rtn = rtn->getParent();
		}
		return ReachableTreeIterator(rtn);
	}
	
	bool operator==(const ReachableTreeIterator& rhs) {return value_ == rhs.value_; }
	bool operator!=(const ReachableTreeIterator& rhs) {return value_ != rhs.value_;}
	ReachableTreeNode& operator*() {return *value_;}
private:
	ReachableTreeNode* value_;
};

class ConstReachableTreeIterator : public std::iterator<std::forward_iterator_tag, const ReachableTreeNode>
{
public:
	ConstReachableTreeIterator(const ReachableTreeNode* node) : value_(node) {}
	ConstReachableTreeIterator(const ConstReachableTreeIterator& rti) : value_(rti.value_) {}
	
	ConstReachableTreeIterator& operator++() { value_ = value_->getParent(); return *this; }
	ConstReachableTreeIterator operator++(int) {ConstReachableTreeIterator tmp(*this); operator++(); return tmp;}
	
	ConstReachableTreeIterator operator+(unsigned int increment)
	{
		const ReachableTreeNode* rtn = value_;
		for (unsigned int i = 0; i < increment; i++)
		{
			assert (rtn != NULL);
			rtn = rtn->getParent();
		}
		return ConstReachableTreeIterator(rtn);
	}
	
	bool operator==(const ConstReachableTreeIterator& rhs) {return value_ == rhs.value_; }
	bool operator!=(const ConstReachableTreeIterator& rhs) {return value_ != rhs.value_;}
	const ReachableTreeNode& operator*() {return *value_;}
private:
	const ReachableTreeNode* value_;
};

	
class ReachableTree
{
public:
	ReachableTree(const ReachableSet& reachable_set, const std::vector<std::vector<std::pair<unsigned int, unsigned int> >** >& constraints_set);
	
	~ReachableTree();
	
	void addFact(unsigned int level, const ReachableFact& reachable_fact);
	
	void equivalencesUpdated(unsigned int iteration, const std::vector<ReachableTree*>& reachable_trees);
	
	const ReachableTreeNode* getRoot() const { return root_node_; }

	void updateRoot() { root_node_->updateReachableFact(); }
	
	const std::list<ReachableFact*>& getFactsAtLevel(unsigned int level) const;
	
	unsigned int getMaxDepth() const { return reachable_set_->getFactsSet().size(); }
	
	void addNewLeaf(ReachableTreeNode& new_leaf);
	
	// TODO: Don't expose this information!
	const std::vector<ReachableTreeNode*>& getLeaves() const { return leaf_nodes_; }
	unsigned int getTotalNumberOfLeafs() const { return leaf_nodes_.size(); };
//	unsigned int getNumberOfProcessedLeafs() const 	{ return leafs_processed_; }
	unsigned int getCachedNumberOfLeafs()
	{
		if (!cache_is_valid_)
		{
			cached_size_ = leaf_nodes_.size();
			cache_is_valid_ = true;
		}
		assert (cached_size_ <= leaf_nodes_.size());
		return cached_size_;
	}
	
private:
	const ReachableSet* reachable_set_;
	
	/**
	 * Search the tree to find a node which holds a reference to the given reachable fact and restrict the search to the
	 * given level.
	 */
	ReachableTreeNode* find(const ReachableFact& reachable_fact, unsigned int level) const;
	
	const std::vector<std::vector<std::pair<unsigned int, unsigned int> >** >* constraints_set_;
	
	// The root of the tree.
	ReachableTreeNode* root_node_;
	
	// Store all the leaves which are at the maximal depth, thus forming a complete assignment to all the 
	// preconditions of a reachable set.
	std::vector<ReachableTreeNode*> leaf_nodes_;
	
//	unsigned int leafs_processed_;
	bool cache_is_valid_;
	unsigned int cached_size_;
	
	void sanityCheck() const;
	
	friend std::ostream& operator<<(std::ostream& os, const ReachableTree& reachable_tree);
};

std::ostream& operator<<(std::ostream& os, const ReachableTree& reachable_tree);

};

};

#endif // MYPOP_SAS_PLUS_REACHABLE_TREE_H
