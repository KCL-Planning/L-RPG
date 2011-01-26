#ifndef MYPOP_ORDERINGS_H
#define MYPOP_ORDERINGS_H

#include <vector>
#include <iostream>
#include <boost/dynamic_bitset.hpp>
#include "plan_types.h"

namespace MyPOP {

/**
 * An empty class, only to be used with durative actions (not considered for now).
 */
class StepTime
{
public:
	static StepTime dummy_step_time;

};

/**
 * Ordering constraint between plan steps.
 */
class Ordering
{
public:
	/* Constructs an ordering constraint. */
	Ordering(StepID before_id, StepTime before_time, StepID after_id, StepTime after_time)
	: before_id_(before_id), before_time_(before_time), after_id_(after_id), after_time_(after_time) {}

	/* Returns the preceeding step id. */
	StepID before_id() const { return before_id_; }

	/* Returns the time point of preceeding step. */
	StepTime before_time() const { return before_time_; }

	/* Returns the suceeding step id. */
	StepID after_id() const { return after_id_; }

	/* Returns the time point of the preceeding step. */
	StepTime after_time() const { return after_time_; }

private:
	/* Preceeding step id. */
	StepID before_id_;
	/* Time point of preceeding step. */
	StepTime before_time_;
	/* Succeeding step id. */
	StepID after_id_;
	/* Time point of suceeding step. */
	StepTime after_time_;
};

/**
 * To determine the ordering between steps, the Orderings interface gives all the facilities
 * to either query about possible orderings between steps (e.g. can step x be ordered before
 * / after step y) and add additional constraints (e.g. step x must be ordered after step y).
 */
class Orderings
{
public:
	virtual ~Orderings() {}

	/**
	 * Impose an ordering on these ordering constraints and return true if and only if succesfull.
	 */
	virtual bool addOrdering(const Ordering& ordering) = 0;

	/**
	 * Check if a step can be ordered before another step.
	 */
	virtual bool canBeOrderedBefore(StepID step_id1, const StepTime& step_time1, StepID step_id2, const StepTime& step_time2) const = 0;

	/**
	 * Check if a step can be ordered after another step.
	 */
	virtual bool canBeOrderedAfter(StepID step_id1, const StepTime& step_time1, StepID step_id2, const StepTime& step_time2) const = 0;

	/**
	 * Check if two steps can be ordered concurrently.
	 */
	virtual bool canBeOrderedConcurrently(StepID step_id1, const StepTime& step_time1, StepID step_id2, const StepTime& step_time2) const = 0;

	/**
	 * Print the orders in a human readable manner.
	 */
	virtual void print(std::ostream& os) const = 0;
};

/**
 * Binary orderings are the simplest form of orderings. Given two steps we can say if one can be
 * ordered before the other. This ordering scheme is used if we do not concern ourselves with 
 * actions with durations. To store the orderings themselves we use a bitset which has N entries
 * for every step, where N is the total number of steps.
 *
 * When asking if step x is ordered before step y, we return the entry stored at index x * N + y.
 * A 1 signifies that the ordering can be made, a 0 signifies it can't. All bits start being set
 * to 1.
 *
 * TODO: We can scale down the number of bits we need to store (and number of manipulations we need
 * to make by 2 by only storing the relation of x can be ordered before y if the step id of x is 
 * lower than the step id of y. Because at the moment, whenever we add a new ordering we need to
 * update two entries in the bit array.
 */
class BinaryOrderings : public Orderings
{
public:
	BinaryOrderings();

	BinaryOrderings(const BinaryOrderings& other);

	virtual ~BinaryOrderings();

	virtual bool addOrdering(const Ordering& ordering);

	/**
	 * Check if a step can be ordered before another step.
	 */
	virtual bool canBeOrderedBefore(MyPOP::StepID step_id1, const MyPOP::StepTime& step_time1, MyPOP::StepID step_id2, const MyPOP::StepTime& step_time2) const;

	/**
	 * Check if a step can be ordered after another step.
	 */
	virtual bool canBeOrderedAfter(MyPOP::StepID step_id1, const MyPOP::StepTime& step_time1, MyPOP::StepID step_id2, const MyPOP::StepTime& step_time2) const;

	/**
	 * Check if two steps can be ordered concurrently.
	 */
	virtual bool canBeOrderedConcurrently(MyPOP::StepID step_id1, const MyPOP::StepTime& step_time1, MyPOP::StepID step_id2, const MyPOP::StepTime& step_time2) const;

	/**
	 * Print out the orders in a readable manner.
	 */
	virtual void print(std::ostream& os) const;

protected:
	/**
	 * Order a step before another step and return true if and only if succesfull.
	 */
	virtual bool orderBefore(MyPOP::StepID step_id1, const MyPOP::StepTime& step_time1, MyPOP::StepID step_id2, const MyPOP::StepTime& step_time2);

	/**
	 * Order a step after another step and return true if and only if succesfull.
	 */
	virtual bool orderAfter(MyPOP::StepID step_id1, const MyPOP::StepTime& step_time1, MyPOP::StepID step_id2, const MyPOP::StepTime& step_time2);


	// The actuall orderings.
	std::vector<boost::dynamic_bitset<>* > orderings_;

	// The greatest step id for which an ordering was stored.
	StepID biggest_step_id_;
};

};

#endif
