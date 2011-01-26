
#include "plan_orderings.h"
#include "plan.h"
#include "logging.h"

#include <algorithm>

namespace MyPOP {

StepTime StepTime::dummy_step_time = StepTime();

BinaryOrderings::BinaryOrderings()
	: biggest_step_id_(0)
{

}

BinaryOrderings::BinaryOrderings(const BinaryOrderings& other)
{
	biggest_step_id_ = other.biggest_step_id_;
	for (std::vector<boost::dynamic_bitset<>*>::const_iterator ci = other.orderings_.begin(); ci != other.orderings_.end(); ci++)
	{
		orderings_.push_back(new boost::dynamic_bitset<>(**ci));
	}
}

BinaryOrderings::~BinaryOrderings()
{
	for (std::vector<boost::dynamic_bitset<>* >::const_iterator ci = orderings_.begin(); ci != orderings_.end(); ci++)
	{
		delete *ci;
	}
}

bool BinaryOrderings::canBeOrderedBefore(StepID step_id1, const StepTime& step_time1, StepID step_id2, const StepTime& step_time2) const
{
	if (step_id1 == step_id2)
		return false;
	else if (step_id1 >= orderings_.size() || step_id2 >= orderings_.size())
		return true;
	return (*orderings_[step_id1])[step_id2];
}

bool BinaryOrderings::canBeOrderedAfter(StepID step_id1, const StepTime& step_time1, StepID step_id2, const StepTime& step_time2) const
{
	if (step_id1 == step_id2)
		return false;
	else if (step_id1 >= orderings_.size() || step_id2 >= orderings_.size())
		return true;
	return (*orderings_[step_id2])[step_id1];
}

bool BinaryOrderings::canBeOrderedConcurrently(StepID step_id1, const StepTime& step_time1, StepID step_id2, const StepTime& step_time2) const
{
	if (step_id1 == step_id2)
		return true;
	return canBeOrderedBefore(step_id1, step_time1, step_id2, step_time2) && 
	       canBeOrderedAfter(step_id1, step_time1, step_id2, step_time2);
}

bool BinaryOrderings::orderBefore(StepID step_id1, const StepTime& step_time1, StepID step_id2, const StepTime& step_time2)
{
	if (!canBeOrderedBefore(step_id1, step_time1, step_id2, step_time2))
		return false;
	(*orderings_[step_id2])[step_id1] = false;
	return true;
}

bool BinaryOrderings::orderAfter(StepID step_id1, const StepTime& step_time1, StepID step_id2, const StepTime& step_time2)
{
	if (!canBeOrderedAfter(step_id1, step_time1, step_id2, step_time2))
		return false;
	(*orderings_[step_id1])[step_id2] = false;
	return true;
}

bool BinaryOrderings::addOrdering(const Ordering& ordering)
{

	// Check if any of the new orderings concern a step id which is greater than we currently
	// have stored.
	StepID max_step_id = (ordering.before_id() < ordering.after_id() ? ordering.after_id() : ordering.before_id());
	if (max_step_id >= orderings_.size())
	{
		// Add new bitsets for the new step(s).
		while (max_step_id >= orderings_.size())
		{
			orderings_.push_back(new boost::dynamic_bitset<>());
		}

		// Extend the existing and new bitsets.
		for (std::vector<boost::dynamic_bitset<>*>::const_iterator ci = orderings_.begin(); ci != orderings_.end(); ci++)
		{
			(*ci)->resize(max_step_id + 1, true);
		}

		biggest_step_id_ = max_step_id;
	}

	if (Logging::verbosity <= Logging::DEBUG)
	{
		std::cout << "Highest index " << biggest_step_id_ << std::endl;
		std::cout << "Ordering size" << orderings_.size() << std::endl;
		std::cout << "before id " << ordering.before_id() << std::endl;
		std::cout << "after id " << ordering.after_id() << std::endl;
	}

	// Having extended the bitset. We continue by imposing the actual ordering constraint.
	(*orderings_[ordering.after_id()])[ordering.before_id()] = false;

	// Now we have to search through the bitset for other orderings we can deduce from this
	// information. All steps ordered before before_id are also ordered before after_id and
	// all steps ordered after after_id are also ordered after before_id (Bweh!? - you're
	// still with me? ;)).
	for (StepID i = 0; i < biggest_step_id_; i++)
	{
		// Step id i cannot be ordered before after_id. So make sure it also cannot be ordered
		// before before_id.
		if (!canBeOrderedBefore(i, StepTime::dummy_step_time, ordering.after_id(), StepTime::dummy_step_time))
		{
			// If the step cannot be ordered after, we cannot impose the ordering.
			if (!orderAfter(i, StepTime::dummy_step_time, ordering.before_id(), StepTime::dummy_step_time))
				return false;
		}

		// The other way around, step id i cannot be ordered after before_id. So make sure it also
		// cannot be ordered after after_id.
		if (!canBeOrderedAfter(i, StepTime::dummy_step_time, ordering.before_id(), StepTime::dummy_step_time))
		{
			// If the step cannot be ordered before, we cannot impose the ordering.
			if (!orderBefore(i, StepTime::dummy_step_time, ordering.after_id(), StepTime::dummy_step_time))
				return false;
		}
	}

	// We could succesfully impose the orderings.
	return true;
}

void BinaryOrderings::print(std::ostream& os) const
{
	for (StepID i = 0; i < orderings_.size(); i++)
	{
		for (StepID j = 0; j < orderings_[i]->size(); j++)
		{
			if (canBeOrderedBefore(i, StepTime::dummy_step_time, j, StepTime::dummy_step_time) &&
			    !canBeOrderedAfter(i, StepTime::dummy_step_time, j, StepTime::dummy_step_time))
			{
				os << i << "<" << j << " ";
			}
		}
	}
}

};

