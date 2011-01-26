#ifndef MYPOP_POINTERS_H
#define MYPOP_POINTERS_H

#include <boost/shared_ptr.hpp>

namespace MyPOP {

/**
 * All temporal pointer types used by the planner. When working with partial plans
 * some properties are shared between these. For example:
 * - Steps are always monotonically increasing, once added to a plan all its children
 * will have the same steps.
 * - Likewise, links will never be broken once established. If then need to be broken
 * the planner will have to backtrack.
 * - Flaws are shared among multiple plans, so we want to have only a single
 * object in memory at any given time.
 */

class Flaw;
typedef boost::shared_ptr<const Flaw> FlawPtr;

class OpenCondition;
typedef boost::shared_ptr<const OpenCondition> OpenConditionPtr;

class Mutex;
typedef boost::shared_ptr<const Mutex> MutexPtr;

class Unsafe;
typedef boost::shared_ptr<const Unsafe> UnsafePtr;

class Step;
typedef boost::shared_ptr<const Step> StepPtr;

class Link;
typedef boost::shared_ptr<const Link> LinkPtr;

/**
 * When defining the domain of a variable, we can say that the domain of two variables are
 * equal. Thus they share the same set of objects which is easier to maintain if the set of
 * objects is an external object the VariableDomain objects have a pointer to.
 */
//class VariableDomain;
//typedef boost::shared_ptr<VariableDomain> VariableDomainPtr;

};

#endif
