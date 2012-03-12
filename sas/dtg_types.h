#ifndef SAS_PLUS_TYPES_H
#define SAS_PLUS_TYPES_H

#include <limits>

/**
 * Every atom in a DTG atom has a invariable index. This index marks the variable which 
 * is not affected by the transitions through the DTG. The combination of a predicate and
 * the invariable index is a unique identifier for atoms in a DTG node.
 */
typedef unsigned int InvariableIndex;
const InvariableIndex NO_INVARIABLE_INDEX = std::numeric_limits<unsigned int>::max();

// Used as a parameter to methods, indicates the caller does not care about the index of the invariable 
// and the function should ignore that parameter.
const InvariableIndex ALL_INVARIABLE_INDEXES = std::numeric_limits<unsigned int>::max() - 1;

#endif
