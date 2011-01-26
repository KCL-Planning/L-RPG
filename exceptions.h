#ifndef MYPOP_EXCEPTIONS_H
#define MYPOP_EXCEPTIONS_H

#include <exception>

namespace MyPOP {

/**
 * The bindings class holds maps a pair of step id and variable to the variable domain
 * of all values the variable can take. The planner is not allowed to request a pair
 * which does not exists. Failing to do so will result in an exception.
 */
class RequestNonExistingVariableBindingException : public std::exception
{
public:
    RequestNonExistingVariableBindingException() {}
};

};

#endif
