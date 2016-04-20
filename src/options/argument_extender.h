/*********************                                                        */
/*! \file argument_extender.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Abstract utility class for extending commandline options.
 **
 ** Abstract utility class for extending commandline options.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__OPTIONS__ARGUMENT_EXTENDER_H
#define __CVC4__OPTIONS__ARGUMENT_EXTENDER_H

#include <cstddef>

namespace CVC4 {
namespace options {

/**
 * Abstract utility class for implementing command line options
 * parsing for the Options class. This allows for adding preemption
 * arguments. A preemption is effectivly adding a new argument into
 * the commandline arguments and must be processed immediately.
 */
class ArgumentExtender {
public:
  ArgumentExtender(){}
  virtual ~ArgumentExtender(){}

  /**
   * This creates a copy of the current arguments list as a new array.
   * The new array is stored in argv.  The user of this function is
   * expected to own the memory of the string array, but not the
   * strings themselves.  The length of the new array is
   * numArguments() and is stored in argc.
   *
   * Preconditions:
   * - argc and argv are non-null.
   */
  virtual void getArguments(int* argc, char*** argv) const = 0;

  /** Returns the number of arguments that are . */
  virtual size_t numArguments() const = 0;

  /**
   * Inserts a copy of element into the front of the arguments list.
   * Preconditions: element is non-null and 0 terminated.
   */
  virtual void pushFrontArgument(const char* element) = 0;

  /**
   * Inserts a copy of element into the back of the arguments list.
   * Preconditions: element is non-null and 0 terminated.
   */
  virtual void pushBackArgument(const char* element) = 0;

  /** Removes the front of the arguments list.*/
  virtual void popFrontArgument() = 0;

  /** Adds a new preemption to the arguments list. */
  virtual void pushBackPreemption(const char* element) = 0;

  /**
   * Moves all of the preemptions into the front of the arguments
   * list.
   */
  virtual void movePreemptionsToArguments() = 0;

  /** Returns true iff there is a pending preemption.*/
  virtual bool hasPreemptions() const = 0;

};/* class ArgumentExtender */

}/* CVC4::options namespace */
}/* CVC4 namespace */

#endif /* __CVC4__OPTIONS__ARGUMENT_EXTENDER_H */
