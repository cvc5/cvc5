/*********************                                                        */
/*! \file argument_extender_implementation.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility class for extending commandline options.
 **
 ** Utility class for extending commandline options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__OPTIONS__ARGUMENT_EXTENDER_IMPLEMENTATION_H
#define __CVC4__OPTIONS__ARGUMENT_EXTENDER_IMPLEMENTATION_H

#include <cstddef>
#include <list>

#include "options/argument_extender.h"

namespace CVC4 {
namespace options {

/**
 * Utility class for implementing command line options parsing for the
 * Options class. This allows for adding preemption arguments.
 * Preemptions are processed immediately after the current argument.
 */
class ArgumentExtenderImplementation : public ArgumentExtender {
 public:
  /** Constructs a new empty ArgumentExtender.*/
  ArgumentExtenderImplementation();

  /** Destroys an ArgumentExtender and frees its associated memory.*/
  ~ArgumentExtenderImplementation();

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
  void getArguments(int* argc, char*** argv) const override;

  /** Returns the number of arguments that are . */
  size_t numArguments() const override;

  /**
   * Inserts a copy of element into the front of the arguments list.
   * Preconditions: element is non-null and 0 terminated.
   */
  void pushFrontArgument(const char* element) override;

  /**
   * Inserts a copy of element into the back of the arguments list.
   * Preconditions: element is non-null and 0 terminated.
   */
  void pushBackArgument(const char* element) override;

  /** Removes the front of the arguments list.*/
  void popFrontArgument() override;

  /** Adds a new preemption to the arguments list. */
  void pushBackPreemption(const char* element) override;

  /**
   * Moves all of the preemptions into the front of the arguments
   * list.
   */
  void movePreemptionsToArguments() override;

  /** Returns true iff there is a pending preemption.*/
  bool hasPreemptions() const override;

 private:

  typedef std::list< char* > CharPointerList;

  /** Creates of copy of the arugments list.*/
  char** copyArguments() const;

  /** Allocates a copy and stores a copy in d_allocated.*/
  char* allocateCopy(const char* element);

  /** Contains a copy of the allocated strings.*/
  CharPointerList d_allocated;

  /**
   * A list of all of the preempted arguments. All of these pointers
   * in this list should be contained in d_allocated.
   */
  CharPointerList d_preemptions;

  /**
   * A list of all of the arguments. All of these pointers in this
   * list should be contained in d_allocated.
   */
  CharPointerList d_arguments;

};/* class ArgumentExtenderImplementation */

}/* CVC4::options namespace */
}/* CVC4 namespace */

#endif /* __CVC4__OPTIONS__ARGUMENT_EXTENDER_IMPLEMENTATION_H */
