/*********************                                                        */
/*! \file argument_extender_implementation.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility class for parsing commandline options.
 **
 ** Utility class for parsing commandline options.
 **/

#include "options/argument_extender_implementation.h"

#include <cstdlib>
#include <cstring>
#include <list>

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "options/argument_extender.h"

namespace CVC4 {
namespace options {

ArgumentExtenderImplementation::ArgumentExtenderImplementation()
  : d_allocated()
  , d_preemptions()
  , d_arguments()
{
}

ArgumentExtenderImplementation::~ArgumentExtenderImplementation(){
  for(CharPointerList::iterator i = d_allocated.begin(),
        iend = d_allocated.end(); i != iend; ++i) {
    char* current = *i;
    Debug("options") << "~ArgumentExtenderImplementation " << current
    << std::endl;
    free(current);
  }
  d_allocated.clear();
}

size_t ArgumentExtenderImplementation::numArguments() const {
  return d_arguments.size();
}

char* ArgumentExtenderImplementation::allocateCopy(const char* element) {
  Assert(element != NULL);

  char* duplicate = strdup(element);
  Assert(duplicate != NULL);
  d_allocated.push_back(duplicate);
  return duplicate;
}

bool ArgumentExtenderImplementation::hasPreemptions() const {
  return !d_preemptions.empty();
}

void ArgumentExtenderImplementation::pushBackPreemption(const char* element) {
  d_preemptions.push_back(allocateCopy(element));
}

void ArgumentExtenderImplementation::movePreemptionsToArguments() {
  d_arguments.splice(d_arguments.begin(), d_preemptions);
}

void ArgumentExtenderImplementation::popFrontArgument() {
  Assert(!d_arguments.empty());
  Debug("options") << "ArgumentExtenderImplementation::popFrontArgument "
                   << d_arguments.front() << std::endl;
  d_arguments.pop_front();
}

void ArgumentExtenderImplementation::pushFrontArgument(const char* element) {
  d_arguments.push_front(allocateCopy(element));
}

void ArgumentExtenderImplementation::pushBackArgument(const char* element) {
  d_arguments.push_back(allocateCopy(element));
}

void ArgumentExtenderImplementation::getArguments(int* argc, char*** argv)
  const {
  Assert(argc != NULL);
  Assert(argv != NULL);

  *argc = numArguments();
  *argv = copyArguments();
}

char** ArgumentExtenderImplementation::copyArguments() const {
  int size = numArguments();
  Assert(size >= 0);

  char** array = (char**) malloc( sizeof(char*) * size );
  Assert(array != NULL);
  int position = 0;
  for(std::list< char* >::const_iterator i = d_arguments.begin(),
        iend = d_arguments.end(); i != iend; ++i, ++position) {
    char* at_position = *i;
    array[position] = at_position;
  }

  return array;
}

}/* CVC4::options namespace */
}/* CVC4 namespace */
