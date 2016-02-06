/*********************                                                        */
/*! \file preempt_get_option.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Utility function for parsing commandline options.
 **
 ** Utility function for parsing commandline options.
 **/

#include "options/argument_extender.h"

#include <cstdlib>
#include <cstring>
#include <vector>

#include "base/cvc4_assert.h"
#include "base/output.h"

namespace CVC4 {
namespace options {

ArgumentExtender::ArgumentExtender(unsigned additional, size_t length)
    : d_additional(additional)
    , d_length(length)
{
  AlwaysAssert(d_additional >= 1);
  AlwaysAssert(d_length >= 1);
}

ArgumentExtender::~ArgumentExtender(){}

unsigned ArgumentExtender::getIncrease() const { return d_additional; }
size_t ArgumentExtender::getLength() const { return d_length; }

void ArgumentExtender::extend(int& argc, char**& argv, const char* opt,
                                std::vector<char*>& allocated)
{

  Debug("preemptGetopt") << "preempting getopt() with " << opt << std::endl;

  AlwaysAssert(opt != NULL && *opt != '\0');
  AlwaysAssert(strlen(opt) <= getLength());

  ++argc;
  unsigned i = 1;
  while(argv[i] != NULL && argv[i][0] != '\0') {
    ++i;
  }

  if(argv[i] == NULL) {
    unsigned newSize = i + getIncrease();
    argv = (char**) realloc(argv, newSize * sizeof(char*));
    for(unsigned j = i; j < newSize-1; ++j) {
      char* newString = (char*) malloc(sizeof(char) * getLength());
      newString[0] = '\0';
      argv[j] = newString;
      allocated.push_back(newString);
    }
    argv[newSize - 1] = NULL;
  }

  strncpy(argv[i], opt, getLength() - 1);
  argv[i][getLength() - 1] = '\0'; // ensure NULL-termination even on overflow
}

}/* CVC4::options namespace */
}/* CVC4 namespace */
