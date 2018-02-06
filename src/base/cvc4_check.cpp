/*********************                                                        */
/*! \file cvc4_check.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Assertion utility classes, functions and macros.
 **
 ** Implementation of assertion utility classes, functions and macros.
 **/

#include "base/cvc4_check.h"

#include <cstdlib>
#include <iostream>

namespace CVC4 {

FatalStream::FatalStream(const char* function, const char* file, int line)
{
  stream() << "Fatal failure within " << function << " at " << file << ":"
           << line << "\n";
}

FatalStream::~FatalStream()
{
  Flush();
  abort();
}

std::ostream& FatalStream::stream() { return std::cerr; }

void FatalStream::Flush()
{
  stream() << std::endl;
  stream().flush();
}

}  // namespace CVC4
