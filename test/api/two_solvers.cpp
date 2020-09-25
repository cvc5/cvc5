/*********************                                                        */
/*! \file two_solvers.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple test of multiple SmtEngines
 **
 ** A simple test of multiple SmtEngines.
 **/

#include <iostream>
#include <sstream>

#include "api/cvc4cpp.h"

using namespace CVC4::api;
using namespace std;

int main() {
  Solver s1;
  Solver s2;
  Result r = s1.checkEntailed(s1.mkBoolean(true));
  Result r2 = s2.checkEntailed(s2.mkBoolean(true));
  return r.isEntailed() && r2.isEntailed() ? 0 : 1;
}

