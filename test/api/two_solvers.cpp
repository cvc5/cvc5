/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple test of multiple SmtEngines.
 */

#include <iostream>
#include <sstream>

#include "api/cpp/cvc5.h"

using namespace cvc5::api;
using namespace std;

int main() {
  Solver s1;
  Solver s2;
  Result r = s1.checkEntailed(s1.mkBoolean(true));
  Result r2 = s2.checkEntailed(s2.mkBoolean(true));
  return r.isEntailed() && r2.isEntailed() ? 0 : 1;
}

