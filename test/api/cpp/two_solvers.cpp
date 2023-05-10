/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple test of multiple SmtEngines.
 */

#include <cvc5/cvc5.h>

#include <iostream>
#include <sstream>

using namespace cvc5;
using namespace std;

int main() {
  Solver s1;
  Solver s2;
  Result r = s1.checkSatAssuming(s1.mkBoolean(false));
  Result r2 = s2.checkSatAssuming(s2.mkBoolean(false));
  return r.isUnsat() && r2.isUnsat() ? 0 : 1;
}

