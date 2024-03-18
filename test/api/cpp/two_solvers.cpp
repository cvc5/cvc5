/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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

int main()
{
  TermManager tm;
  Solver s1(tm);
  Solver s2(tm);
  Result r = s1.checkSatAssuming(tm.mkBoolean(false));
  Result r2 = s2.checkSatAssuming(tm.mkBoolean(false));
  return r.isUnsat() && r2.isUnsat() ? 0 : 1;
}
