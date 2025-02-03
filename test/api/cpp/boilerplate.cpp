/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple start-up/tear-down test for cvc5.
 *
 * This simple test just makes sure that the public interface is
 * minimally functional.  It is useful as a template to use for other
 * system tests.
 */

#include <cvc5/cvc5.h>

#include <iostream>
#include <sstream>

using namespace cvc5;
using namespace std;

int main()
{
  TermManager tm;
  Solver slv(tm);
  Result r = slv.checkSatAssuming(tm.mkBoolean(false));
  return r.isUnsat() ? 0 : 1;
}
