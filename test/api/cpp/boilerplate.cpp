/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

#include <iostream>
#include <sstream>

#include "api/cpp/cvc5.h"

using namespace cvc5::api;
using namespace std;

int main() {
  Solver slv;
  Result r = slv.checkEntailed(slv.mkBoolean(true));
  return r.isEntailed() ? 0 : 1;
}

