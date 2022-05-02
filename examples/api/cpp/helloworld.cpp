/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A very simple cvc5 example.
 */

#include <cvc5/cvc5.h>

#include <iostream>

using namespace cvc5;

int main()
{
  Solver slv;
  Term helloworld = slv.mkConst(slv.getBooleanSort(), "Hello World!");
  std::cout << helloworld << " is " << slv.checkSatAssuming(helloworld)
            << std::endl;
  return 0;
}
