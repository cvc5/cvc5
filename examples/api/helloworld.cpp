/*********************                                                        */
/*! \file helloworld.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A very simple CVC4 example
 **
 ** A very simple CVC4 tutorial example.
 **/

#include <iostream>

#include <cvc4/api/cvc4cpp.h>

using namespace CVC4::api;

int main()
{
  Solver slv;
  Term helloworld = slv.mkVar(slv.getBooleanSort(), "Hello World!");
  std::cout << helloworld << " is " << slv.checkEntailed(helloworld)
            << std::endl;
  return 0;
}
