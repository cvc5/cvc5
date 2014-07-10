/*********************                                                        */
/*! \file helloworld.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: Kshitij Bansal
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A very simple CVC4 example
 **
 ** A very simple CVC4 tutorial example.
 **/

#include <iostream>

#ifdef CVC4_MAKE_EXAMPLES
#include "smt/smt_engine.h" // for use with make examples
#else
#include <cvc4/cvc4.h>      // To follow the wiki
#endif /* CVC4_MAKE_EXAMPLES */

using namespace CVC4;
int main() {
  ExprManager em;
  Expr helloworld = em.mkVar("Hello World!", em.booleanType());
  SmtEngine smt(&em);
  std::cout << helloworld << " is " << smt.query(helloworld) << std::endl;
  return 0;
}
