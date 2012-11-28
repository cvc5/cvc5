/*********************                                                        */
/*! \file helloworld.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A very simple CVC4 example
 **
 ** A very simple CVC4 tutorial example.
 **/

#include <iostream>
#warning "To use helloworld.cpp as given in the wiki, instead of make examples, change the following two includes lines."
#include "smt/smt_engine.h" // for use with make examples
//#include <cvc4/cvc4.h> // To follow the wiki
using namespace CVC4;
int main() {
  ExprManager em;
  Expr helloworld = em.mkVar("Hello World!", em.booleanType());
  SmtEngine smt(&em);
  std::cout << helloworld << " is " << smt.query(helloworld) << std::endl;
  return 0;
}
