/*********************                                                        */
/*! \file boilerplate.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A simple start-up/tear-down test for CVC4.
 **
 ** This simple test just makes sure that the public interface is
 ** minimally functional.  It is useful as a template to use for other
 ** system tests.
 **/

#include <iostream>
#include <sstream>

#include "expr/expr.h"
#include "smt/smt_engine.h"

using namespace CVC4;
using namespace std;

int main() {
  ExprManager em;
  Options opts;
  SmtEngine smt(&em);
  Result r = smt.query(em.mkConst(true));

  return r == Result::VALID ? 0 : 1;
}

