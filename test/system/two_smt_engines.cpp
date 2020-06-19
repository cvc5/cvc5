/*********************                                                        */
/*! \file two_smt_engines.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple test of multiple SmtEngines
 **
 ** A simple test of multiple SmtEngines.
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
  SmtEngine smt2(&em);
  Result r = smt.checkEntailed(em.mkConst(true));
  Result r2 = smt2.checkEntailed(em.mkConst(true));

  return r == Result::ENTAILED && r2 == Result::ENTAILED ? 0 : 1;
}

