/*********************                                                        */
/*! \file nln_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of new non-linear solver
 **/

#include "theory/arith/nln_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "util/iand.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

NlnSolver::NlnSolver(TheoryArith& containing, NlModel& model)
    : d_containing(containing),
      d_model(model),
      d_initRefine(containing.getUserContext())
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_two = nm->mkConst(Rational(2));
  d_neg_one = nm->mkConst(Rational(-1));
}

NlnSolver::~NlnSolver() {}

void NlnSolver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  Trace("nln-check") << "NlnSolver::initLastCall" << std::endl;

}

std::vector<Node> NlnSolver::checkInitialRefine()
{
  Trace("nln-check") << "NlnSolver::checkInitialRefine" << std::endl;
  std::vector<Node> lems;
  
  return lems;
}

std::vector<Node> NlnSolver::checkFullRefine()
{
  Trace("iand-check") << "NlnSolver::checkFullRefine";
  std::vector<Node> lems;
  
  return lems;
}


}  // namespace arith
}  // namespace theory
}  // namespace CVC4
