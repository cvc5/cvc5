/*********************                                                        */
/*! \file cad_solver.cpp
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

#include "theory/arith/cad_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

CadSolver::CadSolver(TheoryArith& containing, NlModel& model)
    : d_containing(containing),
      d_model(model)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  d_zero = nm->mkConst(Rational(0));
  d_one = nm->mkConst(Rational(1));
  d_neg_one = nm->mkConst(Rational(-1));
}

CadSolver::~CadSolver() {}

void CadSolver::initLastCall(const std::vector<Node>& assertions,
                              const std::vector<Node>& false_asserts,
                              const std::vector<Node>& xts)
{
  Trace("nln-check") << "CadSolver::initLastCall" << std::endl;

}

std::vector<Node> CadSolver::checkInitialRefine()
{
  Trace("nln-check") << "CadSolver::checkInitialRefine" << std::endl;
  std::vector<Node> lems;
  
  return lems;
}

std::vector<Node> CadSolver::checkFullRefine()
{
  Trace("iand-check") << "CadSolver::checkFullRefine";
  std::vector<Node> lems;
  
  return lems;
}


}  // namespace arith
}  // namespace theory
}  // namespace CVC4
