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

#include "theory/arith/nl/cad_solver.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "preprocessing/passes/bv_to_int.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

CadSolver::CadSolver(TheoryArith& containing, NlModel& model)
    : d_containing(containing), d_model(model)
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
  if (Trace.isOn("cad-check"))
  {
    Trace("cad-check") << "CadSolver::initLastCall" << std::endl;
    Trace("cad-check") << "* Assertions: " << std::endl;
    for (const Node& a : assertions)
    {
      Trace("cad-check") << "  " << a << std::endl;
      if (std::find(false_asserts.begin(), false_asserts.end(), a)
          != false_asserts.end())
      {
        Trace("cad-check") << " (false in candidate model)" << std::endl;
      }
    }
    Trace("cad-check") << "* Extended terms: " << std::endl;
    for (const Node& t : xts)
    {
      Trace("cad-check") << "  " << t << std::endl;
    }
  }
  // store or process assertions
}

std::vector<NlLemma> CadSolver::checkInitialRefine()
{
  Trace("cad-check") << "CadSolver::checkInitialRefine" << std::endl;
  std::vector<NlLemma> lems;

  // add lemmas corresponding to easy conflicts or refinements based on
  // the assertions/terms given in initLastCall.

  return lems;
}

std::vector<NlLemma> CadSolver::checkFullRefine()
{
  Trace("cad-check") << "CadSolver::checkFullRefine";
  std::vector<NlLemma> lems;

  // Run a complete check on assertions/terms given in initLastCall. In other
  // words, do not return any lemmas if

  return lems;
}

void CadSolver::preprocessAssertionsCheckModel(std::vector<Node>& assertions) {}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
