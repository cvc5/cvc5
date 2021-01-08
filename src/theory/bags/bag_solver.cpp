/*********************                                                        */
/*! \file bag_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief solver for the theory of bags.
 **
 ** solver for the theory of bags.
 **/

#include "theory/bags/bag_solver.h"

#include "theory/bags/inference_generator.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

BagSolver::BagSolver(SolverState& s, InferenceManager& im, TermRegistry& tr)
    : d_state(s), d_im(im), d_termReg(tr)
{
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

BagSolver::~BagSolver() {}

void BagSolver::postCheck()
{
  for (const Node& n : d_state.getBags())
  {
    Kind k = n.getKind();
    switch (k)
    {
      case kind::MK_BAG: checkMkBag(n); break;
      case kind::UNION_DISJOINT: checkUnionDisjoint(n); break;
      case kind::UNION_MAX: checkUnionMax(n); break;
      case kind::DIFFERENCE_SUBTRACT: checkDifferenceSubtract(n); break;
      default: break;
    }
  }
}

void BagSolver::checkUnionDisjoint(const Node& n)
{
  Assert(n.getKind() == UNION_DISJOINT);
  TypeNode elementType = n.getType().getBagElementType();
  for (const Node& e : d_state.getElements(elementType))
  {
    InferenceGenerator ig(&d_state);
    InferInfo i = ig.unionDisjoint(n, e);
    i.process(&d_im, true);
    Trace("bags::BagSolver::postCheck") << i << endl;
  }
}

void BagSolver::checkUnionMax(const Node& n)
{
  Assert(n.getKind() == UNION_MAX);
  TypeNode elementType = n.getType().getBagElementType();
  for (const Node& e : d_state.getElements(elementType))
  {
    InferenceGenerator ig(&d_state);
    InferInfo i = ig.unionMax(n, e);
    i.process(&d_im, true);
    Trace("bags::BagSolver::postCheck") << i << endl;
  }
}

void BagSolver::checkDifferenceSubtract(const Node& n)
{
  Assert(n.getKind() == DIFFERENCE_SUBTRACT);
  TypeNode elementType = n.getType().getBagElementType();
  for (const Node& e : d_state.getElements(elementType))
  {
    InferenceGenerator ig(&d_state);
    InferInfo i = ig.differenceSubtract(n, e);
    i.process(&d_im, true);
    Trace("bags::BagSolver::postCheck") << i << endl;
  }
}
void BagSolver::checkMkBag(const Node& n)
{
  Assert(n.getKind() == MK_BAG);
  TypeNode elementType = n.getType().getBagElementType();
  for (const Node& e : d_state.getElements(elementType))
  {
    InferenceGenerator ig(&d_state);
    InferInfo i = ig.mkBag(n, e);
    i.process(&d_im, true);
    Trace("bags::BagSolver::postCheck") << i << endl;
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
