/*********************                                                        */
/*! \file theory_bool.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory of booleans.
 **
 ** The theory of booleans.
 **/

#include "theory/booleans/theory_bool.h"

#include <stack>
#include <vector>

#include "expr/proof_node_manager.h"
#include "smt_util/boolean_simplification.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory.h"
#include "theory/valuation.h"
#include "util/hash.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace booleans {

TheoryBool::TheoryBool(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo,
                       ProofNodeManager* pnm)
    : Theory(THEORY_BOOL, c, u, out, valuation, logicInfo, pnm)
{
  ProofChecker* pc = pnm != nullptr ? pnm->getChecker() : nullptr;
  if (pc != nullptr)
  {
    // add checkers
    d_bProofChecker.registerTo(pc);
  }
}

Theory::PPAssertStatus TheoryBool::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  if (in.getKind() == kind::CONST_BOOLEAN && !in.getConst<bool>()) {
    // If we get a false literal, we're in conflict
    return PP_ASSERT_STATUS_CONFLICT;
  }

  // Add the substitution from the variable to its value
  if (in.getKind() == kind::NOT) {
    if (in[0].isVar())
    {
      outSubstitutions.addSubstitutionSolved(
          in[0], NodeManager::currentNM()->mkConst<bool>(false), tin);
      return PP_ASSERT_STATUS_SOLVED;
    }
  } else {
    if (in.isVar())
    {
      outSubstitutions.addSubstitutionSolved(
          in, NodeManager::currentNM()->mkConst<bool>(true), tin);
      return PP_ASSERT_STATUS_SOLVED;
    }
  }

  return Theory::ppAssert(tin, outSubstitutions);
}

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
