/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of CAD proof checker.
 */

#include "theory/arith/nl/coverings/proof_checker.h"

#include "expr/sequence.h"
#include "theory/arith/arith_utilities.h"
#include "util/rational.h"
#include "util/real_algebraic_number.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

CoveringsProofRuleChecker::CoveringsProofRuleChecker(NodeManager* nm)
    : ProofRuleChecker(nm)
{
}

void CoveringsProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::ARITH_COVERINGS_UNIV, this);
  pc->registerChecker(ProofRule::COVER, this);
  pc->registerChecker(ProofRule::SGN_INV_ELIM, this);
  pc->registerChecker(ProofRule::SGN_INV_INTRO, this);
  pc->registerChecker(ProofRule::IS_ROOT_INTRO, this);
  pc->registerChecker(ProofRule::RAN_EVAL, this);
}

// TODO: check the side condition (no root of args[0] in (args[3], args[4])
// other than args[1] and args[2], which are roots when finite) using the
// Sturm sequence args[5] and the Sturm-Tarski sequences args[6] and args[7]
// of the defining polynomials of args[1] and args[2] with args[0]
Node CoveringsProofRuleChecker::checkSgnInvIntro(const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  if (args.size() != 8 || args[5].getKind() != Kind::SEXPR
      || args[6].getKind() != Kind::SEXPR || args[7].getKind() != Kind::SEXPR)
  {
    return Node::null();
  }
  return mkSgnInv(nm, args[0], args[1], args[2]);
}
// TODO: check the side condition (args[1] is a root of args[0]) using the
// Sturm-Tarski sequence args[2]
Node CoveringsProofRuleChecker::checkIsRootIntro(const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  if (args.size() != 3 || args[2].getKind() != Kind::SEXPR)
  {
    return Node::null();
  }
  return mkIsRoot(nm, args[0], args[1]);
}
// TODO: Check side condition
Node CoveringsProofRuleChecker::checkCover(const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  if (args.size() != 2 || args[1].getKind() != Kind::SEXPR)
  {
    return Node::null();
  }
  const Node& var = args[0];
  if (!var.getType().isRealOrInt())
  {
    return Node::null();
  }
  std::vector<Node> disjs;
  for (const Node& iv : args[1])
  {
    if (iv.getKind() != Kind::SEXPR || iv.getNumChildren() != 2)
    {
      return Node::null();
    }

    if (iv[0] == iv[1])
    {
      disjs.push_back(nm->mkNode(Kind::EQUAL, var, iv[0]));
    }
    else
    {
      std::vector<Node> conjs;
      if (iv[0].getKind() != Kind::MINUS_INFINITY)
      {
        Node conj = nm->mkNode(Kind::GT, var, iv[0]);
        conjs.push_back(conj);
      }
      if (iv[1].getKind() != Kind::PLUS_INFINITY)
      {
        Node conj = nm->mkNode(Kind::LT, var, iv[1]);
        conjs.push_back(conj);
      }
      if (conjs.empty())
      {
        return nm->mkConst(true);
      }
      disjs.push_back(nm->mkAnd(conjs));
    }
  }

  return nm->mkOr(disjs);
}

Node CoveringsProofRuleChecker::checkSgnInvElim(const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  Node var = args[0];
  Node lower = args[3];
  Node upper = args[4];
  Node piece = mkOpenPiece(nm, var, lower, upper);
  Node conc = piece.isNull() ? nm->mkConst(false) : piece.notNode();
  return conc;
}

Node CoveringsProofRuleChecker::checkRanEval(const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  Node var = args[0];
  Node r = args[1];
  return nm->mkNode(Kind::EQUAL, var, r).notNode();
}

Node CoveringsProofRuleChecker::checkInternal(ProofRule id,
                                              const std::vector<Node>& children,
                                              const std::vector<Node>& args)
{
  (void)children;  // hack for avoiding unused variable error on CI
  // TODO: Actually check the proof.
  if (id == ProofRule::ARITH_COVERINGS_UNIV)
  {
    return nodeManager()->mkConst(false);
  }
  if (id == ProofRule::COVER)
  {
    return checkCover(args);
  }
  if (id == ProofRule::SGN_INV_INTRO)
  {
    return checkSgnInvIntro(args);
  }
  if (id == ProofRule::IS_ROOT_INTRO)
  {
    return checkIsRootIntro(args);
  }
  if (id == ProofRule::SGN_INV_ELIM)
  {
    return checkSgnInvElim(args);
  }
  if (id == ProofRule::RAN_EVAL)
  {
    return checkRanEval(args);
  }
  return Node::null();
}

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
