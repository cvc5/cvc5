/*********************                                                        */
/*! \file theory_proof_step_buffer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of theory proof step buffer utility
 **/

#include "theory/theory_proof_step_buffer.h"

#include "expr/proof.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

TheoryProofStepBuffer::TheoryProofStepBuffer(ProofChecker* pc)
    : ProofStepBuffer(pc)
{
}

bool TheoryProofStepBuffer::applyPredTransform(Node src,
                                               Node tgt,
                                               const std::vector<Node>& exp,
                                               MethodId ids,
                                               MethodId idr)
{
  // symmetric equalities
  if (CDProof::isSame(src, tgt))
  {
    return true;
  }
  std::vector<Node> children;
  children.push_back(src);
  std::vector<Node> args;
  // try to prove that tgt rewrites to src
  children.insert(children.end(), exp.begin(), exp.end());
  args.push_back(tgt);
  builtin::BuiltinProofRuleChecker::addMethodIds(args, ids, idr);
  Node res = tryStep(PfRule::MACRO_SR_PRED_TRANSFORM, children, args);
  if (res.isNull())
  {
    // failed to apply
    return false;
  }
  // should definitely have concluded tgt
  Assert(res == tgt);
  return true;
}

bool TheoryProofStepBuffer::applyPredIntro(Node tgt,
                                           const std::vector<Node>& exp,
                                           MethodId ids,
                                           MethodId idr)
{
  std::vector<Node> args;
  args.push_back(tgt);
  builtin::BuiltinProofRuleChecker::addMethodIds(args, ids, idr);
  Node res = tryStep(PfRule::MACRO_SR_PRED_INTRO, exp, args);
  if (res.isNull())
  {
    return false;
  }
  Assert(res == tgt);
  return true;
}

Node TheoryProofStepBuffer::applyPredElim(Node src,
                                          const std::vector<Node>& exp,
                                          MethodId ids,
                                          MethodId idr)
{
  std::vector<Node> children;
  children.push_back(src);
  children.insert(children.end(), exp.begin(), exp.end());
  std::vector<Node> args;
  builtin::BuiltinProofRuleChecker::addMethodIds(args, ids, idr);
  Node srcRew = tryStep(PfRule::MACRO_SR_PRED_ELIM, children, args);
  if (CDProof::isSame(src, srcRew))
  {
    popStep();
  }
  return srcRew;
}

}  // namespace theory
}  // namespace CVC4
