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

Node TheoryProofStepBuffer::factorReorderElimDoubleNeg(Node n)
{
  if (n.getKind() != kind::OR)
  {
    return elimDoubleNegLit(n);
  }
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> children{n.begin(), n.end()};
  std::vector<Node> childrenEqs;
  // eliminate double neg for each lit. Do it first because it may expose
  // duplicates
  bool hasDoubleNeg = false;
  for (unsigned i = 0; i < children.size(); ++i)
  {
    if (children[i].getKind() == kind::NOT
        && children[i][0].getKind() == kind::NOT)
    {
      hasDoubleNeg = true;
      childrenEqs.push_back(children[i].eqNode(children[i][0][0]));
      addStep(PfRule::MACRO_SR_PRED_INTRO,
              {},
              {childrenEqs.back()},
              childrenEqs.back());
      // update child
      children[i] = children[i][0][0];
    }
    else
    {
      childrenEqs.push_back(children[i].eqNode(children[i]));
      addStep(PfRule::REFL, {}, {children[i]}, childrenEqs.back());
    }
  }
  if (hasDoubleNeg)
  {
    Node oldn = n;
    n = nm->mkNode(kind::OR, children);
    // Create a congruence step to justify replacement of each doubly negated
    // literal. This is done to avoid having to use MACRO_SR_PRED_TRANSFORM
    // from the old clause to the new one, which, under the standard rewriter,
    // may not hold. An example is
    //
    //   ---------------------------------------------------------------------
    //   (or (or (not x2) x1 x2) (not (not x2))) = (or (or (not x2) x1 x2) x2)
    //
    // which fails due to factoring not happening after flattening.
    //
    // Using congruence only the
    //
    //  ------------------ MACRO_SR_PRED_INTRO
    //  (not (not t)) = t
    //
    // steps are added, which, since double negation is eliminated in a
    // pre-rewrite in the Boolean rewriter, will always hold under the
    // standard rewriter.
    Node congEq = oldn.eqNode(n);
    addStep(PfRule::CONG,
            childrenEqs,
            {ProofRuleChecker::mkKindNode(kind::OR)},
            congEq);
    // add an equality resolution step to derive normalize clause
    addStep(PfRule::EQ_RESOLVE, {oldn, congEq}, {}, n);
  }
  children.clear();
  // remove duplicates while keeping the order of children
  std::unordered_set<TNode, TNodeHashFunction> clauseSet;
  unsigned size = n.getNumChildren();
  for (unsigned i = 0; i < size; ++i)
  {
    if (clauseSet.count(n[i]))
    {
      continue;
    }
    children.push_back(n[i]);
    clauseSet.insert(n[i]);
  }
  // if factoring changed
  if (children.size() < size)
  {
    Node factored = children.empty()
                        ? nm->mkConst<bool>(false)
                        : children.size() == 1 ? children[0]
                                               : nm->mkNode(kind::OR, children);
    // don't overwrite what already has a proof step to avoid cycles
    addStep(PfRule::FACTORING, {n}, {}, factored);
    n = factored;
  }
  // nothing to order
  if (children.size() < 2)
  {
    return n;
  }
  // order
  std::sort(children.begin(), children.end());
  Node ordered = nm->mkNode(kind::OR, children);
  // if ordering changed
  if (ordered != n)
  {
    // don't overwrite what already has a proof step to avoid cycles
    addStep(PfRule::REORDERING, {n}, {ordered}, ordered);
  }
  return ordered;
}

Node TheoryProofStepBuffer::elimDoubleNegLit(Node n)
{
  // eliminate double neg
  if (n.getKind() == kind::NOT && n[0].getKind() == kind::NOT)
  {
    addStep(PfRule::MACRO_SR_PRED_TRANSFORM, {n}, {n[0][0]}, n[0][0]);
    return n[0][0];
  }
  return n;
}

}  // namespace theory
}  // namespace CVC4
