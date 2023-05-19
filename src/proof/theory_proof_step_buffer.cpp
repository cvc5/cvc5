/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of theory proof step buffer utility.
 */

#include "proof/theory_proof_step_buffer.h"

#include "proof/proof.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

TheoryProofStepBuffer::TheoryProofStepBuffer(ProofChecker* pc,
                                             bool ensureUnique,
                                             bool autoSym)
    : ProofStepBuffer(pc, ensureUnique, autoSym)
{
}

bool TheoryProofStepBuffer::applyEqIntro(Node src,
                                         Node tgt,
                                         const std::vector<Node>& exp,
                                         MethodId ids,
                                         MethodId ida,
                                         MethodId idr,
                                         bool useExpected)
{
  std::vector<Node> args;
  args.push_back(src);
  addMethodIds(args, ids, ida, idr);
  bool added;
  Node expected = src.eqNode(tgt);
  Node res = tryStep(added,
                     PfRule::MACRO_SR_EQ_INTRO,
                     exp,
                     args,
                     useExpected ? expected : Node::null());
  if (res.isNull())
  {
    // failed to apply
    return false;
  }
  // should have concluded the expected equality
  if (res != expected)
  {
    // did not provide the correct target
    if (added)
    {
      popStep();
    }
    return false;
  }
  // successfully proved src == tgt.
  return true;
}

bool TheoryProofStepBuffer::applyPredTransform(Node src,
                                               Node tgt,
                                               const std::vector<Node>& exp,
                                               MethodId ids,
                                               MethodId ida,
                                               MethodId idr,
                                               bool useExpected)
{
  // symmetric equalities
  if (d_autoSym && CDProof::isSame(src, tgt))
  {
    return true;
  }
  std::vector<Node> children;
  children.push_back(src);
  std::vector<Node> args;
  // try to prove that tgt rewrites to src
  children.insert(children.end(), exp.begin(), exp.end());
  args.push_back(tgt);
  addMethodIds(args, ids, ida, idr);
  Node res = tryStep(PfRule::MACRO_SR_PRED_TRANSFORM,
                     children,
                     args,
                     useExpected ? tgt : Node::null());
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
                                           MethodId ida,
                                           MethodId idr,
                                           bool useExpected)
{
  std::vector<Node> args;
  args.push_back(tgt);
  addMethodIds(args, ids, ida, idr);
  Node res = tryStep(
      PfRule::MACRO_SR_PRED_INTRO, exp, args, useExpected ? tgt : Node::null());
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
                                          MethodId ida,
                                          MethodId idr)
{
  std::vector<Node> children;
  children.push_back(src);
  children.insert(children.end(), exp.begin(), exp.end());
  std::vector<Node> args;
  addMethodIds(args, ids, ida, idr);
  bool added;
  Node srcRew = tryStep(added, PfRule::MACRO_SR_PRED_ELIM, children, args);
  if (d_autoSym && added && CDProof::isSame(src, srcRew))
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
  std::unordered_set<TNode> clauseSet;
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
    addStep(PfRule::NOT_NOT_ELIM, {n}, {}, n[0][0]);
    return n[0][0];
  }
  return n;
}

}  // namespace cvc5::internal
