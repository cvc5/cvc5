/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Hans-Jörg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of theory proof step buffer utility.
 */

#include "proof/theory_proof_step_buffer.h"

#include "expr/skolem_manager.h"
#include "proof/proof.h"
#include "util/rational.h"

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
                     ProofRule::MACRO_SR_EQ_INTRO,
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
  if (src == tgt || (d_autoSym && CDProof::isSame(src, tgt)))
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
  Node res = tryStep(ProofRule::MACRO_SR_PRED_TRANSFORM,
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
  Node res = tryStep(ProofRule::MACRO_SR_PRED_INTRO,
                     exp,
                     args,
                     useExpected ? tgt : Node::null());
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
  Node srcRew = tryStep(added, ProofRule::MACRO_SR_PRED_ELIM, children, args);
  if (d_autoSym && added && CDProof::isSame(src, srcRew))
  {
    popStep();
  }
  return srcRew;
}

bool TheoryProofStepBuffer::applyExtendedPredInfer(Node src,
                                                   Node tgt,
                                                   const std::vector<Node>& exp)
{
  if (applyPredTransform(src, tgt, exp))
  {
    return true;
  }
  bool success = false;
  // more aggressive
  Node srco = SkolemManager::getOriginalForm(src);
  Node psrco = applyPredElim(srco,
                             exp,
                             MethodId::SB_DEFAULT,
                             MethodId::SBA_SEQUENTIAL,
                             MethodId::RW_EXT_REWRITE);
  Node tgto = SkolemManager::getOriginalForm(tgt);
  if (psrco == tgto)
  {
    applyPredTransform(src, srco, {});
    applyPredTransform(tgto, tgt, {});
    return true;
  }
  Node ptgto = applyPredElim(tgto,
                             exp,
                             MethodId::SB_DEFAULT,
                             MethodId::SBA_SEQUENTIAL,
                             MethodId::RW_EXT_REWRITE);
  Trace("tpsb-debug") << "applyExtendedPredInfer: " << exp << " => " << src
                      << " == " << tgt << std::endl;
  Trace("tpsb-debug") << "- " << psrco << " (from " << src << ")" << std::endl;
  Trace("tpsb-debug") << "- " << ptgto << " (from " << tgt << ")" << std::endl;
  if (psrco == ptgto)
  {
    success = true;
    Trace("tpsb-debug") << "...equal to target" << std::endl;
  }
  else if (psrco.getKind() == Kind::AND)
  {
    // see if src rewrites to (and ... tgt ...). In this case, we can
    // infer tgt via AND_ELIM.
    for (size_t i = 0, nchild = psrco.getNumChildren(); i < nchild; i++)
    {
      if (psrco[i] == ptgto)
      {
        success = true;
        NodeManager* nm = NodeManager::currentNM();
        Node ni = nm->mkConstInt(Rational(i));
        addStep(ProofRule::AND_ELIM, {psrco}, {ni}, ptgto);
        Trace("tpsb-debug")
            << "...equal to target after AND_ELIM " << i << std::endl;
        break;
      }
    }
  }
  if (success)
  {
    // If we were successful, now go back and justify the conversion to
    // original forms, which should be trivial.
    applyPredTransform(src, srco, {});
    applyPredTransform(srco,
                       tgto,
                       exp,
                       MethodId::SB_DEFAULT,
                       MethodId::SBA_SEQUENTIAL,
                       MethodId::RW_EXT_REWRITE);
    applyPredTransform(tgto, tgt, {});
  }
  return success;
}

Node TheoryProofStepBuffer::factorReorderElimDoubleNeg(Node n)
{
  if (n.getKind() != Kind::OR)
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
    if (children[i].getKind() == Kind::NOT
        && children[i][0].getKind() == Kind::NOT)
    {
      hasDoubleNeg = true;
      childrenEqs.push_back(children[i].eqNode(children[i][0][0]));
      addStep(ProofRule::MACRO_SR_PRED_INTRO,
              {},
              {childrenEqs.back()},
              childrenEqs.back());
      // update child
      children[i] = children[i][0][0];
    }
    else
    {
      childrenEqs.push_back(children[i].eqNode(children[i]));
      addStep(ProofRule::REFL, {}, {children[i]}, childrenEqs.back());
    }
  }
  if (hasDoubleNeg)
  {
    Node oldn = n;
    n = nm->mkNode(Kind::OR, children);
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
    addStep(ProofRule::NARY_CONG,
            childrenEqs,
            {ProofRuleChecker::mkKindNode(Kind::OR)},
            congEq);
    // add an equality resolution step to derive normalize clause
    addStep(ProofRule::EQ_RESOLVE, {oldn, congEq}, {}, n);
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
    Node factored = children.empty()       ? nm->mkConst<bool>(false)
                    : children.size() == 1 ? children[0]
                                           : nm->mkNode(Kind::OR, children);
    // don't overwrite what already has a proof step to avoid cycles
    addStep(ProofRule::FACTORING, {n}, {}, factored);
    n = factored;
  }
  // nothing to order
  if (children.size() < 2)
  {
    return n;
  }
  // order
  std::sort(children.begin(), children.end());
  Node ordered = nm->mkNode(Kind::OR, children);
  // if ordering changed
  if (ordered != n)
  {
    // don't overwrite what already has a proof step to avoid cycles
    addStep(ProofRule::REORDERING, {n}, {ordered}, ordered);
  }
  return ordered;
}

Node TheoryProofStepBuffer::elimDoubleNegLit(Node n)
{
  // eliminate double neg
  if (n.getKind() == Kind::NOT && n[0].getKind() == Kind::NOT)
  {
    addStep(ProofRule::NOT_NOT_ELIM, {n}, {}, n[0][0]);
    return n[0][0];
  }
  return n;
}

}  // namespace cvc5::internal
