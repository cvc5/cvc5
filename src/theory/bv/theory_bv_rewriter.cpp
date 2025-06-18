/******************************************************************************
 * Top contributors (to current version):
 *   Leni Aniva, Liana Hadarean, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory BV rewriter.
 */

#include "theory/bv/theory_bv_rewriter.h"

#include "options/bv_options.h"
#include "theory/arith/arith_poly_norm.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_rewrite_rules_constant_evaluation.h"
#include "theory/bv/theory_bv_rewrite_rules_core.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_rewrite_rules_operator_elimination.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/theory.h"

using namespace cvc5::internal;
using namespace cvc5::internal::theory;
using namespace cvc5::internal::theory::bv;

#define TRY_REWRITE(rule)                               \
  if (RewriteRule<rule>::applies(node))                 \
  {                                                     \
    Node nrew = RewriteRule<rule>::run<false>(node);    \
    if (nrew != node)                                   \
    {                                                   \
      return RewriteResponse(REWRITE_AGAIN_FULL, nrew); \
    }                                                   \
  }

TheoryBVRewriter::TheoryBVRewriter(NodeManager* nm) : TheoryRewriter(nm)
{
  initializeRewrites();
  registerProofRewriteRule(ProofRewriteRule::MACRO_BV_EQ_SOLVE,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_BV_EXTRACT_CONCAT,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_BV_OR_SIMPLIFY,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_BV_AND_SIMPLIFY,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_BV_XOR_SIMPLIFY,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_BV_AND_OR_XOR_CONCAT_PULLUP,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_BV_MULT_SLT_MULT,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_BV_CONCAT_EXTRACT_MERGE,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_BV_CONCAT_CONSTANT_MERGE,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::BV_UMULO_ELIM,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::BV_SMULO_ELIM,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::BV_BITWISE_SLICING,
                           TheoryRewriteCtx::POST_DSL);
  registerProofRewriteRule(ProofRewriteRule::BV_REPEAT_ELIM,
                           TheoryRewriteCtx::PRE_DSL);
}

RewriteResponse TheoryBVRewriter::preRewrite(TNode node)
{
  RewriteResponse res =
      d_rewriteTable[static_cast<uint32_t>(node.getKind())](node, true);
  if (res.d_node != node)
  {
    Trace("bitvector-rewrite")
        << "TheoryBV::preRewrite    " << node << std::endl;
    Trace("bitvector-rewrite")
        << "TheoryBV::preRewrite to " << res.d_node << std::endl;
  }
  return res;
}

RewriteResponse TheoryBVRewriter::postRewrite(TNode node)
{
  RewriteResponse res =
      d_rewriteTable[static_cast<uint32_t>(node.getKind())](node, false);
  if (res.d_node != node)
  {
    Trace("bitvector-rewrite")
        << "TheoryBV::postRewrite    " << node << std::endl;
    Trace("bitvector-rewrite")
        << "TheoryBV::postRewrite to " << res.d_node << std::endl;
  }
  return res;
}
Node TheoryBVRewriter::rewriteViaRule(ProofRewriteRule id, const Node& n)
{
  switch (id)
  {
#define BV_PROOF_REWRITE_CASE(rule)                              \
  {                                                              \
    if (RewriteRule<rule>::applies(n))                           \
    {                                                            \
      return LinearRewriteStrategy<RewriteRule<rule>>::apply(n); \
    }                                                            \
    break;                                                       \
  }                                                              \
    /* end of macro */
    case ProofRewriteRule::MACRO_BV_EQ_SOLVE:
    {
      if (n.getKind() == Kind::EQUAL && n[0] != n[1])
      {
        Node ns = d_nm->mkNode(Kind::BITVECTOR_SUB, n[0], n[1]);
        Node nsn = arith::PolyNorm::getPolyNorm(ns);
        if (nsn.isConst())
        {
          return d_nm->mkConst(nsn.getConst<BitVector>().toInteger().isZero());
        }
      }
    }
    break;
    case ProofRewriteRule::MACRO_BV_EXTRACT_CONCAT:
      BV_PROOF_REWRITE_CASE(ExtractConcat)
    case ProofRewriteRule::MACRO_BV_OR_SIMPLIFY:
      BV_PROOF_REWRITE_CASE(OrSimplify)
    case ProofRewriteRule::MACRO_BV_AND_SIMPLIFY:
      BV_PROOF_REWRITE_CASE(AndSimplify)
    case ProofRewriteRule::MACRO_BV_XOR_SIMPLIFY:
      BV_PROOF_REWRITE_CASE(XorSimplify)
    case ProofRewriteRule::MACRO_BV_AND_OR_XOR_CONCAT_PULLUP:
      BV_PROOF_REWRITE_CASE(AndOrXorConcatPullUp)
    case ProofRewriteRule::MACRO_BV_MULT_SLT_MULT:
      BV_PROOF_REWRITE_CASE(MultSltMult)
    case ProofRewriteRule::MACRO_BV_CONCAT_EXTRACT_MERGE:
      BV_PROOF_REWRITE_CASE(ConcatExtractMerge)
    case ProofRewriteRule::MACRO_BV_CONCAT_CONSTANT_MERGE:
      BV_PROOF_REWRITE_CASE(ConcatConstantMerge)
    case ProofRewriteRule::BV_UMULO_ELIM:
      BV_PROOF_REWRITE_CASE(UmuloEliminate)
    case ProofRewriteRule::BV_SMULO_ELIM:
      BV_PROOF_REWRITE_CASE(SmuloEliminate)
    case ProofRewriteRule::BV_BITWISE_SLICING:
      BV_PROOF_REWRITE_CASE(BitwiseSlicing)
    case ProofRewriteRule::BV_REPEAT_ELIM:
      BV_PROOF_REWRITE_CASE(RepeatEliminate)
    default: break;
  }
  return Node::null();
}

Node TheoryBVRewriter::expandDefinition(Node node)
{
  return eliminateOverflows(node);
}

Node TheoryBVRewriter::eliminateOverflows(Node node)
{
  Node res = node;
  if (RewriteRule<UaddoEliminate>::applies(node))
  {
    res = RewriteRule<UaddoEliminate>::run<false>(node);
  }
  else if (RewriteRule<SaddoEliminate>::applies(node))
  {
    res = RewriteRule<SaddoEliminate>::run<false>(node);
  }
  else if (RewriteRule<UmuloEliminate>::applies(node))
  {
    res = RewriteRule<UmuloEliminate>::run<false>(node);
  }
  else if (RewriteRule<SmuloEliminate>::applies(node))
  {
    res = RewriteRule<SmuloEliminate>::run<false>(node);
  }
  else if (RewriteRule<UsuboEliminate>::applies(node))
  {
    res = RewriteRule<UsuboEliminate>::run<false>(node);
  }
  else if (RewriteRule<SsuboEliminate>::applies(node))
  {
    res = RewriteRule<SsuboEliminate>::run<false>(node);
  }
  return res;
}

RewriteResponse TheoryBVRewriter::RewriteBit(TNode node, bool prerewrite)
{
  Node resultNode = LinearRewriteStrategy<RewriteRule<BitConst>>::apply(node);
  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteUlt(TNode node, bool prerewrite)
{
  // reduce common subexpressions on both sides
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<EvalUlt>,  // if both arguments are
                                                   // constants evaluates
                            RewriteRule<UltSelf>,
                            RewriteRule<UltOne>,
                            RewriteRule<UltOnes>,
                            RewriteRule<UltZero>,  // a < 0 rewrites to false,
                            RewriteRule<SignExtendUltConst>,
                            RewriteRule<ZeroExtendUltConst>,
                            RewriteRule<IneqElimConversion>>::apply(node);

  return RewriteResponse(resultNode == node ? REWRITE_DONE : REWRITE_AGAIN_FULL,
                         resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteUltBv(TNode node, bool prerewrite)
{
  // reduce common subexpressions on both sides
  Node resultNode = LinearRewriteStrategy<RewriteRule<EvalUltBv>>::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSlt(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<EvalSlt>,
                            RewriteRule<SltSelf>,
                            RewriteRule<MultSltMult>>::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode);

  // Node resultNode = LinearRewriteStrategy
  //   < RewriteRule < SltEliminate >
  //     // a <_s b ==> a + 2^{n-1} <_u b + 2^{n-1}
  //     >::apply(node);

  // return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSltBv(TNode node, bool prerewrite)
{
  Node resultNode = LinearRewriteStrategy<RewriteRule<EvalSltBv>>::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteUle(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<EvalUle>,
                            RewriteRule<UleMax>,
                            RewriteRule<ZeroUle>,
                            RewriteRule<IneqElimConversion>,
                            RewriteRule<UleZero>,
                            RewriteRule<UleSelf>,
                            RewriteRule<UleEliminate>>::apply(node);
  return RewriteResponse(resultNode == node ? REWRITE_DONE : REWRITE_AGAIN,
                         resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSle(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<EvalSle>,
                            RewriteRule<SleEliminate>>::apply(node);
  return RewriteResponse(resultNode == node ? REWRITE_DONE : REWRITE_AGAIN,
                         resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteUgt(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<UgtUrem>,
                            RewriteRule<UgtEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSgt(TNode node, bool prerewrite)
{
  Node resultNode = LinearRewriteStrategy<RewriteRule<SgtEliminate>
                                          // RewriteRule<SltEliminate>
                                          >::apply(node);

  return RewriteResponse(REWRITE_AGAIN, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteUge(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<UgeEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSge(TNode node, bool prerewrite)
{
  Node resultNode = LinearRewriteStrategy<RewriteRule<SgeEliminate>
                                          //      RewriteRule<SleEliminate>
                                          >::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteITEBv(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<EvalITEBv>,
                            RewriteRule<BvIteConstCond>,
                            RewriteRule<BvIteEqualChildren>>::apply(node);
  // If the node has been rewritten, we return here because we need to make
  // sure that `BvIteEqualChildren` has been applied until we reach a fixpoint
  // before applying `BvIteConstChildren`. Otherwise, `BvIteConstChildren`
  // potentially performs an unsound rewrite. Returning hands back the control
  // to the `Rewriter` which will then call this method again, ensuring that
  // the rewrites are applied in the correct order.
  if (resultNode != node)
  {
    return RewriteResponse(REWRITE_AGAIN, resultNode);
  }

  resultNode = LinearRewriteStrategy<RewriteRule<BvIteConstChildren>,
                                     RewriteRule<BvIteEqualCond>>::apply(node);
  if (resultNode != node)
  {
    return RewriteResponse(REWRITE_AGAIN, resultNode);
  }

  resultNode =
      LinearRewriteStrategy<RewriteRule<BvIteMergeThenIf>,
                            RewriteRule<BvIteMergeElseIf>,
                            RewriteRule<BvIteMergeThenElse>,
                            RewriteRule<BvIteMergeElseElse>>::apply(node);
  return RewriteResponse(resultNode == node ? REWRITE_DONE : REWRITE_AGAIN_FULL,
                         resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteNot(TNode node, bool prerewrite)
{
  Node resultNode = node;

  resultNode =
      LinearRewriteStrategy<RewriteRule<NotIdemp>, RewriteRule<EvalNot>>::apply(
          node);

  // It is is safe to return REWRITE_DONE here, because `NotIdemp` removes all
  // pairs of `bvnot` and then `EvalNot` evaluates the remaining `bvnot` if
  // applicable.
  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteExtract(TNode node, bool prerewrite)
{
  Node resultNode = node;

  if (RewriteRule<ExtractConcat>::applies(node))
  {
    resultNode = RewriteRule<ExtractConcat>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }

  if (RewriteRule<ExtractSignExtend>::applies(node))
  {
    resultNode = RewriteRule<ExtractSignExtend>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }

  if (RewriteRule<ExtractNot>::applies(node))
  {
    resultNode = RewriteRule<ExtractNot>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }

  if (!prerewrite)
  {
    // We could have an extract over extract
    TRY_REWRITE(ExtractExtract)
  }

  resultNode = LinearRewriteStrategy<
      // The extract may cover the whole bit-vector
      RewriteRule<ExtractWhole>,
      // Rewrite extracts over wide multiplications
      RewriteRule<ExtractMultLeadingBit>,
      // Perform constant folding last to maximize chances that it applies
      RewriteRule<ExtractConstant>>::apply(node);

  // There are terms that can be rewritten by repeatedly alternating between
  // ExtractExtract and ExtractConcat, so we have to be conservative here and
  // return REWRITE_AGAIN if the node changed.
  return RewriteResponse(resultNode != node ? REWRITE_AGAIN : REWRITE_DONE,
                         resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteConcat(TNode node, bool prerewrite)
{
  TRY_REWRITE(ConcatFlatten)
  TRY_REWRITE(ConcatExtractMerge)
  Node resultNode = LinearRewriteStrategy<
      // Remove extracts that have no effect
      ApplyRuleToChildren<Kind::BITVECTOR_CONCAT, ExtractWhole>,
      // Merge the adjacent extracts on constants
      RewriteRule<ConcatConstantMerge>>::apply(node);

  // Applying ExtractWhole to the children may result in concat nodes that can
  // be flattened by this method.
  return RewriteResponse(resultNode != node ? REWRITE_AGAIN : REWRITE_DONE,
                         resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteAnd(TNode node, bool prerewrite)
{
  TRY_REWRITE(FlattenAssocCommutNoDuplicates)
  TRY_REWRITE(AndSimplify)
  TRY_REWRITE(AndOrXorConcatPullUp)
  if (!prerewrite)
  {
    TRY_REWRITE(BitwiseSlicing)
  }
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheoryBVRewriter::RewriteOr(TNode node, bool prerewrite)
{
  TRY_REWRITE(FlattenAssocCommutNoDuplicates)
  TRY_REWRITE(OrSimplify)
  TRY_REWRITE(AndOrXorConcatPullUp)
  if (!prerewrite)
  {
    TRY_REWRITE(BitwiseSlicing)
  }
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheoryBVRewriter::RewriteXor(TNode node, bool prerewrite)
{
  TRY_REWRITE(FlattenAssocCommut) // flatten the expression
  TRY_REWRITE(XorSimplify) // simplify duplicates and constants
  TRY_REWRITE(XorZero) // checks if the constant part is zero and eliminates it
  TRY_REWRITE(AndOrXorConcatPullUp)

  if (!prerewrite)
  {
    TRY_REWRITE(XorOnes)
    TRY_REWRITE(BitwiseSlicing)
  }

  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheoryBVRewriter::RewriteXnor(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<XnorEliminate>>::apply(node);
  // need to rewrite two levels in
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteNand(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<NandEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteNor(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<NorEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteComp(TNode node, bool prerewrite)
{
  Node resultNode = LinearRewriteStrategy<RewriteRule<EvalComp>>::apply(node);

  if (node == resultNode && RewriteRule<BvComp>::applies(node))
  {
    resultNode = RewriteRule<BvComp>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN, resultNode);
  }

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteConstBvSym(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<EvalConstBvSym>>::apply(node);
  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteOverflow(TNode node, bool prerewrite)
{
  // If all children are constant, we rewrite based on the definition of the
  // overflow predicate using eliminateOverflows. We require rewriting this
  // way to ensure the rewrite does constant folding, which is necessary for
  // model evaluation.
  bool allConstChildren = true;
  for (const Node& nc : node)
  {
    if (!nc.isConst())
    {
      allConstChildren = false;
      break;
    }
  }
  if (allConstChildren)
  {
    Node nodeo = eliminateOverflows(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, nodeo);
  }
  return RewriteResponse(REWRITE_DONE, node);
}
RewriteResponse TheoryBVRewriter::RewriteSize(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<SizeEliminate>>::apply(node);
  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteEagerAtom(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<EvalEagerAtom>>::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteMult(TNode node, bool prerewrite)
{
  TRY_REWRITE(FlattenAssocCommut) // flattens and sorts
  TRY_REWRITE(MultSimplify) // multiplies constant part and checks for 0

  // only apply if every subterm was already rewritten
  if (!prerewrite)
  {
    TRY_REWRITE(MultPow2) // replaces multiplication by a power of 2 by a shift
    TRY_REWRITE(MultDistribConst)
    TRY_REWRITE(MultDistrib)
  }
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheoryBVRewriter::RewriteAdd(TNode node, bool prerewrite)
{
  Node resultNode = node;
  if (prerewrite)
  {
    resultNode =
        LinearRewriteStrategy<RewriteRule<FlattenAssocCommut>>::apply(node);
    return RewriteResponse(REWRITE_DONE, resultNode);
  }

  resultNode =
      LinearRewriteStrategy<RewriteRule<FlattenAssocCommut>,
                            RewriteRule<AddCombineLikeTerms>>::apply(node);

  if (node != resultNode)
  {
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSub(TNode node, bool prerewrite)
{
  // return RewriteResponse(REWRITE_DONE, node);
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<SubEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteNeg(TNode node, bool prerewrite)
{
  Node resultNode = node;

  resultNode = LinearRewriteStrategy<RewriteRule<EvalNeg>,
                                     RewriteRule<NegIdemp>,
                                     RewriteRule<NegSub>>::apply(node);

  if (RewriteRule<NegAdd>::applies(node))
  {
    resultNode = RewriteRule<NegAdd>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }

  if (!prerewrite)
  {
    if (RewriteRule<NegMult>::applies(node))
    {
      resultNode = RewriteRule<NegMult>::run<false>(node);
      return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
    }
  }

  // There are cases where we need to rewrite the resulting term again. For
  // example, if we rewrite (bvneg (bvneg (bvneg #b0))) to (bvneg #b0) then we
  // have to rewrite again.
  return RewriteResponse(resultNode != node ? REWRITE_AGAIN : REWRITE_DONE,
                         resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteUdiv(TNode node, bool prerewrite)
{
  Node resultNode = node;

  if (RewriteRule<UdivPow2>::applies(node))
  {
    resultNode = RewriteRule<UdivPow2>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }

  resultNode = LinearRewriteStrategy<RewriteRule<EvalUdiv>,
                                     RewriteRule<UdivZero>,
                                     RewriteRule<UdivOne>>::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteUrem(TNode node, bool prerewrite)
{
  Node resultNode = node;

  if (RewriteRule<UremPow2>::applies(node))
  {
    resultNode = RewriteRule<UremPow2>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }

  resultNode = LinearRewriteStrategy<RewriteRule<EvalUrem>,
                                     RewriteRule<UremOne>,
                                     RewriteRule<UremSelf>>::apply(node);
  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSmod(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<SmodEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSdiv(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<SdivEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSrem(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<SremEliminate>>::apply(node);
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteShl(TNode node, bool prerewrite)
{
  Node resultNode = node;
  if (RewriteRule<ShlByConst>::applies(node))
  {
    resultNode = RewriteRule<ShlByConst>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }

  resultNode = LinearRewriteStrategy<RewriteRule<EvalShl>,
                                     RewriteRule<ShiftZero>>::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteLshr(TNode node, bool prerewrite)
{
  Node resultNode = node;
  if (RewriteRule<LshrByConst>::applies(node))
  {
    resultNode = RewriteRule<LshrByConst>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }

  resultNode = LinearRewriteStrategy<RewriteRule<EvalLshr>,
                                     RewriteRule<ShiftZero>>::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteAshr(TNode node, bool prerewrite)
{
  Node resultNode = node;
  if (RewriteRule<AshrByConst>::applies(node))
  {
    resultNode = RewriteRule<AshrByConst>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }

  resultNode = LinearRewriteStrategy<RewriteRule<EvalAshr>,
                                     RewriteRule<ShiftZero>>::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteRepeat(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<RepeatEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteZeroExtend(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<ZeroExtendEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSignExtend(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<MergeSignExtend>,
                            RewriteRule<EvalSignExtend>>::apply(node);

  if (resultNode != node)
  {
    return RewriteResponse(REWRITE_AGAIN, resultNode);
  }
  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteRotateRight(TNode node,
                                                     bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<RotateRightEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteRotateLeft(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<RotateLeftEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteRedor(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<RedorEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteRedand(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<RedandEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteEqual(TNode node, bool prerewrite)
{
  if (prerewrite)
  {
    Node resultNode =
        LinearRewriteStrategy<RewriteRule<FailEq>,
                              RewriteRule<SimplifyEq>,
                              RewriteRule<ReflexivityEq>>::apply(node);
    return RewriteResponse(REWRITE_DONE, resultNode);
  }
  else
  {
    Node resultNode =
        LinearRewriteStrategy<RewriteRule<FailEq>,
                              RewriteRule<SimplifyEq>,
                              RewriteRule<ReflexivityEq>>::apply(node);

    return RewriteResponse(REWRITE_DONE, resultNode);
  }
}

RewriteResponse TheoryBVRewriter::RewriteNego(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<NegoEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteSdivo(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<SdivoEliminate>>::apply(node);

  return RewriteResponse(REWRITE_AGAIN, resultNode);
}

RewriteResponse TheoryBVRewriter::IdentityRewrite(TNode node, bool prerewrite)
{
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheoryBVRewriter::UndefinedRewrite(TNode node, bool prerewrite)
{
  Trace("bv-rewrite") << "TheoryBV::UndefinedRewrite for" << node;
  Unimplemented();
}

void TheoryBVRewriter::initializeRewrites()
{
  for (unsigned i = 0; i < static_cast<uint32_t>(Kind::LAST_KIND); ++i)
  {
    d_rewriteTable[i] = IdentityRewrite;  // UndefinedRewrite;
  }

  d_rewriteTable[static_cast<uint32_t>(Kind::EQUAL)] = RewriteEqual;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_BIT)] = RewriteBit;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_ULT)] = RewriteUlt;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SLT)] = RewriteSlt;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_ULE)] = RewriteUle;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SLE)] = RewriteSle;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_UGT)] = RewriteUgt;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SGT)] = RewriteSgt;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_UGE)] = RewriteUge;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SGE)] = RewriteSge;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_NOT)] = RewriteNot;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_CONCAT)] = RewriteConcat;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_AND)] = RewriteAnd;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_OR)] = RewriteOr;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_XOR)] = RewriteXor;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_XNOR)] = RewriteXnor;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_NAND)] = RewriteNand;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_NOR)] = RewriteNor;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_COMP)] = RewriteComp;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_MULT)] = RewriteMult;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_ADD)] = RewriteAdd;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SUB)] = RewriteSub;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_NEG)] = RewriteNeg;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_UDIV)] = RewriteUdiv;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_UREM)] = RewriteUrem;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SMOD)] = RewriteSmod;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SDIV)] = RewriteSdiv;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SREM)] = RewriteSrem;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SHL)] = RewriteShl;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_LSHR)] = RewriteLshr;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_ASHR)] = RewriteAshr;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_EXTRACT)] =
      RewriteExtract;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_REPEAT)] = RewriteRepeat;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_ZERO_EXTEND)] =
      RewriteZeroExtend;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SIGN_EXTEND)] =
      RewriteSignExtend;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_ROTATE_RIGHT)] =
      RewriteRotateRight;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_ROTATE_LEFT)] =
      RewriteRotateLeft;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_REDOR)] = RewriteRedor;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_REDAND)] = RewriteRedand;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_ULTBV)] = RewriteUltBv;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SLTBV)] = RewriteSltBv;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_ITE)] = RewriteITEBv;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_NEGO)] = RewriteNego;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SDIVO)] = RewriteSdivo;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_EAGER_ATOM)] =
      RewriteEagerAtom;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SIZE)] = RewriteSize;
  d_rewriteTable[static_cast<uint32_t>(Kind::CONST_BITVECTOR_SYMBOLIC)] =
      RewriteConstBvSym;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SADDO)] =
      RewriteOverflow;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_UADDO)] =
      RewriteOverflow;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SMULO)] =
      RewriteOverflow;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_UMULO)] =
      RewriteOverflow;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_SSUBO)] =
      RewriteOverflow;
  d_rewriteTable[static_cast<uint32_t>(Kind::BITVECTOR_USUBO)] =
      RewriteOverflow;
}
