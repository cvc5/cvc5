/*********************                                                        */
/*! \file theory_bv_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "options/bv_options.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_rewrite_rules_constant_evaluation.h"
#include "theory/bv/theory_bv_rewrite_rules_core.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_rewrite_rules_operator_elimination.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/theory.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

TheoryBVRewriter::TheoryBVRewriter() { initializeRewrites(); }

RewriteResponse TheoryBVRewriter::preRewrite(TNode node) {
  RewriteResponse res = d_rewriteTable[node.getKind()](node, true);
  if (res.d_node != node)
  {
    Debug("bitvector-rewrite") << "TheoryBV::preRewrite    " << node << std::endl;
    Debug("bitvector-rewrite")
        << "TheoryBV::preRewrite to " << res.d_node << std::endl;
  }
  return res; 
}

RewriteResponse TheoryBVRewriter::postRewrite(TNode node) {
  RewriteResponse res = d_rewriteTable[node.getKind()](node, false);
  if (res.d_node != node)
  {
    Debug("bitvector-rewrite") << "TheoryBV::postRewrite    " << node << std::endl;
    Debug("bitvector-rewrite")
        << "TheoryBV::postRewrite to " << res.d_node << std::endl;
  }
  return res; 
}

RewriteResponse TheoryBVRewriter::RewriteBitOf(TNode node, bool prerewrite)
{
  Node resultNode = LinearRewriteStrategy<RewriteRule<BitOfConst>>::apply(node);
  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteUlt(TNode node, bool prerewrite) {
  // reduce common subexpressions on both sides
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalUlt>, // if both arguments are constants evaluates
      RewriteRule<UltZero>, // a < 0 rewrites to false,
      RewriteRule<SignExtendUltConst>,
      RewriteRule<ZeroExtendUltConst>
       >::apply(node);

  return RewriteResponse(resultNode == node ? REWRITE_DONE : REWRITE_AGAIN_FULL,
                         resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteUltBv(TNode node, bool prerewrite) {
  // reduce common subexpressions on both sides
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalUltBv>
       >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}


RewriteResponse TheoryBVRewriter::RewriteSlt(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalSlt>,
      RewriteRule<MultSltMult>
       >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 

  // Node resultNode = LinearRewriteStrategy
  //   < RewriteRule < SltEliminate >
  //     // a <_s b ==> a + 2^{n-1} <_u b + 2^{n-1}
  //     >::apply(node);

  // return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSltBv(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule < EvalSltBv >
       >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUle(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalUle>,
      RewriteRule<UleMax>,
      RewriteRule<ZeroUle>,
      RewriteRule<UleZero>,
      RewriteRule<UleSelf>,
      RewriteRule<UleEliminate>
      >::apply(node);
  return RewriteResponse(resultNode == node ? REWRITE_DONE : REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSle(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule <EvalSle>, 
      RewriteRule <SleEliminate>
      >::apply(node);
  return RewriteResponse(resultNode == node? REWRITE_DONE : REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUgt(TNode node, bool prerewrite){
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<UgtUrem>,
                            RewriteRule<UgtEliminate>>::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSgt(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SgtEliminate>
      //RewriteRule<SltEliminate>
      >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUge(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<UgeEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSge(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SgeEliminate>
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

RewriteResponse TheoryBVRewriter::RewriteNot(TNode node, bool prerewrite){
  Node resultNode = node;
  
  // // if(RewriteRule<NotXor>::applies(node)) {
  // //   resultNode = RewriteRule<NotXor>::run<false>(node);
  // //   return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  // // }
  resultNode = LinearRewriteStrategy
    < RewriteRule<EvalNot>,
      RewriteRule<NotIdemp>
    >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteExtract(TNode node, bool prerewrite) {
  Node resultNode = node;

  if (RewriteRule<ExtractConcat>::applies(node)) {
    resultNode = RewriteRule<ExtractConcat>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  if (RewriteRule<ExtractSignExtend>::applies(node)) {
    resultNode = RewriteRule<ExtractSignExtend>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  if (RewriteRule<ExtractNot>::applies(node)) {
    resultNode = RewriteRule<ExtractNot>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  if (options::bvExtractArithRewrite()) {
    if (RewriteRule<ExtractArith>::applies(node)) {
      resultNode = RewriteRule<ExtractArith>::run<false>(node);
      return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
    }
  }

  
  resultNode = LinearRewriteStrategy
    < RewriteRule<ExtractConstant>, 
      RewriteRule<ExtractExtract>,
      // We could get another extract over extract
      RewriteRule<ExtractWhole>,
      // At this point only Extract-Whole could apply
      RewriteRule<ExtractMultLeadingBit>
      >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteConcat(TNode node, bool prerewrite)
{
  Node resultNode = LinearRewriteStrategy<
      RewriteRule<ConcatFlatten>,
      // Flatten the top level concatenations
      RewriteRule<ConcatExtractMerge>,
      // Merge the adjacent extracts on non-constants
      RewriteRule<ConcatConstantMerge>,
      // Merge the adjacent extracts on constants
      ApplyRuleToChildren<kind::BITVECTOR_CONCAT, ExtractWhole>>::apply(node);
  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteAnd(TNode node, bool prerewrite)
{
  Node resultNode = node;
  resultNode =
      LinearRewriteStrategy<RewriteRule<FlattenAssocCommutNoDuplicates>,
                            RewriteRule<AndSimplify>,
                            RewriteRule<AndOrXorConcatPullUp>>::apply(node);
  if (!prerewrite)
  {
    resultNode =
        LinearRewriteStrategy<RewriteRule<BitwiseSlicing>>::apply(resultNode);

    if (resultNode.getKind() != node.getKind())
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
    }
  }

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteOr(TNode node, bool prerewrite)
{
  Node resultNode = node;
  resultNode =
      LinearRewriteStrategy<RewriteRule<FlattenAssocCommutNoDuplicates>,
                            RewriteRule<OrSimplify>,
                            RewriteRule<AndOrXorConcatPullUp>>::apply(node);

  if (!prerewrite)
  {
    resultNode =
        LinearRewriteStrategy<RewriteRule<BitwiseSlicing>>::apply(resultNode);

    if (resultNode.getKind() != node.getKind())
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
    }
  }

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteXor(TNode node, bool prerewrite)
{
  Node resultNode = node;
  resultNode = LinearRewriteStrategy<
      RewriteRule<FlattenAssocCommut>,  // flatten the expression
      RewriteRule<XorSimplify>,         // simplify duplicates and constants
      RewriteRule<XorZero>,  // checks if the constant part is zero and
                             // eliminates it
      RewriteRule<AndOrXorConcatPullUp>,
      RewriteRule<BitwiseSlicing>>::apply(node);

  if (!prerewrite)
  {
    resultNode =
        LinearRewriteStrategy<RewriteRule<XorOne>,
                              RewriteRule<BitwiseSlicing>>::apply(resultNode);

    if (resultNode.getKind() != node.getKind())
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
    }
  }

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteXnor(TNode node, bool prerewrite) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<XnorEliminate>
    >::apply(node);
  // need to rewrite two levels in 
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNand(TNode node, bool prerewrite) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<NandEliminate>
      >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNor(TNode node, bool prerewrite) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<NorEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteComp(TNode node, bool prerewrite)
{
  Node resultNode =
      LinearRewriteStrategy<RewriteRule<EvalComp>, RewriteRule<BvComp> >::apply(
          node);

  return RewriteResponse(REWRITE_DONE, resultNode);
}

RewriteResponse TheoryBVRewriter::RewriteMult(TNode node, bool prerewrite) {
  Node resultNode = node; 
  resultNode = LinearRewriteStrategy
    < RewriteRule<FlattenAssocCommut>, // flattens and sorts
      RewriteRule<MultSimplify>,       // multiplies constant part and checks for 0
      RewriteRule<MultPow2>            // replaces multiplication by a power of 2 by a shift
    >::apply(resultNode);

  // only apply if every subterm was already rewritten 
  if (!prerewrite) {
    resultNode = LinearRewriteStrategy
      <   RewriteRule<MultDistribConst>
        , RewriteRule<MultDistrib>
        >::apply(resultNode);
  }

  if(resultNode == node) {
    return RewriteResponse(REWRITE_DONE, resultNode); 
  }
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewritePlus(TNode node, bool prerewrite) {
  Node resultNode = node;
  if (prerewrite) {
    resultNode = LinearRewriteStrategy
      < RewriteRule<FlattenAssocCommut>
        >::apply(node);
    return RewriteResponse(REWRITE_DONE, resultNode);
  }
  
  resultNode =  LinearRewriteStrategy
    < RewriteRule<FlattenAssocCommut>,
      RewriteRule<PlusCombineLikeTerms>
      >::apply(node);

  if (node != resultNode) {
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSub(TNode node, bool prerewrite){
  // return RewriteResponse(REWRITE_DONE, node); 
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SubEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNeg(TNode node, bool prerewrite) {
  Node resultNode = node; 
  
  resultNode = LinearRewriteStrategy
    < RewriteRule<EvalNeg>,
      RewriteRule<NegIdemp>,
      RewriteRule<NegSub>
      >::apply(node);
  
  if (RewriteRule<NegPlus>::applies(node)) {
    resultNode = RewriteRule<NegPlus>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }
  
  if(!prerewrite) {
    if (RewriteRule<NegMult>::applies(node)) {
      resultNode = RewriteRule<NegMult>::run<false>(node);
      return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
    }
  }

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUdiv(TNode node, bool prerewrite){
  Node resultNode = node;

  if(node[1].isConst() && node[1].getConst<BitVector>().getValue() != 0) {
    return RewriteUdivTotal(node, prerewrite);
  }

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUrem(TNode node, bool prerewrite){
  Node resultNode = node;

  if(node[1].isConst() && node[1].getConst<BitVector>().getValue() != 0) {
    return RewriteUremTotal(node, prerewrite);
  }

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUdivTotal(TNode node, bool prerewrite){
  Node resultNode = node;

  if(RewriteRule<UdivPow2>::applies(node)) {
    resultNode = RewriteRule<UdivPow2>::run <false> (node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  resultNode =
      LinearRewriteStrategy<RewriteRule<EvalUdiv>, RewriteRule<UdivZero>,
                            RewriteRule<UdivOne> >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUremTotal(TNode node, bool prerewrite) {
  Node resultNode = node;

  if(RewriteRule<UremPow2>::applies(node)) {
    resultNode = RewriteRule<UremPow2>::run <false> (node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  resultNode = LinearRewriteStrategy
    < RewriteRule<EvalUrem>,
      RewriteRule<UremOne>,
      RewriteRule<UremSelf>
      >::apply(node);
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSmod(TNode node, bool prerewrite) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SmodEliminate>
      >::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSdiv(TNode node, bool prerewrite) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SdivEliminate>
      >::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSrem(TNode node, bool prerewrite) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SremEliminate>
       >::apply(node);
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteShl(TNode node, bool prerewrite) {
  Node resultNode = node; 
  if(RewriteRule<ShlByConst>::applies(node)) {
    resultNode = RewriteRule<ShlByConst>::run <false> (node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  resultNode = LinearRewriteStrategy
    < RewriteRule<EvalShl>,
      RewriteRule<ShiftZero> 
      >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteLshr(TNode node, bool prerewrite) {
  Node resultNode = node; 
  if(RewriteRule<LshrByConst>::applies(node)) {
    resultNode = RewriteRule<LshrByConst>::run <false> (node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  resultNode = LinearRewriteStrategy
    < RewriteRule<EvalLshr>,
      RewriteRule<ShiftZero> 
      >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteAshr(TNode node, bool prerewrite) {
  Node resultNode = node; 
  if(RewriteRule<AshrByConst>::applies(node)) {
    resultNode = RewriteRule<AshrByConst>::run <false> (node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  resultNode = LinearRewriteStrategy
    < RewriteRule<EvalAshr>,
      RewriteRule<ShiftZero>
        >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}


RewriteResponse TheoryBVRewriter::RewriteRepeat(TNode node, bool prerewrite) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RepeatEliminate >
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteZeroExtend(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<ZeroExtendEliminate >
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSignExtend(TNode node, bool prerewrite) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<MergeSignExtend>
    , RewriteRule<EvalSignExtend>
    >::apply(node);

  
  if (resultNode != node) {
    return RewriteResponse(REWRITE_AGAIN, resultNode);
  }
  return RewriteResponse(REWRITE_DONE, resultNode); 
}


RewriteResponse TheoryBVRewriter::RewriteRotateRight(TNode node, bool prerewrite) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RotateRightEliminate >
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteRotateLeft(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RotateLeftEliminate >
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteRedor(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RedorEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteRedand(TNode node, bool prerewrite){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RedandEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteBVToNat(TNode node, bool prerewrite) {
  //do not use lazy rewrite strategy if equality solver is disabled
  if( node[0].isConst() || !options::bvLazyRewriteExtf() ){
    Node resultNode = LinearRewriteStrategy
      < RewriteRule<BVToNatEliminate>
      >::apply(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }else{
    return RewriteResponse(REWRITE_DONE, node); 
  }
}

RewriteResponse TheoryBVRewriter::RewriteIntToBV(TNode node, bool prerewrite) {
  //do not use lazy rewrite strategy if equality solver is disabled
  if( node[0].isConst() || !options::bvLazyRewriteExtf() ){
    Node resultNode = LinearRewriteStrategy
      < RewriteRule<IntToBVEliminate>
      >::apply(node);

    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }else{
    return RewriteResponse(REWRITE_DONE, node); 
  }
}

RewriteResponse TheoryBVRewriter::RewriteEqual(TNode node, bool prerewrite) {
  if (prerewrite) {
    Node resultNode = LinearRewriteStrategy
      < RewriteRule<FailEq>,
        RewriteRule<SimplifyEq>,
        RewriteRule<ReflexivityEq>
        >::apply(node);
    return RewriteResponse(REWRITE_DONE, resultNode); 
  }
  else {
    Node resultNode = LinearRewriteStrategy
      < RewriteRule<FailEq>,
        RewriteRule<SimplifyEq>,
        RewriteRule<ReflexivityEq>
        >::apply(node);

    if(RewriteRule<SolveEq>::applies(resultNode)) {
      resultNode = RewriteRule<SolveEq>::run<false>(resultNode);
      if (resultNode != node) {
        return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
      }
    }
    return RewriteResponse(REWRITE_DONE, resultNode); 
  }
}


RewriteResponse TheoryBVRewriter::IdentityRewrite(TNode node, bool prerewrite) {
  return RewriteResponse(REWRITE_DONE, node); 
}

RewriteResponse TheoryBVRewriter::UndefinedRewrite(TNode node, bool prerewrite) {
  Debug("bv-rewrite") << "TheoryBV::UndefinedRewrite for" << node;
  Unimplemented(); 
} 



void TheoryBVRewriter::initializeRewrites() {

  for(unsigned i = 0; i < kind::LAST_KIND; ++i) {
    d_rewriteTable[i] = IdentityRewrite; //UndefinedRewrite;
  }

  d_rewriteTable [ kind::EQUAL ] = RewriteEqual;
  d_rewriteTable[kind::BITVECTOR_BITOF] = RewriteBitOf;
  d_rewriteTable [ kind::BITVECTOR_ULT ] = RewriteUlt;
  d_rewriteTable [ kind::BITVECTOR_SLT ] = RewriteSlt;
  d_rewriteTable [ kind::BITVECTOR_ULE ] = RewriteUle;
  d_rewriteTable [ kind::BITVECTOR_SLE ] = RewriteSle;
  d_rewriteTable [ kind::BITVECTOR_UGT ] = RewriteUgt;
  d_rewriteTable [ kind::BITVECTOR_SGT ] = RewriteSgt;
  d_rewriteTable [ kind::BITVECTOR_UGE ] = RewriteUge;
  d_rewriteTable [ kind::BITVECTOR_SGE ] = RewriteSge;
  d_rewriteTable [ kind::BITVECTOR_NOT ] = RewriteNot;
  d_rewriteTable [ kind::BITVECTOR_CONCAT ] = RewriteConcat;
  d_rewriteTable [ kind::BITVECTOR_AND ] = RewriteAnd;
  d_rewriteTable [ kind::BITVECTOR_OR ] = RewriteOr;
  d_rewriteTable [ kind::BITVECTOR_XOR] = RewriteXor;
  d_rewriteTable [ kind::BITVECTOR_XNOR ] = RewriteXnor;
  d_rewriteTable [ kind::BITVECTOR_NAND ] = RewriteNand;
  d_rewriteTable [ kind::BITVECTOR_NOR ] = RewriteNor;
  d_rewriteTable [ kind::BITVECTOR_COMP ] = RewriteComp;
  d_rewriteTable [ kind::BITVECTOR_MULT ] = RewriteMult;
  d_rewriteTable [ kind::BITVECTOR_PLUS ] = RewritePlus;
  d_rewriteTable [ kind::BITVECTOR_SUB ] = RewriteSub;
  d_rewriteTable [ kind::BITVECTOR_NEG ] = RewriteNeg;
  d_rewriteTable [ kind::BITVECTOR_UDIV ] = RewriteUdiv;
  d_rewriteTable [ kind::BITVECTOR_UREM ] = RewriteUrem;
  d_rewriteTable [ kind::BITVECTOR_UDIV_TOTAL ] = RewriteUdivTotal;
  d_rewriteTable [ kind::BITVECTOR_UREM_TOTAL ] = RewriteUremTotal;
  d_rewriteTable [ kind::BITVECTOR_SMOD ] = RewriteSmod;
  d_rewriteTable [ kind::BITVECTOR_SDIV ] = RewriteSdiv;
  d_rewriteTable [ kind::BITVECTOR_SREM ] = RewriteSrem;
  d_rewriteTable [ kind::BITVECTOR_SHL ] = RewriteShl;
  d_rewriteTable [ kind::BITVECTOR_LSHR ] = RewriteLshr;
  d_rewriteTable [ kind::BITVECTOR_ASHR ] = RewriteAshr;
  d_rewriteTable [ kind::BITVECTOR_EXTRACT ] = RewriteExtract;
  d_rewriteTable [ kind::BITVECTOR_REPEAT ] = RewriteRepeat;
  d_rewriteTable [ kind::BITVECTOR_ZERO_EXTEND ] = RewriteZeroExtend;
  d_rewriteTable [ kind::BITVECTOR_SIGN_EXTEND ] = RewriteSignExtend;
  d_rewriteTable [ kind::BITVECTOR_ROTATE_RIGHT ] = RewriteRotateRight;
  d_rewriteTable [ kind::BITVECTOR_ROTATE_LEFT ] = RewriteRotateLeft;
  d_rewriteTable [ kind::BITVECTOR_REDOR ] = RewriteRedor;
  d_rewriteTable [ kind::BITVECTOR_REDAND ] = RewriteRedand;
  d_rewriteTable [ kind::BITVECTOR_ULTBV ] = RewriteUltBv;
  d_rewriteTable [ kind::BITVECTOR_SLTBV ] = RewriteSltBv;
  d_rewriteTable [ kind::BITVECTOR_ITE ] = RewriteITEBv;

  d_rewriteTable [ kind::BITVECTOR_TO_NAT ] = RewriteBVToNat;
  d_rewriteTable [ kind::INT_TO_BITVECTOR ] = RewriteIntToBV;
}

Node TheoryBVRewriter::eliminateBVSDiv(TNode node) {
  Node result = bv::LinearRewriteStrategy <
    bv::RewriteRule<bv::SremEliminate>,
    bv::RewriteRule<bv::SdivEliminate>,
    bv::RewriteRule<bv::SmodEliminate>
    >::apply(node);
  return result; 
}
