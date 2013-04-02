/*********************                                                        */
/*! \file theory_bv_rewriter.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Liana Hadarean
 ** Minor contributors (to current version): Tim King, Morgan Deters, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/theory.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_rewrite_rules_core.h"
#include "theory/bv/theory_bv_rewrite_rules_operator_elimination.h"
#include "theory/bv/theory_bv_rewrite_rules_constant_evaluation.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;


// CVC4_THREADLOCAL(AllRewriteRules*) TheoryBVRewriter::s_allRules = NULL;
// CVC4_THREADLOCAL(TimerStat*) TheoryBVRewriter::d_rewriteTimer = NULL;
RewriteFunction TheoryBVRewriter::d_rewriteTable[kind::LAST_KIND]; 
void TheoryBVRewriter::init() {
   // s_allRules = new AllRewriteRules;
   // d_rewriteTimer = new TimerStat("theory::bv::rewriteTimer");
   // StatisticsRegistry::registerStat(d_rewriteTimer); 
   initializeRewrites();

}

void TheoryBVRewriter::shutdown() {
   // delete s_allRules;
   // StatisticsRegistry::unregisterStat(d_rewriteTimer); 
   //delete d_rewriteTimer;
}

RewriteResponse TheoryBVRewriter::preRewrite(TNode node) {
  RewriteResponse res = d_rewriteTable[node.getKind()](node, true);
  if(res.node != node) {
    Debug("bitvector-rewrite") << "TheoryBV::preRewrite    " << node << std::endl;
    Debug("bitvector-rewrite") << "TheoryBV::preRewrite to " << res.node << std::endl;
  }
  return res; 
}

RewriteResponse TheoryBVRewriter::postRewrite(TNode node) {
  RewriteResponse res = d_rewriteTable[node.getKind()](node, false);
  if(res.node!= node) {
    Debug("bitvector-rewrite") << "TheoryBV::postRewrite    " << node << std::endl;
    Debug("bitvector-rewrite") << "TheoryBV::postRewrite to " << res.node << std::endl;
  }
  // if (res.status == REWRITE_DONE) {
  //   Node rewr = res.node;
  //   Node rerewr = d_rewriteTable[rewr.getKind()](rewr, false).node;
  //   Assert(rewr == rerewr);
  // }
  
  return res; 
}

RewriteResponse TheoryBVRewriter::RewriteUlt(TNode node, bool preregister) {
  // reduce common subexpressions on both sides
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalUlt>,
      // if both arguments are constants evaluates
      RewriteRule<UltZero>
      // a < 0 rewrites to false
      >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSlt(TNode node, bool preregister){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule < EvalSlt >
      >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 

  // Node resultNode = LinearRewriteStrategy
  //   < RewriteRule < SltEliminate >
  //     // a <_s b ==> a + 2^{n-1} <_u b + 2^{n-1}
  //     >::apply(node);

  // return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUle(TNode node, bool preregister){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalUle>,
      RewriteRule<UleMax>,
      RewriteRule<ZeroUle>,
      RewriteRule<UleZero>,
      RewriteRule<UleSelf>
      >::apply(node);
  return RewriteResponse(resultNode == node ? REWRITE_DONE : REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSle(TNode node, bool preregister){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule < EvalSle >
      >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUgt(TNode node, bool preregister){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<UgtEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSgt(TNode node, bool preregister){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SgtEliminate>
      //RewriteRule<SltEliminate>
      >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUge(TNode node, bool preregister){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<UgeEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSge(TNode node, bool preregister){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SgeEliminate>
      //      RewriteRule<SleEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNot(TNode node, bool preregister){
  Node resultNode = node;
  
  if(RewriteRule<NotXor>::applies(node)) {
    resultNode = RewriteRule<NotXor>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }
  resultNode = LinearRewriteStrategy
    < RewriteRule<EvalNot>,
      RewriteRule<NotIdemp>
    >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteExtract(TNode node, bool preregister) {
  Node resultNode = node;

  if (RewriteRule<ExtractConcat>::applies(node)) {
    resultNode = RewriteRule<ExtractConcat>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  if (RewriteRule<ExtractBitwise>::applies(node)) {
    resultNode = RewriteRule<ExtractBitwise>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }
  
  if (RewriteRule<ExtractNot>::applies(node)) {
    resultNode = RewriteRule<ExtractNot>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  if (RewriteRule<ExtractArith>::applies(node)) {
    resultNode = RewriteRule<ExtractArith>::run<false>(node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  resultNode = LinearRewriteStrategy
    < RewriteRule<ExtractConstant>, 
      RewriteRule<ExtractExtract>,
      // We could get another extract over extract
      RewriteRule<ExtractWhole>
      // At this point only Extract-Whole could apply
      >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}


RewriteResponse TheoryBVRewriter::RewriteConcat(TNode node, bool preregister) {
  
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<ConcatFlatten>,
      // Flatten the top level concatenations
      RewriteRule<ConcatExtractMerge>,
      // Merge the adjacent extracts on non-constants
      RewriteRule<ConcatConstantMerge>,
      // Merge the adjacent extracts on constants
      ApplyRuleToChildren<kind::BITVECTOR_CONCAT, ExtractWhole>
      >::apply(node);
   return RewriteResponse(REWRITE_DONE, resultNode);  
}

RewriteResponse TheoryBVRewriter::RewriteAnd(TNode node, bool preregister){
  Node resultNode = node;
  
  resultNode = LinearRewriteStrategy
    < RewriteRule<FlattenAssocCommut>,
      RewriteRule<AndSimplify>
      // RewriteRule<EvalAnd>,
      // RewriteRule<BitwiseIdemp>,
      // //RewriteRule<BitwiseSlice>, -> might need rw again
      // RewriteRule<AndZero>,
      // RewriteRule<AndOne> 
      >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteOr(TNode node, bool preregister){
  Node resultNode = node;

  resultNode = LinearRewriteStrategy
    < RewriteRule<FlattenAssocCommut>,
      RewriteRule<OrSimplify>
    >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteXor(TNode node, bool preregister) {
  Node resultNode = node;

  resultNode = LinearRewriteStrategy
    < RewriteRule<FlattenAssocCommut>, // flatten the expression 
      RewriteRule<XorSimplify>,        // simplify duplicates and constants
      RewriteRule<XorZero>             // checks if the constant part is zero and eliminates it
    >::apply(node);

  // this simplification introduces new terms and might require further
  // rewriting
  if (RewriteRule<XorOne>::applies(resultNode)) {
    resultNode = RewriteRule<XorOne>::run<false> (resultNode);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteXnor(TNode node, bool preregister) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<XnorEliminate>
    >::apply(node);
  // need to rewrite two levels in 
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNand(TNode node, bool preregister) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<NandEliminate>
      >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNor(TNode node, bool preregister) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<NorEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteComp(TNode node, bool preregister) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<CompEliminate>
      >::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteMult(TNode node, bool preregister) {
  Node resultNode = node; 

  resultNode = LinearRewriteStrategy
    < RewriteRule<FlattenAssocCommut>, // flattens and sorts
      RewriteRule<MultSimplify>        // multiplies constant part and checks for 0
    >::apply(node);

  // only apply if every subterm was already rewritten 
  if (!preregister) {
    // distributes multiplication by constant over +, - and unary -
    if(RewriteRule<MultDistribConst>::applies(resultNode)) {
      resultNode = RewriteRule<MultDistribConst>::run<false>(resultNode);
      // creating new terms that might simplify further
      return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
    }
  }

  if(resultNode == node) {
    return RewriteResponse(REWRITE_DONE, resultNode); 
  }
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewritePlus(TNode node, bool preregister) {
  if (preregister) {
    return RewriteResponse(REWRITE_DONE, node);
  }
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<FlattenAssocCommut>, 
      RewriteRule<PlusCombineLikeTerms>
      // RewriteRule<PlusLiftConcat> 
      >::apply(node);
  if (resultNode == node) {
    return RewriteResponse(REWRITE_DONE, resultNode);
  } else {
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }
}

RewriteResponse TheoryBVRewriter::RewriteSub(TNode node, bool preregister){
  // return RewriteResponse(REWRITE_DONE, node); 
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SubEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNeg(TNode node, bool preregister) {
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
  
  if(!preregister) {
    if (RewriteRule<NegMult>::applies(node)) {
      resultNode = RewriteRule<NegMult>::run<false>(node);
      return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
    }
  }

  return RewriteResponse(REWRITE_DONE, resultNode); 
}


RewriteResponse TheoryBVRewriter::RewriteUdivTotal(TNode node, bool preregister){
  Node resultNode = node;

  if(RewriteRule<UdivPow2>::applies(node)) {
    resultNode = RewriteRule<UdivPow2>::run <false> (node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  resultNode = LinearRewriteStrategy
    < RewriteRule<EvalUdiv>,
      RewriteRule<UdivOne>,
      RewriteRule<UdivSelf>
      >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUremTotal(TNode node, bool preregister) {
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

RewriteResponse TheoryBVRewriter::RewriteSmod(TNode node, bool preregister) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SmodEliminate>
      >::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSdiv(TNode node, bool preregister) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SdivEliminate>
      >::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSrem(TNode node, bool preregister) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SremEliminate>
       >::apply(node);
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteShl(TNode node, bool preregister) {
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

RewriteResponse TheoryBVRewriter::RewriteLshr(TNode node, bool preregister) {
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

RewriteResponse TheoryBVRewriter::RewriteAshr(TNode node, bool preregister) {
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


RewriteResponse TheoryBVRewriter::RewriteRepeat(TNode node, bool preregister) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RepeatEliminate >
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteZeroExtend(TNode node, bool preregister){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<ZeroExtendEliminate >
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSignExtend(TNode node, bool preregister) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalSignExtend>
    >::apply(node);
  
  // return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  return RewriteResponse(REWRITE_DONE, resultNode); 
}


RewriteResponse TheoryBVRewriter::RewriteRotateRight(TNode node, bool preregister) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RotateRightEliminate >
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteRotateLeft(TNode node, bool preregister){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RotateLeftEliminate >
      >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteEqual(TNode node, bool preregister) {
  if (preregister) {
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
  // d_rewriteTable [ kind::BITVECTOR_UDIV ] = RewriteUdiv;
  // d_rewriteTable [ kind::BITVECTOR_UREM ] = RewriteUrem;
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
}

Node TheoryBVRewriter::eliminateBVSDiv(TNode node) {
  Node result = bv::LinearRewriteStrategy <
    bv::RewriteRule<bv::SremEliminate>,
    bv::RewriteRule<bv::SdivEliminate>,
    bv::RewriteRule<bv::SmodEliminate>
    >::apply(node);
  return result; 
}



