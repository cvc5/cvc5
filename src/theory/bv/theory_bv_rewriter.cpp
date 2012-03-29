/*********************                                                        */
/*! \file theory_bv_rewriter.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
  Debug("bitvector-rewrite") << "TheoryBV::preRewrite(" << node << ")" << std::endl;
  //return d_rewriteTable[node.getKind()](node);
  return RewriteResponse(REWRITE_DONE, node); 
}

RewriteResponse TheoryBVRewriter::postRewrite(TNode node) {
  //TimerStat::CodeTimer codeTimer(*d_rewriteTimer); 
  Debug("bitvector-rewrite") << "TheoryBV::postRewrite(" << node << ")" << std::endl;
  RewriteResponse res = d_rewriteTable[node.getKind()](node);
  return res; 
}

RewriteResponse TheoryBVRewriter::RewriteUlt(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalUlt>,
      // if both arguments are constants evaluates
      RewriteRule<UltZero>
      // a < 0 rewrites to false
      >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSlt(TNode node){
  return RewriteResponse(REWRITE_DONE, node); 
  // Node resultNode = LinearRewriteStrategy
  //   < RewriteRule < SltEliminate >
  //     // a <_s b ==> a + 2^{n-1} <_u b + 2^{n-1}
  //     >::apply(node);

  // return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUle(TNode node){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalUle>,
      RewriteRule<UleMax>,
      RewriteRule<ZeroUle>,
      RewriteRule<UleZero>,
      RewriteRule<UleSelf>
      >::apply(node);
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSle(TNode node){
  return RewriteResponse(REWRITE_DONE, node); 
  // Node resultNode = LinearRewriteStrategy
  //   < RewriteRule<SleEliminate>
  //     >::apply(node);

  // return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUgt(TNode node){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<UgtEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSgt(TNode node){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SgtEliminate>
      //RewriteRule<SltEliminate>
      >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUge(TNode node){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<UgeEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSge(TNode node){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SgeEliminate>
      //      RewriteRule<SleEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNot(TNode node){
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

RewriteResponse TheoryBVRewriter::RewriteExtract(TNode node) {
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


RewriteResponse TheoryBVRewriter::RewriteConcat(TNode node) {
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

RewriteResponse TheoryBVRewriter::RewriteAnd(TNode node){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalAnd>,
      RewriteRule<BitwiseIdemp>,
      RewriteRule<AndZero>,
      RewriteRule<AndOne> 
      >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteOr(TNode node){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalOr>,
      RewriteRule<BitwiseIdemp>,
      RewriteRule<OrZero>,
      RewriteRule<OrOne>
    >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteXor(TNode node) {
  Node resultNode = node;
  if (RewriteRule<XorOne>::applies(node)) {
    resultNode = RewriteRule<XorOne>::run<false> (node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }
  resultNode = LinearRewriteStrategy
    < RewriteRule<XorNot>, 
      RewriteRule<EvalXor>,
      RewriteRule<XorDuplicate>,
      RewriteRule<XorZero>
    >::apply(node);
 
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteXnor(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<XnorEliminate>
    >::apply(node);
  // need to rewrite two levels in 
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNand(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<NandEliminate>
      >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNor(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<NorEliminate>
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteComp(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<CompEliminate>
      >::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteMult(TNode node) {
  Node resultNode = node; 
  if(RewriteRule<MultPow2>::applies(node)) {
    resultNode = RewriteRule<MultPow2>::run <false> (node);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
  }

  resultNode = LinearRewriteStrategy
    < RewriteRule<EvalMult>,
      RewriteRule<MultOne>,
      RewriteRule<MultZero>
    >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewritePlus(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalPlus>,
      RewriteRule<PlusZero>
      // RewriteRule<PlusSelf>,
      // RewriteRule<PlusNegSelf>
      // RewriteRule<PlusLiftConcat> 
    >::apply(node);

  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSub(TNode node){
  return RewriteResponse(REWRITE_DONE, node); 
  // Node resultNode = LinearRewriteStrategy
  //   < RewriteRule<SubEliminate>
  //   >::apply(node);
  
  // return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteNeg(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<EvalNeg>,
      RewriteRule<NegIdemp>
    >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteUdiv(TNode node){
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

RewriteResponse TheoryBVRewriter::RewriteUrem(TNode node) {
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

RewriteResponse TheoryBVRewriter::RewriteSmod(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SmodEliminate>
      >::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSdiv(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SdivEliminate>
      >::apply(node);

  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSrem(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<SremEliminate>
       >::apply(node);
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteShl(TNode node) {
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

RewriteResponse TheoryBVRewriter::RewriteLshr(TNode node) {
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

RewriteResponse TheoryBVRewriter::RewriteAshr(TNode node) {
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


RewriteResponse TheoryBVRewriter::RewriteRepeat(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RepeatEliminate >
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteZeroExtend(TNode node){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<ZeroExtendEliminate >
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteSignExtend(TNode node) {
  // Node resultNode = LinearRewriteStrategy
  //   < RewriteRule<SignExtendEliminate >
  //   >::apply(node);
  
  // return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  return RewriteResponse(REWRITE_DONE, node); 
}


RewriteResponse TheoryBVRewriter::RewriteRotateRight(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RotateRightEliminate >
    >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteRotateLeft(TNode node){
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<RotateLeftEliminate >
      >::apply(node);
  
  return RewriteResponse(REWRITE_AGAIN_FULL, resultNode); 
}

RewriteResponse TheoryBVRewriter::RewriteEqual(TNode node) {
  Node resultNode = LinearRewriteStrategy
    < RewriteRule<FailEq>,
      RewriteRule<SimplifyEq>,
      RewriteRule<ReflexivityEq>
      >::apply(node);
  
  return RewriteResponse(REWRITE_DONE, resultNode); 
}


RewriteResponse TheoryBVRewriter::IdentityRewrite(TNode node) {
  return RewriteResponse(REWRITE_DONE, node); 
}

RewriteResponse TheoryBVRewriter::UndefinedRewrite(TNode node) {
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
  d_rewriteTable [ kind::BITVECTOR_UDIV ] = RewriteUdiv;
  d_rewriteTable [ kind::BITVECTOR_UREM ] = RewriteUrem;
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




