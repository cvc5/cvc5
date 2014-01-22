/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Andrew Reynolds, Tianyi Liang, Dejan Jovanovic
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

#include "theory/arith/theory_arith.h"
#include "theory/arith/theory_arith_private.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

TheoryArith::TheoryArith(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo)
  : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo)
  , d_internal(new TheoryArithPrivate(*this, c, u, out, valuation, logicInfo))
{}

TheoryArith::~TheoryArith(){
  delete d_internal;
}

void TheoryArith::preRegisterTerm(TNode n){
  d_internal->preRegisterTerm(n);
}

void TheoryArith::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_internal->setMasterEqualityEngine(eq);
}

void TheoryArith::setQuantifiersEngine(QuantifiersEngine* qe) {
  this->Theory::setQuantifiersEngine(qe);
  d_internal->setQuantifiersEngine(qe);
}

void TheoryArith::addSharedTerm(TNode n){
  d_internal->addSharedTerm(n);
}

Node TheoryArith::ppRewrite(TNode atom) {
  CodeTimer timer(d_ppRewriteTimer);
  return d_internal->ppRewrite(atom);
}

Theory::PPAssertStatus TheoryArith::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  return d_internal->ppAssert(in, outSubstitutions);
}

void TheoryArith::ppStaticLearn(TNode n, NodeBuilder<>& learned) {
  d_internal->ppStaticLearn(n, learned);
}

void TheoryArith::check(Effort effortLevel){
  d_internal->check(effortLevel);
}

Node TheoryArith::explain(TNode n) {
  return d_internal->explain(n);
}

void TheoryArith::propagate(Effort e) {
  d_internal->propagate(e);
}

void TheoryArith::collectModelInfo( TheoryModel* m, bool fullModel ){
  d_internal->collectModelInfo(m, fullModel);
}

void TheoryArith::notifyRestart(){
  d_internal->notifyRestart();
}

void TheoryArith::presolve(){
  d_internal->presolve();
}

EqualityStatus TheoryArith::getEqualityStatus(TNode a, TNode b) {
  return d_internal->getEqualityStatus(a,b);
}

Node TheoryArith::getModelValue(TNode var) {
  return d_internal->getModelValue( var );
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
