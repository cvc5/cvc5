/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): kshitij, ajreynol, mdeters, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
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

TheoryArith::TheoryArith(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe)
  : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo, qe)
  , d_internal(new TheoryArithPrivate(*this, c, u, out, valuation, logicInfo, qe))
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

void TheoryArith::addSharedTerm(TNode n){
  d_internal->addSharedTerm(n);
}

Node TheoryArith::ppRewrite(TNode atom) {
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

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
