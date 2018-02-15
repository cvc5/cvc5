/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/theory_arith.h"

#include "options/smt_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/infer_bounds.h"
#include "theory/arith/theory_arith_private.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

TheoryArith::TheoryArith(context::Context* c, context::UserContext* u,
                         OutputChannel& out, Valuation valuation,
                         const LogicInfo& logicInfo)
    : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo)
    , d_internal(new TheoryArithPrivate(*this, c, u, out, valuation, logicInfo))
    , d_ppRewriteTimer("theory::arith::ppRewriteTimer")
{
  smtStatisticsRegistry()->registerStat(&d_ppRewriteTimer);
  if (options::nlExt()) {
    setupExtTheory();
    getExtTheory()->addFunctionKind(kind::NONLINEAR_MULT);
    getExtTheory()->addFunctionKind(kind::EXPONENTIAL);
    getExtTheory()->addFunctionKind(kind::SINE);
    getExtTheory()->addFunctionKind(kind::PI);
  }
}

TheoryArith::~TheoryArith(){
  smtStatisticsRegistry()->unregisterStat(&d_ppRewriteTimer);
  delete d_internal;
}

void TheoryArith::preRegisterTerm(TNode n){
  d_internal->preRegisterTerm(n);
}

Node TheoryArith::expandDefinition(LogicRequest &logicRequest, Node node) {
  return d_internal->expandDefinition(logicRequest, node);
}

void TheoryArith::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_internal->setMasterEqualityEngine(eq);
}

void TheoryArith::addSharedTerm(TNode n){
  d_internal->addSharedTerm(n);
}

Node TheoryArith::ppRewrite(TNode atom) {
  CodeTimer timer(d_ppRewriteTimer, /* allow_reentrant = */ true);
  return d_internal->ppRewrite(atom);
}

Theory::PPAssertStatus TheoryArith::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  return d_internal->ppAssert(in, outSubstitutions);
}

void TheoryArith::ppStaticLearn(TNode n, NodeBuilder<>& learned) {
  d_internal->ppStaticLearn(n, learned);
}

void TheoryArith::check(Effort effortLevel){
  getOutputChannel().spendResource(options::theoryCheckStep());
  d_internal->check(effortLevel);
}

bool TheoryArith::needsCheckLastEffort() {
  return d_internal->needsCheckLastEffort();
}

Node TheoryArith::explain(TNode n) {
  return d_internal->explain(n);
}

bool TheoryArith::getCurrentSubstitution( int effort, std::vector< Node >& vars, std::vector< Node >& subs, std::map< Node, std::vector< Node > >& exp ) {
  return d_internal->getCurrentSubstitution( effort, vars, subs, exp );
}

bool TheoryArith::isExtfReduced( int effort, Node n, Node on, std::vector< Node >& exp ) {
  return d_internal->isExtfReduced( effort, n, on, exp );
}

void TheoryArith::propagate(Effort e) {
  d_internal->propagate(e);
}
bool TheoryArith::collectModelInfo(TheoryModel* m)
{
  return d_internal->collectModelInfo(m);
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


std::pair<bool, Node> TheoryArith::entailmentCheck (TNode lit,
                                                    const EntailmentCheckParameters* params,
                                                    EntailmentCheckSideEffects* out)
{
  const ArithEntailmentCheckParameters* aparams = NULL;
  if(params == NULL){
    ArithEntailmentCheckParameters* def = new ArithEntailmentCheckParameters();
    def->addLookupRowSumAlgorithms();
    aparams = def;
  }else{
    AlwaysAssert(params->getTheoryId() == getId());
    aparams = dynamic_cast<const ArithEntailmentCheckParameters*>(params);
  }
  Assert(aparams != NULL);

  ArithEntailmentCheckSideEffects* ase = NULL;
  if(out == NULL){
    ase = new ArithEntailmentCheckSideEffects();
  }else{
    AlwaysAssert(out->getTheoryId() == getId());
    ase = dynamic_cast<ArithEntailmentCheckSideEffects*>(out);
  }
  Assert(ase != NULL);

  std::pair<bool, Node> res = d_internal->entailmentCheck(lit, *aparams, *ase);

  if(params == NULL){
    delete aparams;
  }
  if(out == NULL){
    delete ase;
  }

  return res;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
