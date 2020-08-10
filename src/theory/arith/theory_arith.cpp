/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/infer_bounds.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/ext_theory.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

TheoryArith::TheoryArith(context::Context* c,
                         context::UserContext* u,
                         OutputChannel& out,
                         Valuation valuation,
                         const LogicInfo& logicInfo,
                         ProofNodeManager* pnm)
    : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo, pnm),
      d_internal(
          new TheoryArithPrivate(*this, c, u, out, valuation, logicInfo, pnm)),
      d_ppRewriteTimer("theory::arith::ppRewriteTimer"),
      d_proofRecorder(nullptr)
{
  smtStatisticsRegistry()->registerStat(&d_ppRewriteTimer);
}

TheoryArith::~TheoryArith(){
  smtStatisticsRegistry()->unregisterStat(&d_ppRewriteTimer);
  delete d_internal;
}

TheoryRewriter* TheoryArith::getTheoryRewriter()
{
  return d_internal->getTheoryRewriter();
}

void TheoryArith::preRegisterTerm(TNode n){
  d_internal->preRegisterTerm(n);
}

void TheoryArith::finishInit()
{
  if (getLogicInfo().isTheoryEnabled(THEORY_ARITH)
      && getLogicInfo().areTranscendentalsUsed())
  {
    // witness is used to eliminate square root
    d_valuation.setUnevaluatedKind(kind::WITNESS);
    // we only need to add the operators that are not syntax sugar
    d_valuation.setUnevaluatedKind(kind::EXPONENTIAL);
    d_valuation.setUnevaluatedKind(kind::SINE);
    d_valuation.setUnevaluatedKind(kind::PI);
  }
}

TrustNode TheoryArith::expandDefinition(Node node)
{
  return d_internal->expandDefinition(node);
}

void TheoryArith::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_internal->setMasterEqualityEngine(eq);
}

void TheoryArith::addSharedTerm(TNode n){
  d_internal->addSharedTerm(n);
}

TrustNode TheoryArith::ppRewrite(TNode atom)
{
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
  getOutputChannel().spendResource(ResourceManager::Resource::TheoryCheckStep);
  d_internal->check(effortLevel);
}

bool TheoryArith::needsCheckLastEffort() {
  return d_internal->needsCheckLastEffort();
}

TrustNode TheoryArith::explain(TNode n)
{
  Node exp = d_internal->explain(n);
  return TrustNode::mkTrustPropExp(n, exp, nullptr);
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

std::pair<bool, Node> TheoryArith::entailmentCheck(TNode lit)
{
  ArithEntailmentCheckParameters def;
  def.addLookupRowSumAlgorithms();
  ArithEntailmentCheckSideEffects ase;
  std::pair<bool, Node> res = d_internal->entailmentCheck(lit, def, ase);
  return res;
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
