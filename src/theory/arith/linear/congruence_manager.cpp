/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Tim King, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Congruence manager, the interface to the equality engine from the
 * linear arithmetic solver
 */

#include "theory/arith/linear/congruence_manager.h"

#include "base/output.h"
#include "options/arith_options.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/linear/constraint.h"
#include "theory/arith/linear/partial_model.h"
#include "theory/ee_setup_info.h"
#include "theory/rewriter.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/proof_equality_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

std::vector<Node> andComponents(TNode an)
{
  auto nm = NodeManager::currentNM();
  if (an == nm->mkConst(true))
  {
    return {};
  }
  else if (an.getKind() != AND)
  {
    return {an};
  }
  std::vector<Node> a{};
  a.reserve(an.getNumChildren());
  a.insert(a.end(), an.begin(), an.end());
  return a;
}

ArithCongruenceManager::ArithCongruenceManager(
    Env& env,
    ConstraintDatabase& cd,
    SetupLiteralCallBack setup,
    const ArithVariables& avars,
    RaiseEqualityEngineConflict raiseConflict)
    : EnvObj(env),
      d_inConflict(context()),
      d_raiseConflict(raiseConflict),
      d_keepAlive(context()),
      d_propagatations(context()),
      d_explanationMap(context()),
      d_constraintDatabase(cd),
      d_setupLiteral(setup),
      d_avariables(avars),
      d_ee(nullptr),
      d_pnm(d_env.isTheoryProofProducing() ? d_env.getProofNodeManager()
                                           : nullptr),
      // Construct d_pfGenEe with the SAT context, since its proof include
      // unclosed assumptions of theory literals.
      d_pfGenEe(new EagerProofGenerator(
          d_env, context(), "ArithCongruenceManager::pfGenEe")),
      // Construct d_pfGenEe with the USER context, since its proofs are closed.
      d_pfGenExplain(new EagerProofGenerator(
          d_env, userContext(), "ArithCongruenceManager::pfGenExplain")),
      d_pfee(nullptr),
      d_statistics(statisticsRegistry())
{
}

ArithCongruenceManager::~ArithCongruenceManager() {}

void ArithCongruenceManager::finishInit(eq::EqualityEngine* ee)
{
  Assert(ee != nullptr);
  // otherwise, we use the official one
  d_ee = ee;
  // the congruence kinds are already set up
  // the proof equality engine is the one from the equality engine
  d_pfee = d_ee->getProofEqualityEngine();
  // have proof equality engine only if proofs are enabled
  Assert(isProofEnabled() == (d_pfee != nullptr));
}

ArithCongruenceManager::Statistics::Statistics(StatisticsRegistry& sr)
    : d_watchedVariables(
        sr.registerInt("theory::arith::congruence::watchedVariables")),
      d_watchedVariableIsZero(
          sr.registerInt("theory::arith::congruence::watchedVariableIsZero")),
      d_watchedVariableIsNotZero(sr.registerInt(
          "theory::arith::congruence::watchedVariableIsNotZero")),
      d_equalsConstantCalls(
          sr.registerInt("theory::arith::congruence::equalsConstantCalls")),
      d_propagations(sr.registerInt("theory::arith::congruence::propagations")),
      d_propagateConstraints(
          sr.registerInt("theory::arith::congruence::propagateConstraints")),
      d_conflicts(sr.registerInt("theory::arith::congruence::conflicts"))
{
}

void ArithCongruenceManager::raiseConflict(Node conflict,
                                           std::shared_ptr<ProofNode> pf)
{
  Assert(!inConflict());
  Trace("arith::conflict") << "difference manager conflict   " << conflict << std::endl;
  d_inConflict.raise();
  d_raiseConflict.raiseEEConflict(conflict, pf);
}
bool ArithCongruenceManager::inConflict() const{
  return d_inConflict.isRaised();
}

bool ArithCongruenceManager::hasMorePropagations() const {
  return !d_propagatations.empty();
}
const Node ArithCongruenceManager::getNextPropagation() {
  Assert(hasMorePropagations());
  Node prop = d_propagatations.front();
  d_propagatations.dequeue();
  return prop;
}

bool ArithCongruenceManager::canExplain(TNode n) const {
  return d_explanationMap.find(n) != d_explanationMap.end();
}

Node ArithCongruenceManager::externalToInternal(TNode n) const{
  Assert(canExplain(n));
  ExplainMap::const_iterator iter = d_explanationMap.find(n);
  size_t pos = (*iter).second;
  return d_propagatations[pos];
}

void ArithCongruenceManager::pushBack(TNode n){
  d_explanationMap.insert(n, d_propagatations.size());
  d_propagatations.enqueue(n);

  ++(d_statistics.d_propagations);
}
void ArithCongruenceManager::pushBack(TNode n, TNode r){
  d_explanationMap.insert(r, d_propagatations.size());
  d_explanationMap.insert(n, d_propagatations.size());
  d_propagatations.enqueue(n);

  ++(d_statistics.d_propagations);
}
void ArithCongruenceManager::pushBack(TNode n, TNode r, TNode w){
  d_explanationMap.insert(w, d_propagatations.size());
  d_explanationMap.insert(r, d_propagatations.size());
  d_explanationMap.insert(n, d_propagatations.size());
  d_propagatations.enqueue(n);

  ++(d_statistics.d_propagations);
}

void ArithCongruenceManager::watchedVariableIsZero(ConstraintCP lb, ConstraintCP ub){
  Assert(lb->isLowerBound());
  Assert(ub->isUpperBound());
  Assert(lb->getVariable() == ub->getVariable());
  Assert(lb->getValue().sgn() == 0);
  Assert(ub->getValue().sgn() == 0);

  ++(d_statistics.d_watchedVariableIsZero);

  ArithVar s = lb->getVariable();
  TNode eq = d_watchedEqualities[s];
  ConstraintCP eqC = d_constraintDatabase.getConstraint(
      s, ConstraintType::Equality, lb->getValue());
  NodeBuilder reasonBuilder(Kind::AND);
  auto pfLb = lb->externalExplainByAssertions(reasonBuilder);
  auto pfUb = ub->externalExplainByAssertions(reasonBuilder);
  Node reason = mkAndFromBuilder(reasonBuilder);
  std::shared_ptr<ProofNode> pf{};
  if (isProofEnabled())
  {
    pf = d_pnm->mkNode(
        PfRule::ARITH_TRICHOTOMY, {pfLb, pfUb}, {eqC->getProofLiteral()});
    pf = d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM, {pf}, {eq});
  }

  d_keepAlive.push_back(reason);
  Trace("arith-ee") << "Asserting an equality on " << s << ", on trichotomy"
                    << std::endl;
  Trace("arith-ee") << "  based on " << lb << std::endl;
  Trace("arith-ee") << "  based on " << ub << std::endl;
  assertionToEqualityEngine(true, s, reason, pf);
}

void ArithCongruenceManager::watchedVariableIsZero(ConstraintCP eq){
  Trace("arith::cong") << "Cong::watchedVariableIsZero: " << *eq << std::endl;

  Assert(eq->isEquality());
  Assert(eq->getValue().sgn() == 0);

  ++(d_statistics.d_watchedVariableIsZero);

  ArithVar s = eq->getVariable();

  //Explain for conflict is correct as these proofs are generated
  //and stored eagerly
  //These will be safe for propagation later as well
  NodeBuilder nb(Kind::AND);
  // An open proof of eq from literals now in reason.
  if (TraceIsOn("arith::cong"))
  {
    eq->printProofTree(Trace("arith::cong"));
  }
  auto pf = eq->externalExplainByAssertions(nb);
  if (isProofEnabled())
  {
    pf = d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM, {pf}, {d_watchedEqualities[s]});
  }
  Node reason = mkAndFromBuilder(nb);

  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(true, s, reason, pf);
}

void ArithCongruenceManager::watchedVariableCannotBeZero(ConstraintCP c){
  Trace("arith::cong::notzero")
      << "Cong::watchedVariableCannotBeZero " << *c << std::endl;
  ++(d_statistics.d_watchedVariableIsNotZero);

  ArithVar s = c->getVariable();
  Node disEq = d_watchedEqualities[s].negate();

  //Explain for conflict is correct as these proofs are generated and stored eagerly
  //These will be safe for propagation later as well
  NodeBuilder nb(Kind::AND);
  // An open proof of eq from literals now in reason.
  auto pf = c->externalExplainByAssertions(nb);
  if (TraceIsOn("arith::cong::notzero"))
  {
    Trace("arith::cong::notzero") << "  original proof ";
    pf->printDebug(Trace("arith::cong::notzero"));
    Trace("arith::cong::notzero") << std::endl;
  }
  Node reason = mkAndFromBuilder(nb);
  if (isProofEnabled())
  {
    if (c->getType() == ConstraintType::Disequality)
    {
      Assert(c->getLiteral() == d_watchedEqualities[s].negate());
      // We have to prove equivalence to the watched disequality.
      pf = d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM, {pf}, {disEq});
    }
    else
    {
      Trace("arith::cong::notzero")
          << "  proof modification needed" << std::endl;

      // Four cases:
      //   c has form x_i = d, d > 0     => multiply c by -1 in Farkas proof
      //   c has form x_i = d, d > 0     => multiply c by 1 in Farkas proof
      //   c has form x_i <= d, d < 0     => multiply c by 1 in Farkas proof
      //   c has form x_i >= d, d > 0     => multiply c by -1 in Farkas proof
      const bool scaleCNegatively = c->getType() == ConstraintType::LowerBound
                                    || (c->getType() == ConstraintType::Equality
                                        && c->getValue().sgn() > 0);
      const int cSign = scaleCNegatively ? -1 : 1;
      TNode isZero = d_watchedEqualities[s];
      TypeNode type = isZero[0].getType();
      const auto isZeroPf = d_pnm->mkAssume(isZero);
      const auto nm = NodeManager::currentNM();
      const auto sumPf =
          d_pnm->mkNode(PfRule::MACRO_ARITH_SCALE_SUM_UB,
                        {isZeroPf, pf},
                        // Trick for getting correct, opposing signs.
                        {nm->mkConstRealOrInt(type, Rational(-1 * cSign)),
                         nm->mkConstRealOrInt(type, Rational(cSign))});
      const auto botPf = d_pnm->mkNode(
          PfRule::MACRO_SR_PRED_TRANSFORM, {sumPf}, {nm->mkConst(false)});
      std::vector<Node> assumption = {isZero};
      pf = d_pnm->mkScope(botPf, assumption, false);
      Trace("arith::cong::notzero") << "  new proof ";
      pf->printDebug(Trace("arith::cong::notzero"));
      Trace("arith::cong::notzero") << std::endl;
    }
    Assert(pf->getResult() == disEq);
  }
  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(false, s, reason, pf);
}


bool ArithCongruenceManager::propagate(TNode x){
  Trace("arith::congruenceManager")<< "ArithCongruenceManager::propagate("<<x<<")"<<std::endl;
  if(inConflict()){
    return true;
  }

  Node rewritten = rewrite(x);

  //Need to still propagate this!
  if(rewritten.getKind() == kind::CONST_BOOLEAN){
    pushBack(x);

    if(rewritten.getConst<bool>()){
      return true;
    }else{
      // x rewrites to false.
      ++(d_statistics.d_conflicts);
      TrustNode trn = explainInternal(x);
      Node conf = flattenAnd(trn.getNode());
      Trace("arith::congruenceManager") << "rewritten to false "<<x<<" with explanation "<< conf << std::endl;
      if (isProofEnabled())
      {
        auto pf = trn.getGenerator()->getProofFor(trn.getProven());
        auto confPf = d_pnm->mkNode(
            PfRule::MACRO_SR_PRED_TRANSFORM, {pf}, {conf.negate()});
        raiseConflict(conf, confPf);
      }
      else
      {
        raiseConflict(conf);
      }
      return false;
    }
  }

  Assert(rewritten.getKind() != kind::CONST_BOOLEAN);

  ConstraintP c = d_constraintDatabase.lookup(rewritten);
  if(c == NullConstraint){
    //using setup as there may not be a corresponding congruence literal yet
    d_setupLiteral(rewritten);
    c = d_constraintDatabase.lookup(rewritten);
    Assert(c != NullConstraint);
  }

  Trace("arith::congruenceManager")<< "x is "
                                   <<  c->hasProof() << " "
                                   << (x == rewritten) << " "
                                   << c->canBePropagated() << " "
                                   << c->negationHasProof() << std::endl;

  if(c->negationHasProof()){
    TrustNode texpC = explainInternal(x);
    Node expC = texpC.getNode();
    ConstraintCP negC = c->getNegation();
    Node neg = Constraint::externalExplainByAssertions({negC});
    Node conf = expC.andNode(neg);
    Node final = flattenAnd(conf);

    ++(d_statistics.d_conflicts);
    raiseConflict(final);
    Trace("arith::congruenceManager") << "congruenceManager found a conflict " << final << std::endl;
    return false;
  }

  // Cases for propagation
  // C : c has a proof
  // S : x == rewritten
  // P : c can be propagated
  //
  // CSP
  // 000 : propagate x, and mark C it as being explained
  // 001 : propagate x, and propagate c after marking it as being explained
  // 01* : propagate x, mark c but do not propagate c
  // 10* : propagate x, do not mark c and do not propagate c
  // 11* : drop the constraint, do not propagate x or c

  if(!c->hasProof() && x != rewritten){
    if(c->assertedToTheTheory()){
      pushBack(x, rewritten, c->getWitness());
    }else{
      pushBack(x, rewritten);
    }

    c->setEqualityEngineProof();
    if(c->canBePropagated() && !c->assertedToTheTheory()){

      ++(d_statistics.d_propagateConstraints);
      c->propagate();
    }
  }else if(!c->hasProof() && x == rewritten){
    if(c->assertedToTheTheory()){
      pushBack(x, c->getWitness());
    }else{
      pushBack(x);
    }
    c->setEqualityEngineProof();
  }else if(c->hasProof() && x != rewritten){
    if(c->assertedToTheTheory()){
      pushBack(x);
    }else{
      pushBack(x);
    }
  }else{
    Assert(c->hasProof() && x == rewritten);
  }
  return true;
}

TrustNode ArithCongruenceManager::explainInternal(TNode internal)
{
  if (isProofEnabled())
  {
    return d_pfee->explain(internal);
  }
  // otherwise, explain without proof generator
  Node exp = d_ee->mkExplainLit(internal);
  return TrustNode::mkTrustPropExp(internal, exp, nullptr);
}

TrustNode ArithCongruenceManager::explain(TNode external)
{
  Trace("arith-ee") << "Ask for explanation of " << external << std::endl;
  Node internal = externalToInternal(external);
  Trace("arith-ee") << "...internal = " << internal << std::endl;
  TrustNode trn = explainInternal(internal);
  if (isProofEnabled() && trn.getProven()[1] != external)
  {
    Assert(trn.getKind() == TrustNodeKind::PROP_EXP);
    Assert(trn.getProven().getKind() == Kind::IMPLIES);
    Assert(trn.getGenerator() != nullptr);
    Trace("arith-ee") << "tweaking proof to prove " << external << " not "
                      << trn.getProven()[1] << std::endl;
    std::vector<std::shared_ptr<ProofNode>> assumptionPfs;
    std::vector<Node> assumptions = andComponents(trn.getNode());
    assumptionPfs.push_back(trn.toProofNode());
    for (const auto& a : assumptions)
    {
      assumptionPfs.push_back(
          d_pnm->mkNode(PfRule::TRUE_INTRO, {d_pnm->mkAssume(a)}, {}));
    }
    auto litPf = d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM, {assumptionPfs}, {external});
    auto extPf = d_pnm->mkScope(litPf, assumptions);
    return d_pfGenExplain->mkTrustedPropagation(external, trn.getNode(), extPf);
  }
  return trn;
}

void ArithCongruenceManager::addWatchedPair(ArithVar s, TNode x, TNode y){
  Assert(!isWatchedVariable(s));

  Trace("arith::congruenceManager")
    << "addWatchedPair(" << s << ", " << x << ", " << y << ")" << std::endl;


  ++(d_statistics.d_watchedVariables);

  d_watchedVariables.add(s);
  // must ensure types are correct, thus, add TO_REAL if necessary here
  std::pair<Node, Node> p = mkSameType(x, y);
  Node eq = p.first.eqNode(p.second);
  d_watchedEqualities.set(s, eq);
}

void ArithCongruenceManager::assertLitToEqualityEngine(
    Node lit, TNode reason, std::shared_ptr<ProofNode> pf)
{
  bool isEquality = lit.getKind() != Kind::NOT;
  Node eq = isEquality ? lit : lit[0];
  Assert(eq.getKind() == Kind::EQUAL);

  Trace("arith-ee") << "Assert to Eq " << lit << ", reason " << reason
                    << std::endl;
  if (isProofEnabled())
  {
    if (CDProof::isSame(lit, reason))
    {
      Trace("arith-pfee") << "Asserting only, b/c implied by symm" << std::endl;
      // The equality engine doesn't ref-count for us...
      d_keepAlive.push_back(eq);
      d_keepAlive.push_back(reason);
      d_ee->assertEquality(eq, isEquality, reason);
    }
    else if (hasProofFor(lit))
    {
      Trace("arith-pfee") << "Skipping b/c already done" << std::endl;
    }
    else
    {
      setProofFor(lit, pf);
      Trace("arith-pfee") << "Actually asserting" << std::endl;
      if (TraceIsOn("arith-pfee"))
      {
        Trace("arith-pfee") << "Proof: ";
        pf->printDebug(Trace("arith-pfee"));
        Trace("arith-pfee") << std::endl;
      }
      // The proof equality engine *does* ref-count for us...
      d_pfee->assertFact(lit, reason, d_pfGenEe.get());
    }
  }
  else
  {
    // The equality engine doesn't ref-count for us...
    d_keepAlive.push_back(eq);
    d_keepAlive.push_back(reason);
    d_ee->assertEquality(eq, isEquality, reason);
  }
}

void ArithCongruenceManager::assertionToEqualityEngine(
    bool isEquality, ArithVar s, TNode reason, std::shared_ptr<ProofNode> pf)
{
  Assert(isWatchedVariable(s));

  TNode eq = d_watchedEqualities[s];
  Assert(eq.getKind() == kind::EQUAL);

  Node lit = isEquality ? Node(eq) : eq.notNode();
  Trace("arith-ee") << "Assert to Eq " << eq << ", pol " << isEquality
                    << ", reason " << reason << std::endl;
  assertLitToEqualityEngine(lit, reason, pf);
}

bool ArithCongruenceManager::hasProofFor(TNode f) const
{
  Assert(isProofEnabled());
  if (d_pfGenEe->hasProofFor(f))
  {
    return true;
  }
  Node sym = CDProof::getSymmFact(f);
  Assert(!sym.isNull());
  return d_pfGenEe->hasProofFor(sym);
}

void ArithCongruenceManager::setProofFor(TNode f,
                                         std::shared_ptr<ProofNode> pf) const
{
  Assert(!hasProofFor(f));
  d_pfGenEe->mkTrustNode(f, pf);
  Node symF = CDProof::getSymmFact(f);
  auto symPf = d_pnm->mkNode(PfRule::SYMM, {pf}, {});
  d_pfGenEe->mkTrustNode(symF, symPf);
}

void ArithCongruenceManager::equalsConstant(ConstraintCP c){
  Assert(c->isEquality());

  ++(d_statistics.d_equalsConstantCalls);
  Trace("equalsConstant") << "equals constant " << c << std::endl;

  ArithVar x = c->getVariable();
  Node xAsNode = d_avariables.asNode(x);
  NodeManager* nm = NodeManager::currentNM();
  Node asRational = nm->mkConstRealOrInt(
      xAsNode.getType(), c->getValue().getNoninfinitesimalPart());

  // No guarentee this is in normal form!
  // Note though, that it happens to be in proof normal form!
  Node eq = xAsNode.eqNode(asRational);
  d_keepAlive.push_back(eq);

  NodeBuilder nb(Kind::AND);
  auto pf = c->externalExplainByAssertions(nb);
  Node reason = mkAndFromBuilder(nb);
  d_keepAlive.push_back(reason);

  Trace("arith-ee") << "Assert equalsConstant " << eq << ", reason " << reason << std::endl;
  assertLitToEqualityEngine(eq, reason, pf);
}

void ArithCongruenceManager::equalsConstant(ConstraintCP lb, ConstraintCP ub){
  Assert(lb->isLowerBound());
  Assert(ub->isUpperBound());
  Assert(lb->getVariable() == ub->getVariable());

  ++(d_statistics.d_equalsConstantCalls);
  Trace("equalsConstant") << "equals constant " << lb << std::endl
                          << ub << std::endl;

  ArithVar x = lb->getVariable();
  NodeBuilder nb(Kind::AND);
  auto pfLb = lb->externalExplainByAssertions(nb);
  auto pfUb = ub->externalExplainByAssertions(nb);
  Node reason = mkAndFromBuilder(nb);

  Node xAsNode = d_avariables.asNode(x);
  NodeManager* nm = NodeManager::currentNM();
  Node asRational = nm->mkConstRealOrInt(
      xAsNode.getType(), lb->getValue().getNoninfinitesimalPart());

  // No guarentee this is in normal form!
  // Note though, that it happens to be in proof normal form!
  Node eq = xAsNode.eqNode(asRational);
  std::shared_ptr<ProofNode> pf;
  if (isProofEnabled())
  {
    pf = d_pnm->mkNode(PfRule::ARITH_TRICHOTOMY, {pfLb, pfUb}, {eq});
  }
  d_keepAlive.push_back(eq);
  d_keepAlive.push_back(reason);

  Trace("arith-ee") << "Assert equalsConstant2 " << eq << ", reason " << reason << std::endl;

  assertLitToEqualityEngine(eq, reason, pf);
}

bool ArithCongruenceManager::isProofEnabled() const { return d_pnm != nullptr; }

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
