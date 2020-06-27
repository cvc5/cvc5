/*********************                                                        */
/*! \file prop_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the propositional engine of CVC4
 **
 ** Implementation of the propositional engine of CVC4.
 **/

#include "prop/prop_engine.h"

#include <iomanip>
#include <map>
#include <utility>

#include "base/check.h"
#include "base/output.h"
#include "decision/decision_engine.h"
#include "expr/expr.h"
#include "options/base_options.h"
#include "options/decision_options.h"
#include "options/main_options.h"
#include "options/options.h"
#include "options/smt_options.h"
#include "proof/proof_manager.h"
#include "prop/cnf_stream.h"
#include "prop/minisat/minisat.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "prop/theory_proxy.h"
#include "smt/command.h"
#include "smt/smt_statistics_registry.h"
#include "theory/theory_engine.h"
#include "theory/theory_registrar.h"
#include "util/resource_manager.h"
#include "util/result.h"

using namespace std;
using namespace CVC4::context;

namespace CVC4 {
namespace prop {

/** Keeps a boolean flag scoped */
class ScopedBool {

private:

  bool d_original;
  bool& d_reference;

public:

  ScopedBool(bool& reference) :
    d_reference(reference) {
    d_original = reference;
  }

  ~ScopedBool() {
    d_reference = d_original;
  }
};

PropEngine::PropEngine(TheoryEngine* te,
                       Context* satContext,
                       UserContext* userContext,
                       ResourceManager* rm)
    : d_inCheckSat(false),
      d_theoryEngine(te),
      d_context(satContext),
      d_theoryProxy(NULL),
      d_satSolver(NULL),
      d_registrar(NULL),
      d_cnfStream(NULL),
      d_pNodeManager(options::proofNew()
                         ? new ProofNodeManager(te->getProofChecker())
                         : nullptr),
      d_proof(d_pNodeManager.get(), nullptr, userContext),
      d_pfCnfStream(nullptr),
      d_interrupted(false),
      d_resourceManager(rm)
{

  Debug("prop") << "Constructing the PropEngine" << endl;

  d_decisionEngine.reset(new DecisionEngine(satContext, userContext, rm));
  d_decisionEngine->init();  // enable appropriate strategies

  d_satSolver = SatSolverFactory::createDPLLMinisat(smtStatisticsRegistry());

  d_registrar = new theory::TheoryRegistrar(d_theoryEngine);
  d_cnfStream =
      new TseitinCnfStream(d_satSolver, d_registrar, userContext, rm, true);
  if (options::proofNew())
  {
    d_conflictLit = undefSatVariable;
    d_pfCnfStream.reset(new ProofCnfStream(
        userContext, *d_cnfStream, d_pNodeManager.get(), options::proofNew()));
  }

  d_theoryProxy = new TheoryProxy(
      this, d_theoryEngine, d_decisionEngine.get(), d_context, d_cnfStream);
  d_satSolver->initialize(d_context, d_theoryProxy);

  d_decisionEngine->setSatSolver(d_satSolver);
  d_decisionEngine->setCnfStream(d_cnfStream);
  PROOF (
         ProofManager::currentPM()->initCnfProof(d_cnfStream, userContext);
         );

  NodeManager* nm = NodeManager::currentNM();
  if (d_pfCnfStream)
  {
    d_pfCnfStream->convertAndAssert(nm->mkConst(true), false, false);
    d_pfCnfStream->convertAndAssert(nm->mkConst(false).notNode(), false, false);
  }
  else
  {
    d_cnfStream->convertAndAssert(nm->mkConst(true), false, false, RULE_GIVEN);
    d_cnfStream->convertAndAssert(
        nm->mkConst(false).notNode(), false, false, RULE_GIVEN);
  }
}

PropEngine::~PropEngine() {
  Debug("prop") << "Destructing the PropEngine" << endl;
  d_decisionEngine->shutdown();
  d_decisionEngine.reset(nullptr);
  delete d_cnfStream;
  delete d_registrar;
  delete d_satSolver;
  delete d_theoryProxy;
}

void PropEngine::assertFormula(TNode node) {
  Assert(!d_inCheckSat) << "Sat solver in solve()!";
  Debug("prop") << "assertFormula(" << node << ")" << endl;
  // Assert as non-removable
  if (d_pfCnfStream)
  {
    d_pfCnfStream->convertAndAssert(node, false, false);
  }
  else
  {
    d_cnfStream->convertAndAssert(node, false, false, RULE_GIVEN);
  }
}

void PropEngine::assertLemma(theory::TrustNode trn,
                             bool removable,
                             ProofRule rule,
                             TNode from)
{
  Node node = trn.getNode();
  bool negated = trn.getKind() == theory::TrustNodeKind::CONFLICT;
  Debug("prop::lemmas") << "assertLemma(" << node << ")" << endl;
  // Assert as (possibly) removable
  if (d_pfCnfStream)
  {
    Assert(trn.getGenerator());
    d_proof.addLazyStep(node, trn.getGenerator());
    d_pfCnfStream->convertAndAssert(node, negated, removable);
  }
  else
  {
    d_cnfStream->convertAndAssert(node, removable, negated, rule, from);
  }
}

void PropEngine::addAssertionsToDecisionEngine(
    const preprocessing::AssertionPipeline& assertions)
{
  d_decisionEngine->addAssertions(assertions);
}

void PropEngine::requirePhase(TNode n, bool phase) {
  Debug("prop") << "requirePhase(" << n << ", " << phase << ")" << endl;

  Assert(n.getType().isBoolean());
  SatLiteral lit = d_cnfStream->getLiteral(n);
  d_satSolver->requirePhase(phase ? lit : ~lit);
}

bool PropEngine::isDecision(Node lit) const {
  Assert(isSatLiteral(lit));
  return d_satSolver->isDecision(d_cnfStream->getLiteral(lit).getSatVariable());
}

void PropEngine::printSatisfyingAssignment(){
  const CnfStream::NodeToLiteralMap& transCache =
    d_cnfStream->getTranslationCache();
  Debug("prop-value") << "Literal | Value | Expr" << endl
                      << "----------------------------------------"
                      << "-----------------" << endl;
  for(CnfStream::NodeToLiteralMap::const_iterator i = transCache.begin(),
      end = transCache.end();
      i != end;
      ++i) {
    pair<Node, SatLiteral> curr = *i;
    SatLiteral l = curr.second;
    if(!l.isNegated()) {
      Node n = curr.first;
      SatValue value = d_satSolver->modelValue(l);
      Debug("prop-value") << "'" << l << "' " << value << " " << n << endl;
    }
  }
}

Result PropEngine::checkSat() {
  Assert(!d_inCheckSat) << "Sat solver in solve()!";
  Debug("prop") << "PropEngine::checkSat()" << endl;

  // Mark that we are in the checkSat
  ScopedBool scopedBool(d_inCheckSat);
  d_inCheckSat = true;

  // TODO This currently ignores conflicts (a dangerous practice).
  d_theoryEngine->presolve();

  if(options::preprocessOnly()) {
    return Result(Result::SAT_UNKNOWN, Result::REQUIRES_FULL_CHECK);
  }

  // Reset the interrupted flag
  d_interrupted = false;

  // Check the problem
  SatValue result = d_satSolver->solve();

  if( result == SAT_VALUE_UNKNOWN ) {

    Result::UnknownExplanation why = Result::INTERRUPTED;
    if (d_resourceManager->outOfTime())
      why = Result::TIMEOUT;
    if (d_resourceManager->outOfResources())
      why = Result::RESOURCEOUT;

    return Result(Result::SAT_UNKNOWN, why);
  }

  if( result == SAT_VALUE_TRUE && Debug.isOn("prop") ) {
    printSatisfyingAssignment();
  }

  Debug("prop") << "PropEngine::checkSat() => " << result << endl;
  if(result == SAT_VALUE_TRUE && d_theoryEngine->isIncomplete()) {
    return Result(Result::SAT_UNKNOWN, Result::INCOMPLETE);
  }
  return Result(result == SAT_VALUE_TRUE ? Result::SAT : Result::UNSAT);
}

Node PropEngine::getValue(TNode node) const
{
  Assert(node.getType().isBoolean());
  Assert(d_cnfStream->hasLiteral(node));

  SatLiteral lit = d_cnfStream->getLiteral(node);

  SatValue v = d_satSolver->value(lit);
  if (v == SAT_VALUE_TRUE)
  {
    return NodeManager::currentNM()->mkConst(true);
  }
  else if (v == SAT_VALUE_FALSE)
  {
    return NodeManager::currentNM()->mkConst(false);
  }
  else
  {
    Assert(v == SAT_VALUE_UNKNOWN);
    return Node::null();
  }
}

bool PropEngine::isSatLiteral(TNode node) const
{
  return d_cnfStream->hasLiteral(node);
}

bool PropEngine::hasValue(TNode node, bool& value) const
{
  Assert(node.getType().isBoolean());
  Assert(d_cnfStream->hasLiteral(node));

  SatLiteral lit = d_cnfStream->getLiteral(node);

  SatValue v = d_satSolver->value(lit);
  if (v == SAT_VALUE_TRUE)
  {
    value = true;
    return true;
  }
  else if (v == SAT_VALUE_FALSE)
  {
    value = false;
    return true;
  }
  else
  {
    Assert(v == SAT_VALUE_UNKNOWN);
    return false;
  }
}

void PropEngine::getBooleanVariables(std::vector<TNode>& outputVariables) const
{
  d_cnfStream->getBooleanVariables(outputVariables);
}

void PropEngine::ensureLiteral(TNode n)
{
  if (d_pfCnfStream)
  {
    d_pfCnfStream->ensureLiteral(n);
  }
  else
  {
    d_cnfStream->ensureLiteral(n);
  }
}

void PropEngine::push()
{
  Assert(!d_inCheckSat) << "Sat solver in solve()!";
  d_satSolver->push();
  Debug("prop") << "push()" << endl;
}

void PropEngine::pop()
{
  Assert(!d_inCheckSat) << "Sat solver in solve()!";
  d_satSolver->pop();
  Debug("prop") << "pop()" << endl;
}

void PropEngine::resetTrail()
{
  d_satSolver->resetTrail();
  Debug("prop") << "resetTrail()" << endl;
}

unsigned PropEngine::getAssertionLevel() const
{
  return d_satSolver->getAssertionLevel();
}

bool PropEngine::isRunning() const { return d_inCheckSat; }
void PropEngine::interrupt()
{
  if (!d_inCheckSat)
  {
    return;
  }

  d_interrupted = true;
  d_satSolver->interrupt();
  Debug("prop") << "interrupt()" << endl;
}

void PropEngine::spendResource(ResourceManager::Resource r)
{
  d_resourceManager->spendResource(r);
}

bool PropEngine::properExplanation(TNode node, TNode expl) const
{
  if (!d_cnfStream->hasLiteral(node))
  {
    Trace("properExplanation")
        << "properExplanation(): Failing because node "
                               << "being explained doesn't have a SAT literal ?!" << std::endl
                               << "properExplanation(): The node is: " << node << std::endl;
    return false;
  }

  SatLiteral nodeLit = d_cnfStream->getLiteral(node);

  for(TNode::kinded_iterator i = expl.begin(kind::AND),
        i_end = expl.end(kind::AND);
      i != i_end;
       ++i)
  {
    if (!d_cnfStream->hasLiteral(*i))
    {
      Trace("properExplanation")
          << "properExplanation(): Failing because one of explanation "
                                 << "nodes doesn't have a SAT literal" << std::endl
          << "properExplanation(): The explanation node is: " << *i
          << std::endl;
      return false;
    }

    SatLiteral iLit = d_cnfStream->getLiteral(*i);

    if (iLit == nodeLit)
    {
      Trace("properExplanation")
          << "properExplanation(): Failing because the node" << std::endl
                                 << "properExplanation(): " << node << std::endl
          << "properExplanation(): cannot be made to explain itself!"
          << std::endl;
      return false;
    }

    if (!d_satSolver->properExplanation(nodeLit, iLit))
    {
      Trace("properExplanation")
          << "properExplanation(): SAT solver told us that node" << std::endl
                                 << "properExplanation(): " << *i << std::endl
          << "properExplanation(): is not part of a proper explanation node for"
          << std::endl
                                 << "properExplanation(): " << node << std::endl
          << "properExplanation(): Perhaps it one of the two isn't assigned or "
             "the explanation"
          << std::endl
          << "properExplanation(): node wasn't propagated before the node "
             "being explained"
          << std::endl;
      return false;
    }
  }

  return true;
}

void PropEngine::printClause(const Minisat::Solver::TClause& clause)
{
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    SatLiteral satLit = MinisatSatSolver::toSatLiteral(clause[i]);
    Trace("sat-proof") << satLit << " ";
  }
}

Node PropEngine::getClauseNode(SatLiteral satLit)
{
  Assert(d_cnfStream->d_literalToNodeMap.find(satLit)
         != d_cnfStream->d_literalToNodeMap.end())
      << "PropEngine::getClauseNode: literal " << satLit << " undefined.\n";
  return d_cnfStream->d_literalToNodeMap[satLit];
}

Node PropEngine::getClauseNode(const Minisat::Solver::TClause& clause)
{
  std::vector<Node> clauseNodes;
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    SatLiteral satLit = MinisatSatSolver::toSatLiteral(clause[i]);
    Assert(d_cnfStream->d_literalToNodeMap.find(satLit)
           != d_cnfStream->d_literalToNodeMap.end())
        << "PropEngine::getClauseNode: literal " << satLit << " undefined\n";
    clauseNodes.push_back(d_cnfStream->d_literalToNodeMap[satLit]);
  }
  return NodeManager::currentNM()->mkNode(kind::OR, clauseNodes);
}

Node PropEngine::factorAndReorder(Node n)
{
  Trace("sat-proof-norm") << "PropEngine::factorAndReorder: normalize node: "
                          << n << "\n";
  if (n.getKind() != kind::OR)
  {
    Trace("sat-proof-norm") << "PropEngine::factorAndReorder: nothing to do\n";
    return n;
  }
  NodeManager* nm = NodeManager::currentNM();
  // remove duplicates while keeping the order of children
  std::unordered_set<TNode, TNodeHashFunction> clauseSet;
  std::vector<Node> children;
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
    Node factored = children.empty()
                        ? nm->mkConst<bool>(false)
                        : children.size() == 1 ? children[0]
                                               : nm->mkNode(kind::OR, children);
    // don't overwrite what already has a proof step to avoid cycles
    d_proof.addStep(
        factored, PfRule::FACTORING, {n}, {}, false, CDPOverwrite::NEVER);
    n = factored;
  }
  Trace("sat-proof-norm") << "PropEngine::factorAndReorder: factored node: "
                          << n << ", factored children " << children << "\n";
  // nothing to order
  if (children.size() < 2)
  {
    return n;
  }
  // order
  std::sort(children.begin(), children.end());
  Trace("sat-proof-norm") << "PropEngine::factorAndReorder: sorted children: "
                          << children << "\n";
  Node ordered = nm->mkNode(kind::OR, children);
  // if ordering changed
  if (ordered != n)
  {
    // don't overwrite what already has a proof step to avoid cycles
    d_proof.addStep(ordered,
                    PfRule::REORDERING,
                    {n},
                    {ordered},
                    false,
                    CDPOverwrite::NEVER);
  }
  Trace("sat-proof-norm") << "PropEngine::factorAndReorder: orderd node: "
                          << ordered << "\n";
  return ordered;
}

void PropEngine::registerClause(Minisat::Solver::TLit lit)
{
  registerClause(MinisatSatSolver::toSatLiteral(lit));
}

void PropEngine::registerClause(SatLiteral satLit)
{
  Node clauseNode = getClauseNode(satLit);
  if (d_clauseSet.count(clauseNode))
  {
    Trace("sat-proof") << "PropEngine::registerClause: Lit: " << satLit
                       << " already registered\n";
    return;
  }
  d_clauseSet.insert(clauseNode);
  // register in proof as assumption, which should be filled later, since it's
  // not possible yet to know, in general, how this literal came to be. Some
  // components register facts eagerly, like the theory engine, but other
  // lazily, like CNF stream and internal SAT solver propagation.

  // TODO this should be a lazy step with a generator that will query the proof
  // cnf stream
  d_proof.addStep(clauseNode, PfRule::ASSUME, {}, {clauseNode});
  Trace("sat-proof") << "PropEngine::registerClause: Lit: " << satLit << "\n";
}

void PropEngine::registerClause(Minisat::Solver::TClause& clause)
{
  Node clauseNode = getClauseNode(clause);
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "PropEngine::registerClause: TClause: ";
    printClause(clause);
    Trace("sat-proof") << "\n";
  }
  if (d_clauseSet.count(clauseNode))
  {
    Trace("sat-proof")
        << "PropEngine::registerClause: clause already registered\n";
    return;
  }
  d_clauseSet.insert(clauseNode);
  // Rewrite clauseNode before proceeding. This is so ordering is consistent
  clauseNode = factorAndReorder(clauseNode);
  d_clauseSet.insert(clauseNode);
  // register in proof as assumption, which should be filled later, since it's
  // not possible yet to know, in general, how this clause came to be. Some
  // components register facts eagerly, like the theory engine, but other
  // lazily, like CNF stream and internal SAT solver propagation.

  // TODO this should be a lazy step with a generator that will query the proof
  // cnf stream
  d_proof.addStep(clauseNode, PfRule::ASSUME, {}, {clauseNode});
  Trace("sat-proof") << "PropEngine::registerClause: registered clauseNode: "
                     << clauseNode << "\n";
}

void PropEngine::explainPropagation(theory::TrustNode trn)
{
  Node proven = trn.getProven();
  Trace("sat-proof") << "PropEngine::explainPropagation: proven explanation"
                     << proven << "\n";
  Assert(trn.getGenerator());
  d_proof.addLazyStep(proven, trn.getGenerator());
  // since the propagation is added directly to the SAT solver via theoryProxy,
  // do the transformation of the lemma E1 ^ ... ^ En => P into CNF here
  NodeManager* nm = NodeManager::currentNM();
  Node clauseImpliesElim = nm->mkNode(kind::OR, proven[0].notNode(), proven[1]);
  Trace("sat-proof") << "PropEngine::explainPropagation: adding "
                     << PfRule::IMPLIES_ELIM << " rule to conclude "
                     << clauseImpliesElim << "\n";
  d_proof.addStep(clauseImpliesElim, PfRule::IMPLIES_ELIM, {proven}, {});
  // need to eliminate AND
  if (proven[0].getKind() == kind::AND)
  {
    std::vector<Node> disjunctsAndNeg{proven[0]};
    std::vector<Node> disjunctsRes;
    for (unsigned i = 0, size = proven[0].getNumChildren(); i < size; ++i)
    {
      disjunctsAndNeg.push_back(proven[0][i].notNode());
      disjunctsRes.push_back(proven[0][i].notNode());
    }
    disjunctsRes.push_back(proven[1]);
    Node clauseAndNeg = nm->mkNode(kind::OR, disjunctsAndNeg);
    // add proof steps to convert into clause
    d_proof.addStep(clauseAndNeg, PfRule::CNF_AND_NEG, {}, {proven[0]});
    Node clauseRes = nm->mkNode(kind::OR, disjunctsRes);
    d_proof.addStep(clauseRes,
                PfRule::RESOLUTION,
                {clauseAndNeg, clauseImpliesElim},
                {proven[0]});
    // Rewrite clauseNode before proceeding. This is so ordering/factoring
    // is consistent with the clause that is added to the SAT solver
    Node clauseExplanation = factorAndReorder(clauseRes);
    Trace("sat-proof") << "PropEngine::explainPropagation: processed first "
                          "disjunct to conclude "
                       << clauseExplanation << "\n";
  }
}

void PropEngine::startResChain(Minisat::Solver::TClause& start)
{
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "PropEngine::startResChain: ";
    printClause(start);
    Trace("sat-proof") << "\n";
  }
  d_resolution.push_back(
      std::pair<Node, Node>(getClauseNode(start), Node::null()));
}

void PropEngine::addResolutionStep(Minisat::Solver::TLit lit)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(lit);
  Trace("sat-proof") << "PropEngine::addResolutionStep: [" << satLit << "] "
                     << ~satLit << "\n";
  Trace("sat-proof") << CVC4::push
                     << "PropEngine::addResolutionStep: justify lit " << satLit
                     << "\n";
  tryJustifyingLit(~satLit);
  Trace("sat-proof") << CVC4::pop;
  d_resolution.push_back(
      std::pair<Node, Node>(d_cnfStream->d_literalToNodeMap[~satLit],
                            d_cnfStream->d_literalToNodeMap[satLit]));
}

void PropEngine::addResolutionStep(Minisat::Solver::TClause& clause,
                                   Minisat::Solver::TLit lit)
{
  // pivot is given as in the second clause, so we store its negation (which
  // will be removed positivly from the first clause and negatively from the
  // second)
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(~lit);
  Node clauseNode = getClauseNode(clause);
  // clause has not been registered yet
  if (d_clauseSet.count(clauseNode))
  {
    Trace("sat-proof") << CVC4::push;
    registerClause(clause);
    Trace("sat-proof") << CVC4::pop;
  }
  d_resolution.push_back(std::pair<Node, Node>(
      clauseNode, d_cnfStream->d_literalToNodeMap[satLit]));
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "PropEngine::addResolutionStep: [" << satLit << "] ";
    printClause(clause);
    Trace("sat-proof") << "\nPropEngine::addResolutionStep:\t" << clauseNode
                       << "\n";
  }
}

void PropEngine::endResChain(Minisat::Solver::TLit lit)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(lit);
  Trace("sat-proof") << "PropEngine::endResChain: chain_res for " << satLit;
  endResChain(getClauseNode(satLit));
}

void PropEngine::endResChain(Minisat::Solver::TClause& clause)
{
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "PropEngine::endResChain: chain_res for ";
    printClause(clause);
  }
  endResChain(getClauseNode(clause));
}

// id is the conclusion
void PropEngine::endResChain(Node conclusion)
{
  Trace("sat-proof") << ", " << conclusion << "\n";
  std::vector<Node> children, args;
  for (unsigned i = 0, size = d_resolution.size(); i < size; ++i)
  {
    children.push_back(d_resolution[i].first);
    Trace("sat-proof") << "PropEngine::endResChain:   ";
    if (i > 0)
    {
      Trace("sat-proof")
          << "[" << d_cnfStream->d_nodeToLiteralMap[d_resolution[i].second]
          << "] ";
    }
    // special case for clause (or l1 ... ln) being a single literal corresponding itself to a
    // clause, which is indicated by the pivot being of the form (not (or l1 ... ln))
    if (d_resolution[i].first.getKind() == kind::OR
        && !(d_resolution[i].second.getKind() == kind::NOT
             && d_resolution[i].second[0].getKind() == kind::OR
             && d_resolution[i].second[0] == d_resolution[i].first))
    {
      for (unsigned j = 0, sizeJ = d_resolution[i].first.getNumChildren();
           j < sizeJ;
           ++j)
      {
        Trace("sat-proof")
            << d_cnfStream->d_nodeToLiteralMap[d_resolution[i].first[j]];
        if (j < sizeJ - 1)
        {
          Trace("sat-proof") << ", ";
        }
      }
    }
    else
    {
      Assert(d_cnfStream->d_nodeToLiteralMap.find(d_resolution[i].first)
             != d_cnfStream->d_nodeToLiteralMap.end())
          << "clause node " << d_resolution[i].first
          << " treated as unit has no literal. Pivot is "
          << d_resolution[i].second << "\n";
      Trace("sat-proof")
          << d_cnfStream->d_nodeToLiteralMap[d_resolution[i].first];
    }
    Trace("sat-proof") << " : ";
    if (i > 0)
    {
      args.push_back(d_resolution[i].second);
      Trace("sat-proof") << "[" << d_resolution[i].second << "] ";
    }
    Trace("sat-proof") << d_resolution[i].first << "\n";
  }
  // clearing
  d_resolution.clear();
  // since the conclusion can be both reordered and without duplucates and the
  // SAT solver does not record this information, we must recompute it here so
  // the proper CHAIN_RESOLUTION step can be created
  // compute chain resolution conclusion
  Node chainConclusion = d_pNodeManager->getChecker()->checkDebug(
      PfRule::CHAIN_RESOLUTION, children, args, Node::null(), "newproof::sat");
  // create step
  d_proof.addStep(chainConclusion, PfRule::CHAIN_RESOLUTION, children, args);
  if (chainConclusion != conclusion)
  {
    // if this happens that chainConclusion needs to be factored and/or
    // reordered, which in either case can be done only if it's not a unit
    // clause.
    CVC4_UNUSED Node reducedChainConclusion = factorAndReorder(chainConclusion);
    Assert(reducedChainConclusion == conclusion
           || reducedChainConclusion == factorAndReorder(conclusion))
        << "given res chain conclusion " << conclusion
        << "\nafter factorAndReorder " << factorAndReorder(conclusion)
        << "\nis different from chain_res " << chainConclusion
        << "\nafter factorAndReorder " << reducedChainConclusion;
  }
}

void PropEngine::tryJustifyingLit(SatLiteral lit)
{
  Node litNode = getClauseNode(lit);
  Trace("sat-proof") << CVC4::push
                     << "PropEngine::tryJustifyingLit: Lit: " << lit << " ["
                     << litNode << "]\n";
  if (d_clauseSet.count(litNode))
  {
    Trace("sat-proof") << "PropEngine::tryJustifyingLit: not "
                          "registered as clause\n"
                       << CVC4::pop;
    return;
  }
  Minisat::Solver::TCRef reasonRef = d_satSolver->getSolver()->reason(
      Minisat::var(MinisatSatSolver::toMinisatLit(lit)));
  if (reasonRef == Minisat::Solver::TCRef_Undef)
  {
    Trace("sat-proof") << "PropEngine::tryJustifyingLit: no SAT reason\n"
                       << CVC4::pop;
    return;
  }
  Assert(reasonRef >= 0 && reasonRef < d_satSolver->getSolver()->ca.size())
      << "reasonRef " << reasonRef << " and d_satSolver->ca.size() "
      << d_satSolver->getSolver()->ca.size() << "\n";
  // Here, the call to resolveUnit() can reallocate memory in the
  // clause allocator.  So reload reason ptr each time.
  const Minisat::Solver::TClause& initialReason =
      d_satSolver->getSolver()->ca[reasonRef];
  unsigned currentReason_size = initialReason.size();
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "PropEngine::tryJustifyingLit: with clause: ";
    printClause(initialReason);
    Trace("sat-proof") << "\n";
  }
  // add the reason clause first
  std::vector<Node> children{getClauseNode(initialReason)}, args;
  Trace("sat-proof") << CVC4::push;
  for (unsigned i = 0; i < currentReason_size; ++i)
  {
    const Minisat::Solver::TClause& currentReason =
        d_satSolver->getSolver()->ca[reasonRef];
    Assert(currentReason_size == static_cast<unsigned>(currentReason.size()));
    currentReason_size = currentReason.size();
    SatLiteral curr_lit = MinisatSatSolver::toSatLiteral(currentReason[i]);
    // ignore the lit we are trying to justify...
    if (curr_lit == lit)
    {
      continue;
    }
    tryJustifyingLit(~curr_lit);
    // save to resolution chain premises / arguments
    Assert(d_cnfStream->d_literalToNodeMap.find(curr_lit)
           != d_cnfStream->d_literalToNodeMap.end());
    children.push_back(d_cnfStream->d_literalToNodeMap[~curr_lit]);
    args.push_back(d_cnfStream->d_literalToNodeMap[curr_lit]);
  }
  Trace("sat-proof") << CVC4::pop;
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "PropEngine::tryJustifyingLit: chain_res for " << lit
                       << ", " << litNode << " with clauses:\n";
    for (unsigned i = 0, size = children.size(); i < size; ++i)
    {
      Trace("sat-proof") << "PropEngine::tryJustifyingLit:   " << children[i];
      if (i > 0)
      {
        Trace("sat-proof") << " [" << args[i - 1] << "]";
      }
      Trace("sat-proof") << "\n";
    }
  }
  // don't overwrite litNode. If it has a justification, it is as an assumption,
  // which may lead to cyclic proofs. When I'm properly doing the lazy proof
  // here it becomes a matter of it having a proof generator or not maybe?
  d_proof.addStep(litNode,
                  PfRule::CHAIN_RESOLUTION,
                  children,
                  args,
                  false,
                  CDPOverwrite::NEVER);
  Trace("sat-proof") << CVC4::pop;
}

void PropEngine::finalizeProof(Node inConflictNode,
                               const std::vector<SatLiteral>& inConflict)
{
  Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
  Trace("sat-proof") << "PropEngine::finalizeProof: conflicting clause node: "
                     << inConflictNode << "\n";
  // nothing to do
  if (inConflictNode == falseNode)
  {
    return;
  }
  // since this clause is conflicting, I must be able to resolve away each of
  // its literals l_1...l_n. Each literal ~l_i must be justifiable
  //
  // Either ~l_i is the conclusion of some previous, already built, step or from
  // a subproof to be computed.
  //
  // For each l_i, a resolution step is created with the id of the step allowing
  // the derivation of ~l_i, whose pivot in the inConflict will be l_i. All
  // resolution steps will be saved in the given reasons vector.
  Trace("sat-proof") << CVC4::push;
  // premises and arguments for final resolution
  std::vector<Node> children{inConflictNode}, args;
  for (unsigned i = 0, size = inConflict.size(); i < size; ++i)
  {
    Assert(d_cnfStream->d_literalToNodeMap.find(inConflict[i])
           != d_cnfStream->d_literalToNodeMap.end());
    tryJustifyingLit(~inConflict[i]);
    // save to resolution chain premises / arguments
    children.push_back(d_cnfStream->d_literalToNodeMap[~inConflict[i]]);
    args.push_back(d_cnfStream->d_literalToNodeMap[inConflict[i]]);
  }
  Trace("sat-proof") << CVC4::pop;
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof")
        << "PropEngine::finalizeProof: chain_res for false with clauses:\n";
    for (unsigned i = 0, size = children.size(); i < size; ++i)
    {
      Trace("sat-proof") << "PropEngine::finalizeProof:   " << children[i];
      if (i > 0)
      {
        Trace("sat-proof") << " [" << args[i - 1] << "]";
      }
      Trace("sat-proof") << "\n";
    }
  }
  // only build resolution if not cyclic
  d_proof.addStep(falseNode, PfRule::CHAIN_RESOLUTION, children, args);
}

void PropEngine::storeUnitConflict(Minisat::Solver::TLit inConflict)
{
  Assert(d_conflictLit == undefSatVariable);
  d_conflictLit = MinisatSatSolver::toSatLiteral(inConflict);
}

void PropEngine::finalizeProof()
{
  Assert(d_conflictLit != undefSatVariable);
  Trace("sat-proof") << "PropEngine::finalizeProof: conflicting (lazy) satLit: "
                     << d_conflictLit << "\n";
  finalizeProof(getClauseNode(d_conflictLit), {d_conflictLit});
}


void PropEngine::finalizeProof(Minisat::Solver::TLit inConflict)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(inConflict);
  Trace("sat-proof") << "PropEngine::finalizeProof: conflicting satLit: "
                     << satLit << "\n";
  finalizeProof(getClauseNode(satLit), {satLit});
}

void PropEngine::finalizeProof(Minisat::Solver::TClause& inConflict)
{
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "PropEngine::finalizeProof: conflicting clause: ";
    printClause(inConflict);
    Trace("sat-proof") << "\n";
  }
  std::vector<SatLiteral> clause;
  for (unsigned i = 0, size = inConflict.size(); i < size; ++i)
  {
    clause.push_back(MinisatSatSolver::toSatLiteral(inConflict[i]));
  }
  finalizeProof(getClauseNode(inConflict), clause);
}

}  // namespace prop
}  // namespace CVC4
