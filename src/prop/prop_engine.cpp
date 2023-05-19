/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the propositional engine of cvc5.
 */

#include "prop/prop_engine.h"

#include <iomanip>
#include <map>
#include <utility>

#include "base/check.h"
#include "base/output.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/decision_options.h"
#include "options/main_options.h"
#include "options/options.h"
#include "options/proof_options.h"
#include "options/smt_options.h"
#include "proof/proof_node_algorithm.h"
#include "prop/cnf_stream.h"
#include "prop/minisat/minisat.h"
#include "prop/prop_proof_manager.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_factory.h"
#include "prop/theory_proxy.h"
#include "smt/env.h"
#include "theory/output_channel.h"
#include "theory/theory_engine.h"
#include "util/resource_manager.h"
#include "util/result.h"

namespace cvc5::internal {
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

PropEngine::PropEngine(Env& env, TheoryEngine* te)
    : EnvObj(env),
      d_inCheckSat(false),
      d_theoryEngine(te),
      d_skdm(new SkolemDefManager(d_env.getContext(), d_env.getUserContext())),
      d_theoryProxy(nullptr),
      d_satSolver(nullptr),
      d_cnfStream(nullptr),
      d_pfCnfStream(nullptr),
      d_theoryLemmaPg(d_env, d_env.getUserContext(), "PropEngine::ThLemmaPg"),
      d_ppm(nullptr),
      d_interrupted(false),
      d_assumptions(d_env.getUserContext())
{
  Trace("prop") << "Constructing the PropEngine" << std::endl;
  context::UserContext* userContext = d_env.getUserContext();
  ProofNodeManager* pnm = d_env.getProofNodeManager();

  d_satSolver =
      SatSolverFactory::createCDCLTMinisat(d_env, statisticsRegistry());

  // CNF stream and theory proxy required pointers to each other, make the
  // theory proxy first
  d_theoryProxy = new TheoryProxy(d_env, this, d_theoryEngine, d_skdm.get());
  d_cnfStream = new CnfStream(env,
                              d_satSolver,
                              d_theoryProxy,
                              userContext,
                              FormulaLitPolicy::TRACK,
                              "prop");

  // connect theory proxy
  d_theoryProxy->finishInit(d_satSolver, d_cnfStream);
  bool satProofs = d_env.isSatProofProducing();
  // connect SAT solver
  d_satSolver->initialize(d_env.getContext(),
                          d_theoryProxy,
                          d_env.getUserContext(),
                          satProofs ? pnm : nullptr);
  if (satProofs)
  {
    d_pfCnfStream.reset(new ProofCnfStream(
        env,
        *d_cnfStream,
        static_cast<MinisatSatSolver*>(d_satSolver)->getProofManager()));
    d_ppm.reset(
        new PropPfManager(env, userContext, d_satSolver, d_pfCnfStream.get()));
  }
}

void PropEngine::finishInit()
{
  NodeManager* nm = NodeManager::currentNM();
  d_cnfStream->convertAndAssert(nm->mkConst(true), false, false);
  // this is necessary because if True is later asserted to the prop engine the
  // CNF stream will ignore it since the SAT solver already had it registered,
  // thus not having True as an assumption for the SAT proof. To solve this
  // issue we track it directly here
  if (isProofEnabled())
  {
    static_cast<MinisatSatSolver*>(d_satSolver)
        ->getProofManager()
        ->registerSatAssumptions({nm->mkConst(true)});
  }
  d_cnfStream->convertAndAssert(nm->mkConst(false).notNode(), false, false);
}

PropEngine::~PropEngine() {
  Trace("prop") << "Destructing the PropEngine" << std::endl;
  delete d_cnfStream;
  delete d_satSolver;
  delete d_theoryProxy;
}

TrustNode PropEngine::preprocess(TNode node,
                                 std::vector<theory::SkolemLemma>& newLemmas)
{
  return d_theoryProxy->preprocess(node, newLemmas);
}

TrustNode PropEngine::removeItes(TNode node,
                                 std::vector<theory::SkolemLemma>& newLemmas)
{
  return d_theoryProxy->removeItes(node, newLemmas);
}

void PropEngine::notifyTopLevelSubstitution(const Node& lhs,
                                            const Node& rhs) const
{
  d_theoryProxy->notifyTopLevelSubstitution(lhs, rhs);
  if (isOutputOn(OutputTag::SUBS))
  {
    Node eq = SkolemManager::getOriginalForm(lhs.eqNode(rhs));
    output(OutputTag::SUBS) << "(substitution " << eq << ")" << std::endl;
  }
  Assert(lhs.getType() == rhs.getType());
}

void PropEngine::assertInputFormulas(
    const std::vector<Node>& assertions,
    std::unordered_map<size_t, Node>& skolemMap)
{
  Assert(!d_inCheckSat) << "Sat solver in solve()!";
  d_theoryProxy->notifyInputFormulas(assertions, skolemMap);
  for (const Node& node : assertions)
  {
    Trace("prop") << "assertFormula(" << node << ")" << std::endl;
    assertInternal(node, false, false, true);
  }
}

void PropEngine::assertLemma(TrustNode tlemma, theory::LemmaProperty p)
{
  bool removable = isLemmaPropertyRemovable(p);

  // call preprocessor
  std::vector<theory::SkolemLemma> ppLemmas;
  TrustNode tplemma = d_theoryProxy->preprocessLemma(tlemma, ppLemmas);

  // do final checks on the lemmas we are about to send
  if (d_env.isTheoryProofProducing()
      && options().proof.proofCheck == options::ProofCheckMode::EAGER)
  {
    Assert(tplemma.getGenerator() != nullptr);
    // ensure closed, make the proof node eagerly here to debug
    tplemma.debugCheckClosed(
        options(), "te-proof-debug", "TheoryEngine::lemma");
    for (theory::SkolemLemma& lem : ppLemmas)
    {
      Assert(lem.d_lemma.getGenerator() != nullptr);
      lem.d_lemma.debugCheckClosed(
          options(), "te-proof-debug", "TheoryEngine::lemma_new");
    }
  }

  if (TraceIsOn("te-lemma"))
  {
    Trace("te-lemma") << "Lemma, output: " << tplemma.getProven() << std::endl;
    for (const theory::SkolemLemma& lem : ppLemmas)
    {
      Trace("te-lemma") << "Lemma, new lemma: " << lem.d_lemma.getProven()
                        << " (skolem is " << lem.d_skolem << ")" << std::endl;
    }
    Trace("te-lemma") << "removable = " << removable << std::endl;
  }

  // now, assert the lemmas
  assertLemmasInternal(tplemma, ppLemmas, removable);
}

void PropEngine::assertTrustedLemmaInternal(TrustNode trn, bool removable)
{
  Node node = trn.getNode();
  Trace("prop::lemmas") << "assertLemma(" << node << ")" << std::endl;
  if (isOutputOn(OutputTag::LEMMAS))
  {
    output(OutputTag::LEMMAS) << "(lemma ";
    // use original form of the lemma here
    output(OutputTag::LEMMAS) << SkolemManager::getOriginalForm(node);
    output(OutputTag::LEMMAS) << ")" << std::endl;
  }
  bool negated = trn.getKind() == TrustNodeKind::CONFLICT;
  // should have a proof generator if the theory engine is proof producing
  Assert(!d_env.isTheoryProofProducing() || trn.getGenerator() != nullptr);
  // if we are producing proofs for the SAT solver but not for theory engine,
  // then we need to prevent the lemma of being added as an assumption (since
  // the generator will be null). We use the default proof generator for lemmas.
  if (isProofEnabled() && !d_env.isTheoryProofProducing()
      && !trn.getGenerator())
  {
    Node actualNode = negated ? node.notNode() : node;
    d_theoryLemmaPg.addStep(actualNode, PfRule::THEORY_LEMMA, {}, {actualNode});
    trn = TrustNode::mkReplaceGenTrustNode(trn, &d_theoryLemmaPg);
  }
  assertInternal(node, negated, removable, false, trn.getGenerator());
}

void PropEngine::assertInternal(
    TNode node, bool negated, bool removable, bool input, ProofGenerator* pg)
{
  // Assert as (possibly) removable
  if (options().smt.unsatCoresMode == options::UnsatCoresMode::ASSUMPTIONS)
  {
    if (input)
    {
      d_cnfStream->ensureLiteral(node);
      if (negated)
      {
        d_assumptions.push_back(node.notNode());
      }
      else
      {
        d_assumptions.push_back(node);
      }
    }
    else
    {
      d_cnfStream->convertAndAssert(node, removable, negated);
    }
  }
  else if (isProofEnabled())
  {
    d_pfCnfStream->convertAndAssert(node, negated, removable, input, pg);
    // if input, register the assertion in the proof manager
    if (input)
    {
      d_ppm->registerAssertion(node);
    }
  }
  else
  {
    d_cnfStream->convertAndAssert(node, removable, negated);
  }
}

void PropEngine::assertLemmasInternal(
    TrustNode trn,
    const std::vector<theory::SkolemLemma>& ppLemmas,
    bool removable)
{
  if (!removable)
  {
    // notify skolem definitions first to ensure that the computation of
    // when a literal contains a skolem is accurate in the calls below.
    Trace("prop") << "Notify skolem definitions..." << std::endl;
    for (const theory::SkolemLemma& lem : ppLemmas)
    {
      d_theoryProxy->notifySkolemDefinition(lem.getProven(), lem.d_skolem);
    }
  }
  // Assert to the SAT solver first
  Trace("prop") << "Push to SAT..." << std::endl;
  if (!trn.isNull())
  {
    assertTrustedLemmaInternal(trn, removable);
  }
  for (const theory::SkolemLemma& lem : ppLemmas)
  {
    assertTrustedLemmaInternal(lem.d_lemma, removable);
  }
  // Note that this order is important for theories that send lemmas during
  // preregistration, as it impacts the order in which lemmas are processed
  // by default by the decision engine. In particular, sending to the SAT
  // solver first means that lemmas sent during preregistration in response to
  // the current lemma are processed after that lemma. This makes a difference
  // e.g. for string reduction lemmas, where preregistration lemmas are
  // introduced for skolems that appear in reductions. Moving the above
  // block after the one below has mixed performance on SMT-LIB strings logics.
  if (!removable)
  {
    Trace("prop") << "Notify assertions..." << std::endl;
    // also add to the decision engine, where notice we don't need proofs
    if (!trn.isNull())
    {
      // notify the theory proxy of the lemma
      d_theoryProxy->notifyAssertion(trn.getProven(), TNode::null(), true);
    }
    for (const theory::SkolemLemma& lem : ppLemmas)
    {
      d_theoryProxy->notifyAssertion(lem.getProven(), lem.d_skolem, true);
    }
  }
  Trace("prop") << "Finish " << trn << std::endl;
}

void PropEngine::requirePhase(TNode n, bool phase) {
  Trace("prop") << "requirePhase(" << n << ", " << phase << ")" << std::endl;

  Assert(n.getType().isBoolean());
  SatLiteral lit = d_cnfStream->getLiteral(n);
  d_satSolver->requirePhase(phase ? lit : ~lit);
}

bool PropEngine::isDecision(Node lit) const {
  Assert(isSatLiteral(lit));
  return d_satSolver->isDecision(d_cnfStream->getLiteral(lit).getSatVariable());
}

std::vector<Node> PropEngine::getPropDecisions() const
{
  std::vector<Node> decisions;
  std::vector<SatLiteral> miniDecisions = d_satSolver->getDecisions();
  for (SatLiteral d : miniDecisions)
  {
    decisions.push_back(d_cnfStream->getNode(d));
  }
  return decisions;
}

std::vector<Node> PropEngine::getPropOrderHeap() const
{
  return d_satSolver->getOrderHeap();
}

bool PropEngine::isFixed(TNode lit) const
{
  if (isSatLiteral(lit))
  {
    return d_satSolver->isFixed(d_cnfStream->getLiteral(lit).getSatVariable());
  }
  return false;
}

void PropEngine::printSatisfyingAssignment(){
  const CnfStream::NodeToLiteralMap& transCache =
    d_cnfStream->getTranslationCache();
  Trace("prop-value") << "Literal | Value | Expr" << std::endl
                      << "----------------------------------------"
                      << "-----------------" << std::endl;
  for(CnfStream::NodeToLiteralMap::const_iterator i = transCache.begin(),
      end = transCache.end();
      i != end;
      ++i) {
    std::pair<Node, SatLiteral> curr = *i;
    SatLiteral l = curr.second;
    if(!l.isNegated()) {
      Node n = curr.first;
      SatValue value = d_satSolver->modelValue(l);
      Trace("prop-value") << "'" << l << "' " << value << " " << n << std::endl;
    }
  }
}
void PropEngine::outputIncompleteReason(UnknownExplanation uexp,
                                        theory::IncompleteId iid)
{
  if (isOutputOn(OutputTag::INCOMPLETE))
  {
    output(OutputTag::INCOMPLETE) << "(incomplete ";
    output(OutputTag::INCOMPLETE) << uexp;
    if (iid != theory::IncompleteId::UNKNOWN)
    {
      output(OutputTag::INCOMPLETE) << " " << iid;
    }
    output(OutputTag::INCOMPLETE) << ")" << std::endl;
  }
}

Result PropEngine::checkSat() {
  Assert(!d_inCheckSat) << "Sat solver in solve()!";
  Trace("prop") << "PropEngine::checkSat()" << std::endl;

  // Mark that we are in the checkSat
  ScopedBool scopedBool(d_inCheckSat);
  d_inCheckSat = true;

  if (options().base.preprocessOnly)
  {
    outputIncompleteReason(UnknownExplanation::REQUIRES_FULL_CHECK);
    return Result(Result::UNKNOWN, UnknownExplanation::REQUIRES_FULL_CHECK);
  }

  // Note this currently ignores conflicts (a dangerous practice).
  d_theoryProxy->presolve();

  // Reset the interrupted flag
  d_interrupted = false;

  // Check the problem
  SatValue result;
  if (d_assumptions.size() == 0)
  {
    result = d_satSolver->solve();
  }
  else
  {
    std::vector<SatLiteral> assumptions;
    for (const Node& node : d_assumptions)
    {
      assumptions.push_back(d_cnfStream->getLiteral(node));
    }
    result = d_satSolver->solve(assumptions);
  }

  d_theoryProxy->postsolve();

  if( result == SAT_VALUE_UNKNOWN ) {
    ResourceManager* rm = resourceManager();
    UnknownExplanation why = UnknownExplanation::INTERRUPTED;
    if (rm->outOfTime())
    {
      why = UnknownExplanation::TIMEOUT;
    }
    if (rm->outOfResources())
    {
      why = UnknownExplanation::RESOURCEOUT;
    }
    outputIncompleteReason(why);
    return Result(Result::UNKNOWN, why);
  }

  if( result == SAT_VALUE_TRUE && TraceIsOn("prop") ) {
    printSatisfyingAssignment();
  }

  Trace("prop") << "PropEngine::checkSat() => " << result << std::endl;
  if (result == SAT_VALUE_TRUE)
  {
    if (d_theoryProxy->isModelUnsound())
    {
      outputIncompleteReason(UnknownExplanation::INCOMPLETE,
                             d_theoryProxy->getModelUnsoundId());
      return Result(Result::UNKNOWN, UnknownExplanation::INCOMPLETE);
    }
  }
  else if (d_theoryProxy->isRefutationUnsound())
  {
    outputIncompleteReason(UnknownExplanation::INCOMPLETE,
                           d_theoryProxy->getRefutationUnsoundId());
    return Result(Result::UNKNOWN, UnknownExplanation::INCOMPLETE);
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
  Assert(d_cnfStream->hasLiteral(node)) << node;

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

Node PropEngine::ensureLiteral(TNode n)
{
  // must preprocess
  Node preprocessed = getPreprocessedTerm(n);
  Trace("ensureLiteral") << "ensureLiteral preprocessed: " << preprocessed
                         << std::endl;
  if (isProofEnabled())
  {
    d_pfCnfStream->ensureLiteral(preprocessed);
  }
  else
  {
    d_cnfStream->ensureLiteral(preprocessed);
  }
  return preprocessed;
}

Node PropEngine::getPreprocessedTerm(TNode n)
{
  // must preprocess
  std::vector<theory::SkolemLemma> newLemmas;
  TrustNode tpn = d_theoryProxy->preprocess(n, newLemmas);
  // send lemmas corresponding to the skolems introduced by preprocessing n
  TrustNode trnNull;
  assertLemmasInternal(trnNull, newLemmas, false);
  return tpn.isNull() ? Node(n) : tpn.getNode();
}

Node PropEngine::getPreprocessedTerm(TNode n,
                                     std::vector<Node>& skAsserts,
                                     std::vector<Node>& sks)
{
  // get the preprocessed form of the term
  Node pn = getPreprocessedTerm(n);
  // initialize the set of skolems and assertions to process
  std::vector<Node> toProcessAsserts;
  std::vector<Node> toProcess;
  d_theoryProxy->getSkolems(pn, toProcessAsserts, toProcess);
  size_t index = 0;
  // until fixed point is reached
  while (index < toProcess.size())
  {
    Node ka = toProcessAsserts[index];
    Node k = toProcess[index];
    index++;
    if (std::find(sks.begin(), sks.end(), k) != sks.end())
    {
      // already added the skolem to the list
      continue;
    }
    // must preprocess lemmas as well
    Node kap = getPreprocessedTerm(ka);
    skAsserts.push_back(kap);
    sks.push_back(k);
    // get the skolems in the preprocessed form of the lemma ka
    d_theoryProxy->getSkolems(kap, toProcessAsserts, toProcess);
  }
  // return the preprocessed term
  return pn;
}

void PropEngine::push()
{
  Assert(!d_inCheckSat) << "Sat solver in solve()!";
  d_satSolver->push();
  Trace("prop") << "push()" << std::endl;
}

void PropEngine::pop()
{
  Assert(!d_inCheckSat) << "Sat solver in solve()!";
  d_satSolver->pop();
  Trace("prop") << "pop()" << std::endl;
}

void PropEngine::resetTrail()
{
  d_satSolver->resetTrail();
  Trace("prop") << "resetTrail()" << std::endl;
}

uint32_t PropEngine::getAssertionLevel() const
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
  Trace("prop") << "interrupt()" << std::endl;
}

void PropEngine::spendResource(Resource r)
{
  d_env.getResourceManager()->spendResource(r);
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

  for (TNode::kinded_iterator i = expl.begin(kind::AND),
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
  }

  return true;
}

void PropEngine::checkProof(const context::CDList<Node>& assertions)
{
  if (!d_env.isSatProofProducing())
  {
    return;
  }
  return d_ppm->checkProof(assertions);
}

CnfStream* PropEngine::getCnfStream() { return d_theoryProxy->getCnfStream(); }

ProofCnfStream* PropEngine::getProofCnfStream() { return d_pfCnfStream.get(); }

std::shared_ptr<ProofNode> PropEngine::getProof(bool connectCnf)
{
  if (!d_env.isSatProofProducing())
  {
    return nullptr;
  }
  Trace("sat-proof") << "PropEngine::getProof: getting proof with cnfStream's "
                        "lazycdproof cxt lvl "
                     << userContext()->getLevel() << "\n";
  return d_ppm->getProof(connectCnf);
}

std::vector<std::shared_ptr<ProofNode>> PropEngine::getProofLeaves(modes::ProofComponent pc)
{
  return d_ppm->getProofLeaves(pc);
}

bool PropEngine::isProofEnabled() const { return d_pfCnfStream != nullptr; }

void PropEngine::getUnsatCore(std::vector<Node>& core)
{
  if (options().smt.unsatCoresMode == options::UnsatCoresMode::ASSUMPTIONS)
  {
    Trace("unsat-core") << "PropEngine::getUnsatCore: via unsat assumptions"
                        << std::endl;
    std::vector<SatLiteral> unsat_assumptions;
    d_satSolver->getUnsatAssumptions(unsat_assumptions);
    for (const SatLiteral& lit : unsat_assumptions)
    {
      core.push_back(d_cnfStream->getNode(lit));
    }
  }
  else
  {
    Trace("unsat-core") << "PropEngine::getUnsatCore: via proof" << std::endl;
    // otherwise, it is just the free assumptions of the proof
    std::shared_ptr<ProofNode> pfn = getProof();
    expr::getFreeAssumptions(pfn.get(), core);
  }
}

std::vector<Node> PropEngine::getLearnedZeroLevelLiterals(
    modes::LearnedLitType ltype) const
{
  return d_theoryProxy->getLearnedZeroLevelLiterals(ltype);
}

std::vector<Node> PropEngine::getLearnedZeroLevelLiteralsForRestart() const
{
  return d_theoryProxy->getLearnedZeroLevelLiteralsForRestart();
}

modes::LearnedLitType PropEngine::getLiteralType(const Node& lit) const
{
  return d_theoryProxy->getLiteralType(lit);
}

}  // namespace prop
}  // namespace cvc5::internal
