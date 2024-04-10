/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the proof manager for the PropPfManager.
 */

#include "prop/prop_proof_manager.h"

#include "proof/proof_ensure_closed.h"
#include "proof/proof_node_algorithm.h"
#include "proof/theory_proof_step_buffer.h"
#include "prop/cnf_stream.h"
#include "prop/prop_proof_manager.h"
#include "prop/minisat/sat_proof_manager.h"
#include "prop/sat_solver.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace prop {

PropPfManager::PropPfManager(Env& env,
                             CDCLTSatSolver* satSolver,
                             CnfStream& cnf)
    : EnvObj(env),
      d_propProofs(userContext()),
      // Since the ProofCnfStream performs no equality reasoning, there is no
      // need to automatically add symmetry steps. Note that it is *safer* to
      // forbid this, since adding symmetry steps when proof nodes are being
      // updated may inadvertently generate cyclic proofs.
      //
      // This can happen for example if the proof cnf stream has a generator for
      // (= a b), whose proof depends on symmetry applied to (= b a). It does
      // not have a generator for (= b a). However if asked for a proof of the
      // fact (= b a) (after having expanded the proof of (= a b)), since it has
      // no genarotor for (= b a), a proof (= b a) can be generated via symmetry
      // on the proof of (= a b). As a result the assumption (= b a) would be
      // assigned a proof with assumption (= b a). This breakes the invariant of
      // the proof node manager of no cyclic proofs if the ASSUMPTION proof node
      // of both the assumption (= b a) we are asking the proof for and the
      // assumption (= b a) in the proof of (= a b) are the same.
      d_proof(
          env, nullptr, userContext(), "ProofCnfStream::LazyCDProof", false),
      d_pfpp(new ProofPostprocess(env, &d_proof)),
      d_pfCnfStream(env, cnf, this),
      d_satSolver(satSolver),
      d_assertions(userContext()),
      d_cnfStream(cnf),
      d_inputClauses(userContext()),
      d_lemmaClauses(userContext()),
      d_satPm(nullptr)
{
  // add trivial assumption. This is so that we can check the that the prop
  // engine's proof is closed, as the SAT solver's refutation proof may use True
  // as an assumption even when True is not given as an assumption. An example
  // is when a propagated literal has an empty explanation (i.e., it is a valid
  // literal), which leads to adding True as its explanation, since for creating
  // a learned clause we need at least two literals.
  d_assertions.push_back(nodeManager()->mkConst(true));
}

void PropPfManager::ensureLiteral(TNode n) { d_pfCnfStream.ensureLiteral(n); }

void PropPfManager::convertAndAssert(
    TNode node, bool negated, bool removable, bool input, ProofGenerator* pg)
{
  d_pfCnfStream.convertAndAssert(node, negated, removable, input, pg);
  // if input, register the assertion in the proof manager
  if (input)
  {
    d_assertions.push_back(node);
  }
}

void PropPfManager::registerAssertion(Node assertion)
{
  d_assertions.push_back(assertion);
}

void PropPfManager::checkProof(const context::CDList<Node>& assertions)
{
  Trace("sat-proof") << "PropPfManager::checkProof: Checking if resolution "
                        "proof of false is closed\n";
  std::shared_ptr<ProofNode> conflictProof = getProof(false);
  Assert(conflictProof);
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  // add given assertions d_assertions
  for (const Node& assertion : assertions)
  {
    d_assertions.push_back(assertion);
  }
  std::vector<Node> avec{d_assertions.begin(), d_assertions.end()};
  pfnEnsureClosedWrt(options(),
                     conflictProof.get(),
                     avec,
                     "sat-proof",
                     "PropPfManager::checkProof");
}

std::vector<Node> PropPfManager::getUnsatCoreLemmas()
{
  std::vector<Node> usedLemmas;
  std::vector<Node> allLemmas = getLemmaClauses();
  std::shared_ptr<ProofNode> satPf = getProof(false);
  std::vector<Node> satLeaves;
  expr::getFreeAssumptions(satPf.get(), satLeaves);
  for (const Node& lemma : allLemmas)
  {
    if (std::find(satLeaves.begin(), satLeaves.end(), lemma) != satLeaves.end())
    {
      usedLemmas.push_back(lemma);
    }
  }
  return usedLemmas;
}

std::vector<std::shared_ptr<ProofNode>> PropPfManager::getProofLeaves(
    modes::ProofComponent pc)
{
  Trace("sat-proof") << "PropPfManager::getProofLeaves: Getting " << pc
                     << " component proofs\n";
  std::vector<Node> fassumps;
  Assert(pc == modes::ProofComponent::THEORY_LEMMAS
         || pc == modes::ProofComponent::PREPROCESS);
  std::vector<std::shared_ptr<ProofNode>> pfs =
      pc == modes::ProofComponent::THEORY_LEMMAS ? getLemmaClausesProofs()
                                                 : getInputClausesProofs();
  std::shared_ptr<ProofNode> satPf = getProof(false);
  std::vector<Node> satLeaves;
  expr::getFreeAssumptions(satPf.get(), satLeaves);
  std::vector<std::shared_ptr<ProofNode>> usedPfs;
  for (const std::shared_ptr<ProofNode>& pf : pfs)
  {
    Node proven = pf->getResult();
    if (std::find(satLeaves.begin(), satLeaves.end(), proven) != satLeaves.end())
    {
      usedPfs.push_back(pf);
    }
  }
  return usedPfs;
}

std::shared_ptr<ProofNode> PropPfManager::getProof(bool connectCnf)
{
  auto it = d_propProofs.find(connectCnf);
  if (it != d_propProofs.end())
  {
    return it->second;
  }
  // retrieve the SAT solver's refutation proof
  Trace("sat-proof")
      << "PropPfManager::getProof: Getting resolution proof of false\n";
  std::shared_ptr<ProofNode> conflictProof = d_satSolver->getProof();
  Assert(conflictProof);
  if (TraceIsOn("sat-proof"))
  {
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(conflictProof.get(), fassumps);
    Trace("sat-proof")
        << "PropPfManager::getProof: initial free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof-debug")
        << "PropPfManager::getProof: proof is " << *conflictProof.get() << "\n";
    Trace("sat-proof")
        << "PropPfManager::getProof: Connecting with CNF proof\n";
  }
  if (!connectCnf)
  {
    // if the sat proof was previously connected to the cnf, then the
    // assumptions will have been updated and we'll not have the expected
    // behavior here (i.e., the sat proof with the clauses given to the SAT
    // solver as leaves). In this case we will build a new proof node in which
    // we will erase the connected proofs (via overwriting them with
    // assumptions). This will be done in a cloned proof node so we do not alter
    // what is stored in d_propProofs.
    if (d_propProofs.find(true) != d_propProofs.end())
    {
      CDProof cdp(d_env);
      // get the clauses added to the SAT solver and add them as assumptions
      std::vector<Node> inputs = getInputClauses();
      std::vector<Node> lemmas = getLemmaClauses();
      std::vector<Node> allAssumptions{inputs.begin(), inputs.end()};
      allAssumptions.insert(allAssumptions.end(), lemmas.begin(), lemmas.end());
      for (const Node& a : allAssumptions)
      {
        cdp.addStep(a, ProofRule::ASSUME, {}, {a});
      }
      // add the sat proof copying the proof nodes but not overwriting the
      // assumption clauses
      cdp.addProof(conflictProof, CDPOverwrite::NEVER, true);
      conflictProof = cdp.getProof(nodeManager()->mkConst(false));
    }
    d_propProofs[connectCnf] = conflictProof;
    return conflictProof;
  }
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  if (TraceIsOn("sat-proof"))
  {
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(conflictProof.get(), fassumps);
    Trace("sat-proof")
        << "PropPfManager::getProof: new free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof") << "PropPfManager::getProof: assertions are:\n";
    for (const Node& a : d_assertions)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof-debug")
        << "PropPfManager::getProof: proof is " << *conflictProof.get() << "\n";
  }
  d_propProofs[connectCnf] = conflictProof;
  return conflictProof;
}

Node PropPfManager::normalizeAndRegister(TNode clauseNode,
                                         bool input,
                                         bool doNormalize)
{
  Node normClauseNode = clauseNode;
  if (doNormalize)
  {
    TheoryProofStepBuffer psb;
    normClauseNode = psb.factorReorderElimDoubleNeg(clauseNode);
    const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
    for (const std::pair<Node, ProofStep>& step : steps)
    {
      d_proof.addStep(step.first, step.second);
    }
  }
  if (TraceIsOn("cnf") && normClauseNode != clauseNode)
  {
    Trace("cnf") << push
                 << "ProofCnfStream::normalizeAndRegister: steps to normalized "
                 << normClauseNode << "\n"
                 << pop;
  }
  Trace("cnf-input") << "New clause: " << normClauseNode << " " << input
                     << std::endl;
  if (input)
  {
    d_inputClauses.insert(normClauseNode);
  }
  else
  {
    d_lemmaClauses.insert(normClauseNode);
  }
  if (d_satPm)
  {
    d_satPm->registerSatAssumptions({normClauseNode});
  }
  return normClauseNode;
}

LazyCDProof* PropPfManager::getCnfProof() { return &d_proof; }

std::vector<Node> PropPfManager::computeAuxiliaryUnits(
    const std::vector<Node>& clauses)
{
  std::vector<Node> auxUnits;
  for (const Node& c : clauses)
  {
    if (c.getKind() != Kind::OR)
    {
      continue;
    }
    // Determine if any OR child occurs as a top level clause. If so, it may
    // be relevant to include this as a unit clause.
    for (const Node& l : c)
    {
      const Node& atom = l.getKind() == Kind::NOT ? l[0] : l;
      if (atom.getKind() == Kind::OR
          && std::find(clauses.begin(), clauses.end(), atom) != clauses.end()
          && std::find(auxUnits.begin(), auxUnits.end(), atom)
                 == auxUnits.end())
      {
        auxUnits.push_back(atom);
      }
    }
  }
  return auxUnits;
}

std::vector<Node> PropPfManager::getInputClauses()
{
  std::vector<Node> cls;
  for (const Node& c : d_inputClauses)
  {
    cls.push_back(c);
  }
  return cls;
}

std::vector<Node> PropPfManager::getLemmaClauses()
{
  std::vector<Node> cls;
  for (const Node& c : d_lemmaClauses)
  {
    cls.push_back(c);
  }
  return cls;
}

std::vector<std::shared_ptr<ProofNode>> PropPfManager::getInputClausesProofs()
{
  std::vector<std::shared_ptr<ProofNode>> pfs;
  for (const Node& a : d_inputClauses)
  {
    pfs.push_back(d_proof.getProofFor(a));
  }
  return pfs;
}

std::vector<std::shared_ptr<ProofNode>> PropPfManager::getLemmaClausesProofs()
{
  std::vector<std::shared_ptr<ProofNode>> pfs;
  for (const Node& a : d_lemmaClauses)
  {
    pfs.push_back(d_proof.getProofFor(a));
  }
  return pfs;
}

void PropPfManager::notifyExplainedPropagation(TrustNode trn)
{
  Node proven = trn.getProven();
  // If we are not producing proofs in the theory engine there is no need to
  // keep track in d_proof of the clausification. We still need however to let
  // the SAT proof manager know that this clause is an assumption.
  bool proofLogging = trn.getGenerator() != nullptr;
  Trace("cnf")
      << "PropPfManager::notifyExplainedPropagation: proven explanation"
      << proven << ", proofLogging=" << proofLogging << "\n";
  if (proofLogging)
  {
    Assert(trn.getGenerator()->getProofFor(proven)->isClosed());
    Trace("cnf-steps") << proven << " by explainPropagation "
                       << trn.identifyGenerator() << std::endl;
    d_proof.addLazyStep(proven,
                        trn.getGenerator(),
                        TrustId::NONE,
                        true,
                        "PropPfManager::notifyExplainedPropagation");
  }
  // since the propagation is added directly to the SAT solver via theoryProxy,
  // do the transformation of the lemma E1 ^ ... ^ En => P into CNF here
  NodeManager* nm = nodeManager();
  Node clauseImpliesElim;
  if (proofLogging)
  {
    clauseImpliesElim = nm->mkNode(Kind::OR, proven[0].notNode(), proven[1]);
    Trace("cnf") << "PropPfManager::notifyExplainedPropagation: adding "
                 << ProofRule::IMPLIES_ELIM << " rule to conclude "
                 << clauseImpliesElim << "\n";
    d_proof.addStep(clauseImpliesElim, ProofRule::IMPLIES_ELIM, {proven}, {});
  }
  Node clauseExp;
  // need to eliminate AND
  if (proven[0].getKind() == Kind::AND)
  {
    std::vector<Node> disjunctsAndNeg{proven[0]};
    std::vector<Node> disjunctsRes;
    for (unsigned i = 0, size = proven[0].getNumChildren(); i < size; ++i)
    {
      disjunctsAndNeg.push_back(proven[0][i].notNode());
      disjunctsRes.push_back(proven[0][i].notNode());
    }
    disjunctsRes.push_back(proven[1]);
    clauseExp = nm->mkNode(Kind::OR, disjunctsRes);
    if (proofLogging)
    {
      // add proof steps to convert into clause
      Node clauseAndNeg = nm->mkNode(Kind::OR, disjunctsAndNeg);
      d_proof.addStep(clauseAndNeg, ProofRule::CNF_AND_NEG, {}, {proven[0]});
      d_proof.addStep(clauseExp,
                      ProofRule::RESOLUTION,
                      {clauseAndNeg, clauseImpliesElim},
                      {nm->mkConst(true), proven[0]});
    }
  }
  else
  {
    clauseExp = nm->mkNode(Kind::OR, proven[0].notNode(), proven[1]);
  }
  d_currPropagationProcessed = normalizeAndRegister(clauseExp, false);
  // If we are not logging the clausification, we need to add the clause, as *it
  // will be saved in the SAT solver* (i.e., as clauseExp), as closed step in
  // the d_proof, so that there are no non-input assumptions.
  if (!proofLogging)
  {
    d_proof.addTrustedStep(clauseExp, TrustId::THEORY_LEMMA, {}, {clauseExp});
  }
}

Node PropPfManager::getLastExplainedPropagation() const
{
  return d_currPropagationProcessed;
}

void PropPfManager::resetLastExplainedPropagation()
{
  d_currPropagationProcessed = Node::null();
}

}  // namespace prop
}  // namespace cvc5::internal
