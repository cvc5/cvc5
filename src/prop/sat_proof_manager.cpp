/*********************                                                        */
/*! \file sat_proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the proof manager for Minisat
 **/

#include "prop/sat_proof_manager.h"

#include "expr/proof_node_algorithm.h"
#include "prop/cnf_stream.h"
#include "prop/minisat/minisat.h"
#include "prop/theory_proxy.h"

namespace CVC4 {
namespace prop {

SatProofManager::SatProofManager(Minisat::Solver* solver,
                                 CVC4::prop::TheoryProxy* proxy,
                                 context::UserContext* userContext,
                                 ProofNodeManager* pnm)
    : d_solver(solver),
      d_proxy(proxy),
      d_pnm(pnm),
      d_resChains(pnm, userContext),
      d_resChainPg(userContext, pnm),
      d_proof(pnm, userContext, "SatProofManager::CDProof"),
      d_false(NodeManager::currentNM()->mkConst(false)),
      d_conflictLit(undefSatVariable)
{
}

void SatProofManager::printClause(const Minisat::Clause& clause)
{
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    SatLiteral satLit = MinisatSatSolver::toSatLiteral(clause[i]);
    Trace("sat-proof") << satLit << " ";
  }
}

Node SatProofManager::getClauseNode(SatLiteral satLit)
{
  Assert(d_proxy->getCnfStream()->getNodeCache().find(satLit)
         != d_proxy->getCnfStream()->getNodeCache().end())
      << "SatProofManager::getClauseNode: literal " << satLit
      << " undefined.\n";
  return d_proxy->getCnfStream()->getNodeCache()[satLit];
}

Node SatProofManager::getClauseNode(const Minisat::Clause& clause)
{
  std::vector<Node> clauseNodes;
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    SatLiteral satLit = MinisatSatSolver::toSatLiteral(clause[i]);
    Assert(d_proxy->getCnfStream()->getNodeCache().find(satLit)
           != d_proxy->getCnfStream()->getNodeCache().end())
        << "SatProofManager::getClauseNode: literal " << satLit
        << " undefined\n";
    clauseNodes.push_back(d_proxy->getCnfStream()->getNodeCache()[satLit]);
  }
  // the ordering is done because throughout at the node level clauses are used
  // module their node id ordering
  std::sort(clauseNodes.begin(), clauseNodes.end());
  return NodeManager::currentNM()->mkNode(kind::OR, clauseNodes);
}

void SatProofManager::startResChain(const Minisat::Clause& start)
{
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::startResChain: ";
    printClause(start);
    Trace("sat-proof") << "\n";
  }
  d_resLinks.push_back(
      std::pair<Node, Node>(getClauseNode(start), Node::null()));
}

void SatProofManager::addResolutionStep(Minisat::Lit lit, bool redundant)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(lit);
  if (!redundant)
  {
    Trace("sat-proof") << "SatProofManager::addResolutionStep: [" << satLit
                       << "] " << ~satLit << "\n";
    d_resLinks.push_back(
        std::pair<Node, Node>(d_proxy->getCnfStream()->getNodeCache()[~satLit],
                              d_proxy->getCnfStream()->getNodeCache()[satLit]));
  }
  else
  {
    Trace("sat-proof") << "SatProofManager::addResolutionStep: redundant lit "
                       << satLit << " stored\n";
    d_redundantLits.push_back(satLit);
  }
}

void SatProofManager::addResolutionStep(const Minisat::Clause& clause,
                                        Minisat::Lit lit)
{
  // pivot is given as in the second clause, so we store its negation (which
  // will be removed positivly from the first clause and negatively from the
  // second)
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(~lit);
  Node clauseNode = getClauseNode(clause);
  d_resLinks.push_back(std::pair<Node, Node>(
      clauseNode, d_proxy->getCnfStream()->getNodeCache()[satLit]));
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::addResolutionStep: [" << satLit
                       << "] ";
    printClause(clause);
    Trace("sat-proof") << "\nSatProofManager::addResolutionStep:\t"
                       << clauseNode << "\n";
  }
}

void SatProofManager::endResChain(Minisat::Lit lit)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(lit);
  Trace("sat-proof") << "SatProofManager::endResChain: chain_res for "
                     << satLit;
  endResChain(getClauseNode(satLit), {satLit});
}

void SatProofManager::endResChain(const Minisat::Clause& clause)
{
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::endResChain: chain_res for ";
    printClause(clause);
  }
  std::set<SatLiteral> clauseLits;
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    clauseLits.insert(MinisatSatSolver::toSatLiteral(clause[i]));
  }
  endResChain(getClauseNode(clause), clauseLits);
}

// id is the conclusion
void SatProofManager::endResChain(Node conclusion,
                                  const std::set<SatLiteral>& conclusionLits)
{
  Trace("sat-proof") << ", " << conclusion << "\n";
  // first process redundant literals
  std::set<SatLiteral> visited;
  unsigned pos = d_resLinks.size();
  for (SatLiteral satLit : d_redundantLits)
  {
    processRedundantLit(satLit, conclusionLits, visited, pos);
  }
  d_redundantLits.clear();
  // build resolution chain
  std::vector<Node> children, args;
  for (unsigned i = 0, size = d_resLinks.size(); i < size; ++i)
  {
    children.push_back(d_resLinks[i].first);
    Trace("sat-proof") << "SatProofManager::endResChain:   ";
    if (i > 0)
    {
      Trace("sat-proof") << "["
                         << d_proxy->getCnfStream()
                                ->getTranslationCache()[d_resLinks[i].second]
                         << "] ";
    }
    // special case for clause (or l1 ... ln) being a single literal
    // corresponding itself to a clause, which is indicated by the pivot being
    // of the form (not (or l1 ... ln))
    if (d_resLinks[i].first.getKind() == kind::OR
        && !(d_resLinks[i].second.getKind() == kind::NOT
             && d_resLinks[i].second[0].getKind() == kind::OR
             && d_resLinks[i].second[0] == d_resLinks[i].first))
    {
      for (unsigned j = 0, sizeJ = d_resLinks[i].first.getNumChildren();
           j < sizeJ;
           ++j)
      {
        Trace("sat-proof")
            << d_proxy->getCnfStream()
                   ->getTranslationCache()[d_resLinks[i].first[j]];
        if (j < sizeJ - 1)
        {
          Trace("sat-proof") << ", ";
        }
      }
    }
    else
    {
      Assert(d_proxy->getCnfStream()->getTranslationCache().find(
                 d_resLinks[i].first)
             != d_proxy->getCnfStream()->getTranslationCache().end())
          << "clause node " << d_resLinks[i].first
          << " treated as unit has no literal. Pivot is "
          << d_resLinks[i].second << "\n";
      Trace("sat-proof") << d_proxy->getCnfStream()
                                ->getTranslationCache()[d_resLinks[i].first];
    }
    Trace("sat-proof") << " : ";
    if (i > 0)
    {
      args.push_back(d_resLinks[i].second);
      Trace("sat-proof") << "[" << d_resLinks[i].second << "] ";
    }
    Trace("sat-proof") << d_resLinks[i].first << "\n";
  }
  // clearing
  d_resLinks.clear();
  // whether no-op
  if (children.size() == 1)
  {
    Trace("sat-proof") << "SatProofManager::endResChain: no-op. The conclusion "
                       << conclusion << " is set-equal to premise "
                       << children[0] << "\n";
    return;
  }
  if (Trace.isOn("sat-proof") && d_resChains.hasGenerator(conclusion))
  {
    Trace("sat-proof") << "SatProofManager::endResChain: replacing proof of "
                       << conclusion << "\n";
  }
  // since the conclusion can be both reordered and without duplucates and the
  // SAT solver does not record this information, we must recompute it here so
  // the proper CHAIN_RESOLUTION step can be created
  // compute chain resolution conclusion
  Node chainConclusion = d_pnm->getChecker()->checkDebug(
      PfRule::CHAIN_RESOLUTION, children, args, Node::null(), "newproof::sat");
  Trace("sat-proof")
      << "SatProofManager::endResChain: creating step for computed conclusion "
      << chainConclusion << "\n";
  // buffer steps
  ProofStepBuffer psb;
  psb.addStep(PfRule::CHAIN_RESOLUTION, children, args, chainConclusion);
  if (chainConclusion != conclusion)
  {
    // if this happens that chainConclusion needs to be factored and/or
    // reordered, which in either case can be done only if it's not a unit
    // clause.
    CVC4_UNUSED Node reducedChainConclusion =
        CDProof::factorReorderElimDoubleNeg(chainConclusion, psb);
    Assert(reducedChainConclusion == conclusion
           || reducedChainConclusion
                  == CDProof::factorReorderElimDoubleNeg(conclusion, nullptr))
        << "given res chain conclusion " << conclusion
        << "\nafter factorReorderElimDoubleNeg "
        << CDProof::factorReorderElimDoubleNeg(conclusion, nullptr)
        << "\nis different from computed chain_res " << chainConclusion
        << "\nafter factorReorderElimDoubleNeg " << reducedChainConclusion;
  }
  // buffer the steps in the resolution chain proof generator
  const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
  for (const std::pair<Node, ProofStep>& step : steps)
  {
    Trace("sat-proof") << "SatProofManager::endResChain: adding for "
                       << step.first << " step " << step.second << "\n";
    d_resChainPg.addStep(step.first, step.second);
    // the premises of this resolution may not have been justified yet, so we do
    // not pass assumptions to check closedness
    d_resChains.addLazyStep(step.first, &d_resChainPg);
  }
}

void SatProofManager::processRedundantLit(
    SatLiteral lit,
    const std::set<SatLiteral>& conclusionLits,
    std::set<SatLiteral>& visited,
    unsigned pos)
{
  Trace("sat-proof") << CVC4::push
                     << "SatProofManager::processRedundantLit: Lit: " << lit
                     << "\n";
  if (visited.count(lit))
  {
    Trace("sat-proof") << "already visited\n" << CVC4::pop;
    return;
  }
  Minisat::Solver::TCRef reasonRef =
      d_solver->reason(Minisat::var(MinisatSatSolver::toMinisatLit(lit)));
  if (reasonRef == Minisat::Solver::TCRef_Undef)
  {
    Trace("sat-proof") << "unit, add link to lit " << lit << " at pos: " << pos
                       << "\n"
                       << CVC4::pop;
    visited.insert(lit);
    d_resLinks.insert(
        d_resLinks.begin() + pos,
        std::pair<Node, Node>(d_proxy->getCnfStream()->getNodeCache()[~lit],
                              d_proxy->getCnfStream()->getNodeCache()[lit]));
    return;
  }
  Assert(reasonRef >= 0 && reasonRef < d_solver->ca.size())
      << "reasonRef " << reasonRef << " and d_satSolver->ca.size() "
      << d_solver->ca.size() << "\n";
  const Minisat::Clause& reason = d_solver->ca[reasonRef];
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "reason: ";
    printClause(reason);
    Trace("sat-proof") << "\n";
  }
  // check if redundant literals in the reason. The first literal is the one we
  // will be eliminating, so we check the others
  for (unsigned i = 1, size = reason.size(); i < size; ++i)
  {
    SatLiteral satLit = MinisatSatSolver::toSatLiteral(reason[i]);
    // if literal does not occur in the conclusion we process it as well
    if (!conclusionLits.count(satLit))
    {
      processRedundantLit(satLit, conclusionLits, visited, pos);
    }
  }
  if (visited.count(lit))
  {
    Assert(false) << "how come?????\n";
  }
  visited.insert(lit);
  Trace("sat-proof") << "clause, add link to lit " << lit << " at pos: " << pos
                     << "\n"
                     << CVC4::pop;
  // add the step before steps for children
  Node clauseNode = getClauseNode(reason);
  d_resLinks.insert(
      d_resLinks.begin() + pos,
      std::pair<Node, Node>(clauseNode,
                            d_proxy->getCnfStream()->getNodeCache()[lit]));
}

void SatProofManager::tryJustifyingLit(SatLiteral lit)
{
  std::unordered_set<TNode, TNodeHashFunction> assumptions;
  tryJustifyingLit(lit, assumptions);
}

void SatProofManager::tryJustifyingLit(
    SatLiteral lit, std::unordered_set<TNode, TNodeHashFunction>& assumptions)
{
  Node litNode = getClauseNode(lit);
  Trace("sat-proof") << CVC4::push
                     << "SatProofManager::tryJustifyingLit: Lit: " << lit
                     << " [" << litNode << "]\n";
  Minisat::Solver::TCRef reasonRef =
      d_solver->reason(Minisat::var(MinisatSatSolver::toMinisatLit(lit)));
  if (reasonRef == Minisat::Solver::TCRef_Undef)
  {
    Trace("sat-proof") << "SatProofManager::tryJustifyingLit: no SAT reason\n";
    Trace("sat-proof") << CVC4::pop;
    return;
  }
  Assert(reasonRef >= 0 && reasonRef < d_solver->ca.size())
      << "reasonRef " << reasonRef << " and d_satSolver->ca.size() "
      << d_solver->ca.size() << "\n";
  const Minisat::Clause& initialReason = d_solver->ca[reasonRef];
  unsigned currentReason_size = initialReason.size();
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::tryJustifyingLit: with clause: ";
    printClause(initialReason);
    Trace("sat-proof") << "\n";
  }
  // pedantically check that the negation literal of the literal to justify
  // *does not* occur in the reason, otherwise we will loop forever
  for (unsigned i = 0; i < currentReason_size; ++i)
  {
    if (~MinisatSatSolver::toSatLiteral(initialReason[i]) == lit)
    {
      Trace("sat-proof")
          << "SatProofManager::tryJustifyingLit: cyclic justification\n"
          << CVC4::pop;
      return;
    }
  }
  // add the reason clause first
  std::vector<Node> children{getClauseNode(initialReason)}, args;
  // save in the assumptions
  assumptions.insert(children.back());
  Trace("sat-proof") << CVC4::push;
  for (unsigned i = 0; i < currentReason_size; ++i)
  {
    const Minisat::Clause& currentReason = d_solver->ca[reasonRef];
    Assert(currentReason_size == static_cast<unsigned>(currentReason.size()));
    currentReason_size = currentReason.size();
    SatLiteral curr_lit = MinisatSatSolver::toSatLiteral(currentReason[i]);
    // ignore the lit we are trying to justify...
    if (curr_lit == lit)
    {
      continue;
    }
    std::unordered_set<TNode, TNodeHashFunction> childAssumptions;
    tryJustifyingLit(~curr_lit, childAssumptions);
    // save to resolution chain premises / arguments
    Assert(d_proxy->getCnfStream()->getNodeCache().find(curr_lit)
           != d_proxy->getCnfStream()->getNodeCache().end());
    children.push_back(d_proxy->getCnfStream()->getNodeCache()[~curr_lit]);
    args.push_back(d_proxy->getCnfStream()->getNodeCache()[curr_lit]);
    // add child assumptions and the child itself
    assumptions.insert(childAssumptions.begin(), childAssumptions.end());
    assumptions.insert(d_proxy->getCnfStream()->getNodeCache()[~curr_lit]);
  }
  Trace("sat-proof") << CVC4::pop;
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::tryJustifyingLit: chain_res for "
                       << lit << ", " << litNode << " with clauses:\n";
    for (unsigned i = 0, size = children.size(); i < size; ++i)
    {
      Trace("sat-proof") << "SatProofManager::tryJustifyingLit:   "
                         << children[i];
      if (i > 0)
      {
        Trace("sat-proof") << " [" << args[i - 1] << "]";
      }
      Trace("sat-proof") << "\n";
    }
  }
  // if justification of children contains the expected conclusion, avoid the
  // cyclic proof by aborting.
  //
  // The SAT solver can for example here try to dedice (or a b c) via
  //
  // (CHAIN_RESOLUTION
  //   (ASSUME (or (or a b c) (not a)))
  //   (CHAIN_RESOLUTION
  //     (ASSUME |:args| ((or a b c)))
  //     (FACTORING
  //       (CHAIN_RESOLUTION
  //         (ASSUME |:args| ((or (not (or a b c)) (not (or c a b)))))
  //         (ASSUME |:args| ((or (or c a b) (not b))))
  //         (ASSUME |:args| ((or (or a b c) (not b))))
  //         |:args| ((not (or c a b)) (not (or a b c)))))
  //     (FACTORING
  //       (CHAIN_RESOLUTION
  //         (ASSUME |:args| ((or (not (or a b c)) (not (or c a b)))))
  //         (ASSUME |:args| ((or (or c a b) (not c))))
  //         (ASSUME |:args| ((or (or a b c) (not c))))
  //         |:args| ((not (or c a b)) (not (or a b c)))))
  //     |:args| (b c))
  //   |:args| (not a))
  //
  // where note that (or a b c) is an assumption. The above proof happens
  // because the literal being justified is (or a b c) but the premise is the
  // clause (or a b c), i.e. a list of three literals. Internally the SAT solver
  // does not realize this. We must therefore guard against it here.
  if (assumptions.count(litNode))
  {
    Trace("sat-proof") << "SatProofManager::tryJustifyingLit: CYCLIC PROOF of "
                       << lit << " [" << litNode << "], ABORT\n";
    Trace("sat-proof") << CVC4::pop;
    return;
  }
  Trace("sat-proof") << CVC4::pop;
  // create step
  ProofStep ps(PfRule::CHAIN_RESOLUTION, children, args);
  d_resChainPg.addStep(litNode, ps);
  // the premises in the limit of the justification may correspond to other
  // links in the chain which have, themselves, literals yet to be justified. So
  // we are not ready yet to check closedness w.r.t. CNF transformation of the
  // preprocessed assertions
  d_resChains.addLazyStep(litNode, &d_resChainPg);
}

void SatProofManager::finalizeProof(Node inConflictNode,
                                    const std::vector<SatLiteral>& inConflict)
{
  Trace("sat-proof")
      << "SatProofManager::finalizeProof: conflicting clause node: "
      << inConflictNode << "\n";
  // nothing to do
  if (inConflictNode == d_false)
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
  std::unordered_set<TNode, TNodeHashFunction> assumptions;
  for (unsigned i = 0, size = inConflict.size(); i < size; ++i)
  {
    Assert(d_proxy->getCnfStream()->getNodeCache().find(inConflict[i])
           != d_proxy->getCnfStream()->getNodeCache().end());
    std::unordered_set<TNode, TNodeHashFunction> childAssumptions;
    tryJustifyingLit(~inConflict[i], childAssumptions);
    Node negatedLitNode =
        d_proxy->getCnfStream()->getNodeCache()[~inConflict[i]];
    // save to resolution chain premises / arguments
    children.push_back(negatedLitNode);
    args.push_back(d_proxy->getCnfStream()->getNodeCache()[inConflict[i]]);
    // add child assumptions and the child itself
    assumptions.insert(childAssumptions.begin(), childAssumptions.end());
    assumptions.insert(negatedLitNode);
    Trace("sat-proof") << "===========\n";
  }
  Trace("sat-proof") << CVC4::pop;
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::finalizeProof: chain_res for false "
                          "with clauses:\n";
    for (unsigned i = 0, size = children.size(); i < size; ++i)
    {
      Trace("sat-proof") << "SatProofManager::finalizeProof:   " << children[i];
      if (i > 0)
      {
        Trace("sat-proof") << " [" << args[i - 1] << "]";
      }
      Trace("sat-proof") << "\n";
    }
  }
  // create step
  ProofStep ps(PfRule::CHAIN_RESOLUTION, children, args);
  d_resChainPg.addStep(d_false, ps);
  // not yet ready to check closedness because maybe only now we will justify
  // literals used in resolutions
  d_resChains.addLazyStep(d_false, &d_resChainPg);
  // Fix point justification of literals in leaves of the proof of false
  bool expanded;
  do
  {
    expanded = false;
    Trace("sat-proof") << "expand assumptions to prove false\n";
    std::shared_ptr<ProofNode> pfn = d_resChains.getProofFor(d_false);
    Trace("sat-proof-debug") << "sat proof of flase: " << *pfn.get() << "\n";
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(pfn.get(), fassumps);
    if (Trace.isOn("sat-proof"))
    {
      for (const Node& fa : fassumps)
      {
        Trace("sat-proof") << "- ";
        auto it = d_proxy->getCnfStream()->getTranslationCache().find(fa);
        if (it != d_proxy->getCnfStream()->getTranslationCache().end())
        {
          Trace("sat-proof") << it->second << "\n";
          continue;
        }
        // then it's a clause
        Assert(fa.getKind() == kind::OR);
        for (const Node& n : fa)
        {
          it = d_proxy->getCnfStream()->getTranslationCache().find(n);
          Assert(it != d_proxy->getCnfStream()->getTranslationCache().end());
          Trace("sat-proof") << it->second << " ";
        }
        Trace("sat-proof") << "\n";
      }
    }

    // for each assumption, see if it has a reason
    for (const Node& fa : fassumps)
    {
      // ignore already processed assumptions
      if (assumptions.count(fa))
      {
        continue;
      }
      // ignore non-literals
      auto it = d_proxy->getCnfStream()->getTranslationCache().find(fa);
      if (it == d_proxy->getCnfStream()->getTranslationCache().end())
      {
        Trace("sat-proof") << "no lit assumption " << fa << "\n";
        assumptions.insert(fa);
        continue;
      }
      Trace("sat-proof") << "lit assumption (" << it->second << "), " << fa
                         << "\n";
      // mark another iteration for the loop, as some resolution link may be
      // connected because of the new justifications
      expanded = true;
      std::unordered_set<TNode, TNodeHashFunction> childAssumptions;
      tryJustifyingLit(it->second, childAssumptions);
      // add the assumptions used in the justification. We know they will have
      // been as expanded as possible
      assumptions.insert(childAssumptions.begin(), childAssumptions.end());
      // add free assumption itself
      assumptions.insert(fa);
    }
  } while (expanded);
  // now we should be able to close it
  d_resChains.addLazyStep(d_false, &d_resChainPg, d_assumptions);
}

void SatProofManager::storeUnitConflict(Minisat::Lit inConflict)
{
  Assert(d_conflictLit == undefSatVariable);
  d_conflictLit = MinisatSatSolver::toSatLiteral(inConflict);
}

void SatProofManager::finalizeProof()
{
  Assert(d_conflictLit != undefSatVariable);
  Trace("sat-proof")
      << "SatProofManager::finalizeProof: conflicting (lazy) satLit: "
      << d_conflictLit << "\n";
  finalizeProof(getClauseNode(d_conflictLit), {d_conflictLit});
}

void SatProofManager::finalizeProof(Minisat::Lit inConflict, bool adding)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(inConflict);
  Trace("sat-proof") << "SatProofManager::finalizeProof: conflicting satLit: "
                     << satLit << "\n";
  Node clauseNode = getClauseNode(satLit);
  if (adding)
  {
    registerSatAssumptions({clauseNode});
  }
  finalizeProof(clauseNode, {satLit});
}

void SatProofManager::finalizeProof(const Minisat::Clause& inConflict,
                                    bool adding)
{
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof")
        << "SatProofManager::finalizeProof: conflicting clause: ";
    printClause(inConflict);
    Trace("sat-proof") << "\n";
  }
  std::vector<SatLiteral> clause;
  for (unsigned i = 0, size = inConflict.size(); i < size; ++i)
  {
    clause.push_back(MinisatSatSolver::toSatLiteral(inConflict[i]));
  }
  Node clauseNode = getClauseNode(inConflict);
  if (adding)
  {
    registerSatAssumptions({clauseNode});
  }
  finalizeProof(clauseNode, clause);
}

CDProof* SatProofManager::getProof()
{
  std::shared_ptr<ProofNode> pfn = d_resChains.getProofFor(d_false);
  if (pfn)
  {
    d_proof.addProof(pfn);
  }
  return &d_proof;
}

void SatProofManager::registerSatAssumptions(Minisat::Lit lit)
{
  Trace("sat-proof") << "SatProofManager::registerSatAssumptions: - "
                     << getClauseNode(MinisatSatSolver::toSatLiteral(lit))
                     << "\n";
  d_assumptions.push_back(getClauseNode(MinisatSatSolver::toSatLiteral(lit)));
}

void SatProofManager::registerSatAssumptions(const std::vector<Node>& assumps)
{
  if (Trace.isOn("sat-proof"))
  {
    for (const Node& a : assumps)
    {
      Trace("sat-proof") << "SatProofManager::registerSatAssumptions: - " << a
                         << "\n";
    }
  }
  d_assumptions.insert(d_assumptions.end(), assumps.begin(), assumps.end());
}

}  // namespace prop
}  // namespace CVC4
