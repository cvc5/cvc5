/*********************                                                        */
/*! \file sat_proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the proof manager for Minisat
 **/

#include "prop/sat_proof_manager.h"

#include "expr/proof_node_algorithm.h"
#include "options/smt_options.h"
#include "prop/cnf_stream.h"
#include "prop/minisat/minisat.h"
#include "theory/theory_proof_step_buffer.h"

namespace CVC4 {
namespace prop {

SatProofManager::SatProofManager(Minisat::Solver* solver,
                                 CnfStream* cnfStream,
                                 context::UserContext* userContext,
                                 ProofNodeManager* pnm)
    : d_solver(solver),
      d_cnfStream(cnfStream),
      d_pnm(pnm),
      d_resChains(pnm, true, userContext),
      d_resChainPg(userContext, pnm),
      d_assumptions(userContext),
      d_conflictLit(undefSatVariable)
{
  d_false = NodeManager::currentNM()->mkConst(false);
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
  Assert(d_cnfStream->getNodeCache().find(satLit)
         != d_cnfStream->getNodeCache().end())
      << "SatProofManager::getClauseNode: literal " << satLit
      << " undefined.\n";
  return d_cnfStream->getNodeCache()[satLit];
}

Node SatProofManager::getClauseNode(const Minisat::Clause& clause)
{
  std::vector<Node> clauseNodes;
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    SatLiteral satLit = MinisatSatSolver::toSatLiteral(clause[i]);
    Assert(d_cnfStream->getNodeCache().find(satLit)
           != d_cnfStream->getNodeCache().end())
        << "SatProofManager::getClauseNode: literal " << satLit
        << " undefined\n";
    clauseNodes.push_back(d_cnfStream->getNodeCache()[satLit]);
  }
  // order children by node id
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
  d_resLinks.emplace_back(getClauseNode(start), Node::null(), true);
}

void SatProofManager::addResolutionStep(Minisat::Lit lit, bool redundant)
{
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(lit);
  Node litNode = d_cnfStream->getNodeCache()[satLit];
  bool negated = satLit.isNegated();
  Assert(!negated || litNode.getKind() == kind::NOT);
  if (!redundant)
  {
    Trace("sat-proof") << "SatProofManager::addResolutionStep: {"
                       << satLit.isNegated() << "} [" << satLit << "] "
                       << ~satLit << "\n";
    // if lit is negated then the chain resolution construction will use it as a
    // pivot occurring as is in the second clause and the node under the
    // negation in the first clause
    d_resLinks.emplace_back(d_cnfStream->getNodeCache()[~satLit],
                            negated ? litNode[0] : litNode,
                            !satLit.isNegated());
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
  SatLiteral satLit = MinisatSatSolver::toSatLiteral(lit);
  Node litNode = d_cnfStream->getNodeCache()[satLit];
  bool negated = satLit.isNegated();
  Assert(!negated || litNode.getKind() == kind::NOT);
  Node clauseNode = getClauseNode(clause);
  // if lit is negative then the chain resolution construction will use it as a
  // pivot occurring as is in the second clause and the node under the
  // negation in the first clause, which means that the third argument of the
  // tuple must be false
  d_resLinks.emplace_back(clauseNode, negated ? litNode[0] : litNode, negated);
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::addResolutionStep: {"
                       << satLit.isNegated() << "} [" << ~satLit << "] ";
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
  NodeManager* nm = NodeManager::currentNM();
  // the conclusion is stored already in the arguments because of the
  // possibility of reordering
  std::vector<Node> children, args{conclusion};
  for (unsigned i = 0, size = d_resLinks.size(); i < size; ++i)
  {
    Node clause, pivot;
    bool posFirst;
    std::tie(clause, pivot, posFirst) = d_resLinks[i];
    children.push_back(clause);
    Trace("sat-proof") << "SatProofManager::endResChain:   ";
    if (i > 0)
    {
      Trace("sat-proof") << "{" << posFirst << "} ["
                         << d_cnfStream->getTranslationCache()[pivot] << "] ";
    }
    // special case for clause (or l1 ... ln) being a single literal
    // corresponding itself to a clause, which is indicated by the pivot being
    // of the form (not (or l1 ... ln))
    if (clause.getKind() == kind::OR
        && !(pivot.getKind() == kind::NOT && pivot[0].getKind() == kind::OR
             && pivot[0] == clause))
    {
      for (unsigned j = 0, sizeJ = clause.getNumChildren(); j < sizeJ; ++j)
      {
        Trace("sat-proof") << d_cnfStream->getTranslationCache()[clause[j]];
        if (j < sizeJ - 1)
        {
          Trace("sat-proof") << ", ";
        }
      }
    }
    else
    {
      Assert(d_cnfStream->getTranslationCache().find(clause)
             != d_cnfStream->getTranslationCache().end())
          << "clause node " << clause
          << " treated as unit has no literal. Pivot is " << pivot << "\n";
      Trace("sat-proof") << d_cnfStream->getTranslationCache()[clause];
    }
    Trace("sat-proof") << " : ";
    if (i > 0)
    {
      args.push_back(nm->mkConst(posFirst));
      args.push_back(pivot);
      Trace("sat-proof") << "{" << posFirst << "} [" << pivot << "] ";
    }
    Trace("sat-proof") << clause << "\n";
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
  // since the conclusion can be both reordered and without duplicates and the
  // SAT solver does not record this information, we use a MACRO_RESOLUTION
  // step, which bypasses these. Note that we could generate a chain resolution
  // rule here by explicitly computing the detailed steps, but leave this for
  // post-processing.
  ProofStep ps(PfRule::MACRO_RESOLUTION, children, args);
  d_resChainPg.addStep(conclusion, ps);
  // the premises of this resolution may not have been justified yet, so we do
  // not pass assumptions to check closedness
  d_resChains.addLazyStep(conclusion, &d_resChainPg);
}

void SatProofManager::processRedundantLit(
    SatLiteral lit,
    const std::set<SatLiteral>& conclusionLits,
    std::set<SatLiteral>& visited,
    unsigned pos)
{
  Trace("sat-proof") << push
                     << "SatProofManager::processRedundantLit: Lit: " << lit
                     << "\n";
  if (visited.count(lit))
  {
    Trace("sat-proof") << "already visited\n" << pop;
    return;
  }
  Minisat::Solver::TCRef reasonRef =
      d_solver->reason(Minisat::var(MinisatSatSolver::toMinisatLit(lit)));
  if (reasonRef == Minisat::Solver::TCRef_Undef)
  {
    Trace("sat-proof") << "unit, add link to lit " << lit << " at pos: " << pos
                       << "\n"
                       << pop;
    visited.insert(lit);
    Node litNode = d_cnfStream->getNodeCache()[lit];
    bool negated = lit.isNegated();
    Assert(!negated || litNode.getKind() == kind::NOT);

    d_resLinks.emplace(d_resLinks.begin() + pos,
                       d_cnfStream->getNodeCache()[~lit],
                       negated ? litNode[0] : litNode,
                       !negated);
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
  Assert(!visited.count(lit));
  visited.insert(lit);
  Trace("sat-proof") << "clause, add link to lit " << lit << " at pos: " << pos
                     << "\n"
                     << pop;
  // add the step before steps for children. Note that the step is with the
  // reason, not only with ~lit, since the learned clause is built under the
  // assumption that the redundant literal is removed via the resolution with
  // the explanation of its negation
  Node clauseNode = getClauseNode(reason);
  Node litNode = d_cnfStream->getNodeCache()[lit];
  bool negated = lit.isNegated();
  Assert(!negated || litNode.getKind() == kind::NOT);
  d_resLinks.emplace(d_resLinks.begin() + pos,
                     clauseNode,
                     negated ? litNode[0] : litNode,
                     !negated);
}

void SatProofManager::explainLit(
    SatLiteral lit, std::unordered_set<TNode, TNodeHashFunction>& premises)
{
  Node litNode = getClauseNode(lit);
  Trace("sat-proof") << push << "SatProofManager::explainLit: Lit: " << lit
                     << " [" << litNode << "]\n";
  Minisat::Solver::TCRef reasonRef =
      d_solver->reason(Minisat::var(MinisatSatSolver::toMinisatLit(lit)));
  if (reasonRef == Minisat::Solver::TCRef_Undef)
  {
    Trace("sat-proof") << "SatProofManager::explainLit: no SAT reason\n" << pop;
    return;
  }
  Assert(reasonRef >= 0 && reasonRef < d_solver->ca.size())
      << "reasonRef " << reasonRef << " and d_satSolver->ca.size() "
      << d_solver->ca.size() << "\n";
  const Minisat::Clause& reason = d_solver->ca[reasonRef];
  unsigned size = reason.size();
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << "SatProofManager::explainLit: with clause: ";
    printClause(reason);
    Trace("sat-proof") << "\n";
  }
  // pedantically check that the negation of the literal to explain *does not*
  // occur in the reason, otherwise we will loop forever
  for (unsigned i = 0; i < size; ++i)
  {
    AlwaysAssert(~MinisatSatSolver::toSatLiteral(reason[i]) != lit)
        << "cyclic justification\n";
  }
  // add the reason clause first
  std::vector<Node> children{getClauseNode(reason)}, args;
  // save in the premises
  premises.insert(children.back());
  NodeManager* nm = NodeManager::currentNM();
  Trace("sat-proof") << push;
  for (unsigned i = 0; i < size; ++i)
  {
    SatLiteral curr_lit = MinisatSatSolver::toSatLiteral(reason[i]);
    // ignore the lit we are trying to explain...
    if (curr_lit == lit)
    {
      continue;
    }
    std::unordered_set<TNode, TNodeHashFunction> childPremises;
    explainLit(~curr_lit, childPremises);
    // save to resolution chain premises / arguments
    Assert(d_cnfStream->getNodeCache().find(curr_lit)
           != d_cnfStream->getNodeCache().end());
    children.push_back(d_cnfStream->getNodeCache()[~curr_lit]);
    Node currLitNode = d_cnfStream->getNodeCache()[curr_lit];
    bool negated = curr_lit.isNegated();
    Assert(!negated || currLitNode.getKind() == kind::NOT);
    // note this is the opposite of what is done in addResolutionStep. This is
    // because here the clause, which contains the literal being analyzed, is
    // the first clause rather than the second
    args.push_back(nm->mkConst(!negated));
    args.push_back(negated ? currLitNode[0] : currLitNode);
    // add child premises and the child itself
    premises.insert(childPremises.begin(), childPremises.end());
    premises.insert(d_cnfStream->getNodeCache()[~curr_lit]);
  }
  if (Trace.isOn("sat-proof"))
  {
    Trace("sat-proof") << pop << "SatProofManager::explainLit: chain_res for "
                       << lit << ", " << litNode << " with clauses:\n";
    for (unsigned i = 0, csize = children.size(); i < csize; ++i)
    {
      Trace("sat-proof") << "SatProofManager::explainLit:   " << children[i];
      if (i > 0)
      {
        Trace("sat-proof") << " [" << args[i - 1] << "]";
      }
      Trace("sat-proof") << "\n";
    }
  }
  // if justification of children contains the expected conclusion, avoid the
  // cyclic proof by aborting.
  if (premises.count(litNode))
  {
    Trace("sat-proof") << "SatProofManager::explainLit: CYCLIC PROOF of " << lit
                       << " [" << litNode << "], ABORT\n"
                       << pop;
    return;
  }
  Trace("sat-proof") << pop;
  // create step
  args.insert(args.begin(), litNode);
  ProofStep ps(PfRule::MACRO_RESOLUTION, children, args);
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
  if (Trace.isOn("sat-proof-debug2"))
  {
    Trace("sat-proof-debug2")
        << push << "SatProofManager::finalizeProof: saved proofs in chain:\n";
    std::map<Node, std::shared_ptr<ProofNode>> links = d_resChains.getLinks();
    std::unordered_set<Node, NodeHashFunction> skip;
    for (const std::pair<const Node, std::shared_ptr<ProofNode>>& link : links)
    {
      if (skip.count(link.first))
      {
        continue;
      }
      auto it = d_cnfStream->getTranslationCache().find(link.first);
      if (it != d_cnfStream->getTranslationCache().end())
      {
        Trace("sat-proof-debug2")
            << "SatProofManager::finalizeProof:  " << it->second;
      }
      // a refl step added due to double elim negation, ignore
      else if (link.second->getRule() == PfRule::REFL)
      {
        continue;
      }
      // a clause
      else
      {
        Trace("sat-proof-debug2") << "SatProofManager::finalizeProof:";
        Assert(link.first.getKind() == kind::OR) << link.first;
        for (const Node& n : link.first)
        {
          it = d_cnfStream->getTranslationCache().find(n);
          Assert(it != d_cnfStream->getTranslationCache().end());
          Trace("sat-proof-debug2") << it->second << " ";
        }
      }
      Trace("sat-proof-debug2") << "\n";
      Trace("sat-proof-debug2")
          << "SatProofManager::finalizeProof: " << link.first << "\n";
      // get resolution
      Node cur = link.first;
      std::shared_ptr<ProofNode> pfn = link.second;
      while (pfn->getRule() != PfRule::MACRO_RESOLUTION)
      {
        Assert(pfn->getChildren().size() == 1
               && pfn->getChildren()[0]->getRule() == PfRule::ASSUME)
            << *link.second.get() << "\n"
            << *pfn.get();
        cur = pfn->getChildren()[0]->getResult();
        // retrieve justification of assumption in the links
        Assert(links.find(cur) != links.end());
        pfn = links[cur];
        // ignore it in the rest of the outside loop
        skip.insert(cur);
      }
      std::vector<Node> fassumps;
      expr::getFreeAssumptions(pfn.get(), fassumps);
      Trace("sat-proof-debug2") << push;
      for (const Node& fa : fassumps)
      {
        Trace("sat-proof-debug2") << "SatProofManager::finalizeProof:   - ";
        it = d_cnfStream->getTranslationCache().find(fa);
        if (it != d_cnfStream->getTranslationCache().end())
        {
          Trace("sat-proof-debug2") << it->second << "\n";
          continue;
        }
        // then it's a clause
        Assert(fa.getKind() == kind::OR);
        for (const Node& n : fa)
        {
          it = d_cnfStream->getTranslationCache().find(n);
          Assert(it != d_cnfStream->getTranslationCache().end());
          Trace("sat-proof-debug2") << it->second << " ";
        }
        Trace("sat-proof-debug2") << "\n";
      }
      Trace("sat-proof-debug2") << pop;
      Trace("sat-proof-debug2")
          << "SatProofManager::finalizeProof:  " << *pfn.get() << "\n=======\n";
      ;
    }
    Trace("sat-proof-debug2") << pop;
  }
  // We will resolve away of the literals l_1...l_n in inConflict. At this point
  // each ~l_i must be either explainable, the result of a previously saved
  // resolution chain, or an input. In account of it possibly being the first,
  // we call explainLit on each ~l_i while accumulating the children and
  // arguments for the resolution step to conclude false.
  std::vector<Node> children{inConflictNode}, args;
  std::unordered_set<TNode, TNodeHashFunction> premises;
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = inConflict.size(); i < size; ++i)
  {
    Assert(d_cnfStream->getNodeCache().find(inConflict[i])
           != d_cnfStream->getNodeCache().end());
    std::unordered_set<TNode, TNodeHashFunction> childPremises;
    explainLit(~inConflict[i], childPremises);
    Node negatedLitNode = d_cnfStream->getNodeCache()[~inConflict[i]];
    // save to resolution chain premises / arguments
    children.push_back(negatedLitNode);
    Node litNode = d_cnfStream->getNodeCache()[inConflict[i]];
    bool negated = inConflict[i].isNegated();
    Assert(!negated || litNode.getKind() == kind::NOT);
    // note this is the opposite of what is done in addResolutionStep. This is
    // because here the clause, which contains the literal being analyzed, is
    // the first clause rather than the second
    args.push_back(nm->mkConst(!negated));
    args.push_back(negated ? litNode[0] : litNode);
    // add child premises and the child itself
    premises.insert(childPremises.begin(), childPremises.end());
    premises.insert(negatedLitNode);
    Trace("sat-proof") << "===========\n";
  }
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
  args.insert(args.begin(), d_false);
  ProofStep ps(PfRule::MACRO_RESOLUTION, children, args);
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
    Assert(pfn);
    Trace("sat-proof-debug") << "sat proof of flase: " << *pfn.get() << "\n";
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(pfn.get(), fassumps);
    if (Trace.isOn("sat-proof"))
    {
      for (const Node& fa : fassumps)
      {
        Trace("sat-proof") << "- ";
        auto it = d_cnfStream->getTranslationCache().find(fa);
        if (it != d_cnfStream->getTranslationCache().end())
        {
          Trace("sat-proof") << it->second << "\n";
          Trace("sat-proof") << "- " << fa << "\n";
          continue;
        }
        // then it's a clause
        Assert(fa.getKind() == kind::OR);
        for (const Node& n : fa)
        {
          it = d_cnfStream->getTranslationCache().find(n);
          Assert(it != d_cnfStream->getTranslationCache().end());
          Trace("sat-proof") << it->second << " ";
        }
        Trace("sat-proof") << "\n";
        Trace("sat-proof") << "- " << fa << "\n";
      }
    }

    // for each assumption, see if it has a reason
    for (const Node& fa : fassumps)
    {
      // ignore already processed assumptions
      if (premises.count(fa))
      {
        Trace("sat-proof") << "already processed assumption " << fa << "\n";
        continue;
      }
      // ignore input assumptions. This is necessary to avoid rare collisions
      // between input clauses and literals that are equivalent at the node
      // level. In trying to justify the literal below if, it was previously
      // propagated (say, in a previous check-sat call that survived the
      // user-context changes) but no longer holds, then we may introduce a
      // bogus proof for it, rather than keeping it as an input.
      if (d_assumptions.contains(fa))
      {
        Trace("sat-proof") << "input assumption " << fa << "\n";
        continue;
      }
      // ignore non-literals
      auto it = d_cnfStream->getTranslationCache().find(fa);
      if (it == d_cnfStream->getTranslationCache().end())
      {
        Trace("sat-proof") << "no lit assumption " << fa << "\n";
        premises.insert(fa);
        continue;
      }
      Trace("sat-proof") << "lit assumption (" << it->second << "), " << fa
                         << "\n";
      // mark another iteration for the loop, as some resolution link may be
      // connected because of the new justifications
      expanded = true;
      std::unordered_set<TNode, TNodeHashFunction> childPremises;
      explainLit(it->second, childPremises);
      // add the premises used in the justification. We know they will have
      // been as expanded as possible
      premises.insert(childPremises.begin(), childPremises.end());
      // add free assumption itself
      premises.insert(fa);
    }
  } while (expanded);
  // now we should be able to close it
  if (options::proofNewEagerChecking())
  {
    std::vector<Node> assumptionsVec;
    for (const Node& a : d_assumptions)
    {
      assumptionsVec.push_back(a);
    }
    d_resChains.addLazyStep(d_false, &d_resChainPg, assumptionsVec);
  }
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

std::shared_ptr<ProofNode> SatProofManager::getProof()
{
  std::shared_ptr<ProofNode> pfn = d_resChains.getProofFor(d_false);
  if (!pfn)
  {
    pfn = d_pnm->mkAssume(d_false);
  }
  return pfn;
}

void SatProofManager::registerSatLitAssumption(Minisat::Lit lit)
{
  Trace("sat-proof") << "SatProofManager::registerSatLitAssumption: - "
                     << getClauseNode(MinisatSatSolver::toSatLiteral(lit))
                     << "\n";
  d_assumptions.insert(getClauseNode(MinisatSatSolver::toSatLiteral(lit)));
}

void SatProofManager::registerSatAssumptions(const std::vector<Node>& assumps)
{
  for (const Node& a : assumps)
  {
    Trace("sat-proof") << "SatProofManager::registerSatAssumptions: - " << a
                       << "\n";
    d_assumptions.insert(a);
  }
}

}  // namespace prop
}  // namespace CVC4
