/*********************                                                        */
/*! \file new_proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A new manager for Proofs
 **/

#include "proof/new_proof_manager.h"

#include "base/check.h"
#include "expr/proof_node_algorithm.h"
#include "context/context.h"
#include "options/bv_options.h"
#include "options/proof_options.h"
#include "proof/clause_id.h"
#include "proof/proof_utils.h"
#include "proof/resolution_bitvector_proof.h"
#include "proof/sat_proof_implementation.h"
#include "proof/theory_proof.h"
#include "prop/minisat/core/Solver.h"
#include "prop/minisat/minisat.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/rewriter.h"
#include "theory/output_channel.h"
#include "theory/term_registration_visitor.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/valuation.h"
#include "util/hash.h"
#include "util/proof.h"

namespace CVC4 {

NewProofManager::NewProofManager() : d_cdproof(nullptr), d_solver(nullptr) {}

NewProofManager::~NewProofManager() {}

void NewProofManager::setProofNodeManager()
{
  d_cdproof.reset(new CDProof(
      smt::currentSmtEngine()->getTheoryEngine()->getProofNodeManager()));
}

void NewProofManager::setSatSolver(Minisat::Solver* solver)
{
  d_solver = solver;
}

NewProofManager* NewProofManager::currentPM()
{
  return smt::currentNewProofManager();
}

void NewProofManager::addStep(Node expected,
                              PfRule rule,
                              const std::vector<Node>& children,
                              const std::vector<Node>& args)
{
  if (!d_cdproof->addStep(expected, rule, children, args, false))
  {
    Assert(false) << "NewProofManager::couldn't add " << rule
                  << " step with conclusion: " << expected
                  << ", children: " << children << ", args: " << args << "\n";
  }
}

inline void NewProofManager::printLit(const Minisat::Solver::TLit lit)
{
  Debug("newproof::sat") << (Minisat::sign(lit) ? "-" : "")
                         << Minisat::var(lit) + 1 << " ";
}

inline void NewProofManager::printClause(const Minisat::Solver::TClause& clause)
{
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(clause[i]);
    Debug("newproof::sat") << satLit << " ";
    if (Debug.isOn("newproof::sat::cnf"))
    {
      Assert(d_litToNode.find(satLit) != d_litToNode.end());
      Debug("newproof::sat::cnf") << "[" << d_litToNode[satLit] << "] ";
    }
  }
}

Node NewProofManager::factorAndReorder(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  // remove duplicates
  std::set<Node> clauseSet{n.begin(), n.end()};
  std::vector<Node> children{clauseSet.begin(), clauseSet.end()};
  // if factoring changed
  if (children.size() < n.getNumChildren())
  {
    Node factored = children.empty()
                        ? nm->mkConst<bool>(false)
                        : children.size() == 1 ? children[0]
                                               : nm->mkNode(kind::OR, children);
    d_cdproof->addStep(factored, PfRule::FACTORING, {n}, {factored});
    n = factored;
  }
  // remove trivially false literals -- false, (not true)
  // TODO need to find out how intense is the "false elimination" performed by
  // the SAT solver
  // for (unsigned i = 0, size = children.size(); i < size; ++i)
  // {
  //   if children[i].isConst() &&
  // }
  // nothing to order
  if (children.size() < 2)
  {
    return n;
  }
  // order
  std::sort(children.begin(), children.end());
  Node ordered = nm->mkNode(kind::OR, children);
  // if ordering changed
  if (ordered != n)
  {
    d_cdproof->addStep(ordered, PfRule::REORDERING, {n}, {ordered});
  }
  return ordered;
}

void NewProofManager::addLitDef(prop::SatLiteral lit, Node litNode)
{
  Debug("newproof::sat") << "NewProofManager::addLitDef: lit/def: " << lit
                         << " / " << litNode << "\n";
  d_litToNode[lit] = litNode;
  d_nodeToLit[litNode] = lit;
}

void NewProofManager::registerClause(Minisat::Solver::TLit lit)
{
  registerClause(toSatLiteral<Minisat::Solver>(lit));
}

void NewProofManager::registerClause(prop::SatLiteral satLit)
{
  auto it = d_litToClauseId.find(satLit);
  if (it != d_litToClauseId.end())
  {
    if (Debug.isOn("newproof::sat"))
    {
      Debug("newproof::sat")
          << "NewProofManager::registerClause: id " << it->second
          << ", Lit: " << satLit << " already registered\n";
    }
    return;
  }
  ClauseId id = d_nextId++;
  d_litToClauseId[satLit] = id;
  d_clauseIdToLit[id] = satLit;
  Assert(d_litToNode.find(satLit) != d_litToNode.end())
      << "NewProofManager::registerClause: literal " << satLit
      << " should have been defined.\n";
  Node litNode = d_litToNode[satLit];
  d_clauseIdToNode[id] = litNode;
  // register in proof as assumption, which should be filled later, since it's
  // not possible yet to know, in general, how this literal came to be. Some
  // components register facts eagerly, like the theory engine, but other
  // lazily, like CNF stream and internal SAT solver propagation.
  if (!d_cdproof->addStep(litNode, PfRule::ASSUME, {}, {litNode}))
  {
    Assert(false) << "NewProofManager::couldn't add " << PfRule::ASSUME
                  << " step with conclusion: " << litNode << "\n";
  }
  Debug("newproof::sat") << "NewProofManager::registerClause: id " << id
                         << ", Lit: " << satLit << "\n";
}

void NewProofManager::registerClause(Minisat::Solver::TClause& clause)
{
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::registerClause: TClause: ";
    printClause(clause);
    Debug("newproof::sat") << "\n";
  }
  if (clause.proofId() != 0)
  {
    Debug("newproof::sat") << "NewProofManager::registerClause: id "
                           << clause.proofId()
                           << " of clause already registered\n";
    return;
  }
  ClauseId id = d_nextId++;
  clause.setProofId(id);
  // build clauseNode
  std::vector<Node> clauseNodes;
  for (unsigned i = 0, size = clause.size(); i < size; ++i)
  {
    prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(clause[i]);
    Assert(d_litToNode.find(satLit) != d_litToNode.end())
        << "NewProofManager::registerClause: literal " << satLit
        << " not defined yet\n";
    clauseNodes.push_back(d_litToNode[satLit]);
  }
  Node clauseNode = NodeManager::currentNM()->mkNode(kind::OR, clauseNodes);
  // Rewrite clauseNode before proceeding. This is so ordering is consistent
  clauseNode = factorAndReorder(clauseNode);
  d_clauseIdToNode[id] = clauseNode;
  // register in proof as assumption, which should be filled later, since it's
  // not possible yet to know, in general, how this clause came to be. Some
  // components register facts eagerly, like the theory engine, but other
  // lazily, like CNF stream and internal SAT solver propagation.
  if (!d_cdproof->addStep(clauseNode, PfRule::ASSUME, {}, {clauseNode}))
  {
    Assert(false) << "NewProofManager::couldn't add " << PfRule::ASSUME
                  << " step with conclusion: " << clauseNode << "\n";
  }
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::registerClause: id " << id
                           << ", TClause: ";
    printClause(clause);
    Debug("newproof::sat") << ", clauseNode: " << clauseNode << "\n";
  }
}

void NewProofManager::startResChain(Minisat::Solver::TClause& start)
{
  Assert(start.proofId() != 0);
  ClauseId id = start.proofId();
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::startResChain: ";
    printClause(start);
    Debug("newproof::sat") << "\n";
  }
  Assert(d_clauseIdToNode.find(id) != d_clauseIdToNode.end());
  d_resolution.push_back(
      std::pair<Node, Node>(d_clauseIdToNode[id], Node::null()));
}

void NewProofManager::addResolutionStep(Minisat::Solver::TLit lit)
{
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  Assert(d_litToNode.find(satLit) != d_litToNode.end());
  Debug("newproof::sat") << push
                         << "NewProofManager::addResolutionStep: justify lit "
                         << lit << "\n";
  tryJustifyingLit(~satLit);
  d_resolution.push_back(
      std::pair<Node, Node>(d_litToNode[~satLit], d_litToNode[satLit]));
  Debug("newproof::sat") << pop << "NewProofManager::addResolutionStep: ["
                         << satLit << "] " << ~satLit << "\n";
}

void NewProofManager::addResolutionStep(Minisat::Solver::TClause& clause,
                                        Minisat::Solver::TLit lit)
{
  // pivot is given as in the second clause, so we store its negation (which
  // will be removed positivly from the first clause and negatively from the
  // second)
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(~lit);
  Assert(d_litToNode.find(satLit) != d_litToNode.end());
  Assert(d_clauseIdToNode.find(clause.proofId()) != d_clauseIdToNode.end());
  // clause has not been registered yet
  if (clause.proofId() == 0)
  {
    Debug("newproof::sat") << push;
    registerClause(clause);
    Debug("newproof::sat") << pop;
  }
  d_resolution.push_back(std::pair<Node, Node>(
      d_clauseIdToNode[clause.proofId()], d_litToNode[satLit]));
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::addResolutionStep: [" << satLit
                           << "] ";
    printClause(clause);
    Debug("newproof::sat") << "\nNewProofManager::addResolutionStep:\t"
                           << clause.proofId() << " : "
                           << d_clauseIdToNode[clause.proofId()] << "\n";
  }
}

void NewProofManager::endResChain(Minisat::Solver::TLit lit)
{
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  Assert(d_litToClauseId.find(satLit) != d_litToClauseId.end())
      << "literal " << satLit << " not registered yet\n";
  Debug("newproof::sat") << "NewProofManager::endResChain: chain_res for "
                         << d_litToClauseId[satLit] << " : " << satLit;
  endResChain(d_litToClauseId[satLit]);
}

void NewProofManager::endResChain(Minisat::Solver::TClause& clause)
{
  Assert(clause.proofId() != 0);
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::endResChain: chain_res for "
                           << clause.proofId() << ": ";
    printClause(clause);
  }
  endResChain(clause.proofId());
}

// id is the conclusion
void NewProofManager::endResChain(ClauseId id)
{
  Assert(d_clauseIdToNode.find(id) != d_clauseIdToNode.end());
  Node conclusion = d_clauseIdToNode[id];
  Debug("newproof::sat") << ", " << conclusion << "\n";
  std::vector<Node> children, args;
  for (unsigned i = 0, size = d_resolution.size(); i < size; ++i)
  {
    children.push_back(d_resolution[i].first);
    Debug("newproof::sat") << "NewProofManager::endResChain:   ";
    if (i > 0)
    {
      Debug("newproof::sat")
          << "[" << d_nodeToLit[d_resolution[i].second] << "] ";
    }
    // special case for clause being a single literal corresponding itself to a
    // clause, which is indicated by the pivot being of the form (not or ...)
    if (d_resolution[i].first.getKind() == kind::OR
        && !(d_resolution[i].second.getKind() == kind::NOT
             && d_resolution[i].second[0].getKind() == kind::OR))
    {
      for (unsigned j = 0, sizeJ = d_resolution[i].first.getNumChildren();
           j < sizeJ;
           ++j)
      {
        Debug("newproof::sat") << d_nodeToLit[d_resolution[i].first[j]];
        if (j < sizeJ - 1)
        {
          Debug("newproof::sat") << ", ";
        }
      }
    }
    else
    {
      Debug("newproof::sat") << d_nodeToLit[d_resolution[i].first];
    }
    Debug("newproof::sat") << " : ";
    if (i > 0)
    {
      args.push_back(d_resolution[i].second);
      Debug("newproof::sat") << "[" << d_resolution[i].second << "] ";
    }
    Debug("newproof::sat") << d_resolution[i].first << "\n";
  }
  // clearing
  d_resolution.clear();
  // since the conclusion can be both reordered and without duplucates and the
  // SAT solver does not record this information, we must recompute it here so
  // the proper CHAIN_RESOLUTION step can be created
  // compute chain resolution conclusion
  Node chainConclusion = smt::currentSmtEngine()
                             ->getTheoryEngine()
                             ->getProofNodeManager()
                             ->getChecker()
                             ->checkDebug(PfRule::CHAIN_RESOLUTION,
                                          children,
                                          args,
                                          Node::null(),
                                          "newproof::sat");
  // create step
  d_cdproof->addStep(chainConclusion, PfRule::CHAIN_RESOLUTION, children, args);
  if (chainConclusion != conclusion)
  {
    // if this happens that chainConclusion needs to be factored and/or
    // reordered, which in either case can be done only if it's not a unit
    // clause.
    CVC4_UNUSED Node reducedChainConclusion = factorAndReorder(chainConclusion);
    Assert(reducedChainConclusion == conclusion)
        << "given res chain conclusion " << conclusion
        << "\ndifferent from chain_res " << chainConclusion
        << "\n+ reordering + factoring " << reducedChainConclusion;
  }
}

void NewProofManager::tryJustifyingLit(prop::SatLiteral lit)
{
  Debug("newproof::sat") << push
                         << "NewProofManager::tryJustifyingLit: Lit: " << lit
                         << "[" << d_litToNode[lit] << "]\n";
  if (d_litToClauseId.find(lit) == d_litToClauseId.end())
  {
    Debug("newproof::sat") << "NewProofManager::tryJustifyingLit: not "
                              "registered as clause\n"
                           << pop;
    return;
  }
  Minisat::Solver::TCRef reason_ref =
      d_solver->reason(Minisat::var(prop::MinisatSatSolver::toMinisatLit(lit)));
  if (reason_ref == Minisat::Solver::TCRef_Undef)
  {
    Debug("newproof::sat")
        << "NewProofManager::tryJustifyingLit: no SAT reason\n"
        << pop;
    return;
  }
  Assert(reason_ref >= 0 && reason_ref < d_solver->ca.size())
      << "reason_ref " << reason_ref << " and d_solver->ca.size() "
      << d_solver->ca.size() << "\n";
  // Here, the call to resolveUnit() can reallocate memory in the
  // clause allocator.  So reload reason ptr each time.
  const Minisat::Solver::TClause& initial_reason = d_solver->ca[reason_ref];
  unsigned current_reason_size = initial_reason.size();
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::tryJustifyingLit: with clause: ";
    printClause(initial_reason);
    Debug("newproof::sat") << "\n";
  }
  // add the reason clause first
  Assert(initial_reason.proofId() != 0);
  Assert(d_clauseIdToNode.find(initial_reason.proofId())
         != d_clauseIdToNode.end());
  std::vector<Node> children{d_clauseIdToNode[initial_reason.proofId()]}, args;
  Debug("newproof::sat") << push;
  for (unsigned i = 0; i < current_reason_size; ++i)
  {
    const Minisat::Solver::TClause& current_reason = d_solver->ca[reason_ref];
    Assert(current_reason_size == static_cast<unsigned>(current_reason.size()));
    current_reason_size = current_reason.size();
    prop::SatLiteral curr_lit =
        toSatLiteral<Minisat::Solver>(current_reason[i]);
    // ignore the lit we are trying to justify...
    if (curr_lit == lit)
    {
      continue;
    }
    tryJustifyingLit(~curr_lit);
    // save to resolution chain premises / arguments
    Assert(d_litToNode.find(curr_lit) != d_litToNode.end());
    children.push_back(d_litToNode[~curr_lit]);
    args.push_back(d_litToNode[curr_lit]);
  }
  Debug("newproof::sat") << pop;
  // retrieve lit's node definition
  Assert(d_litToNode.find(lit) != d_litToNode.end());
  Node litDef = d_litToNode[lit];
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::tryJustifyingLit: chain_res for "
                           << litDef << " with clauses:\n";
    for (unsigned i = 0, size = children.size(); i < size; ++i)
    {
      Debug("newproof::sat")
          << "NewProofManager::tryJustifyingLit:   " << children[i];
      if (i > 0)
      {
        Debug("newproof::sat") << " [" << args[i - 1] << "]";
      }
      Debug("newproof::sat") << "\n";
    }
  }
  // only build resolution if not cyclic
  d_cdproof->addStep(litDef, PfRule::CHAIN_RESOLUTION, children, args);
  Debug("newproof::sat") << pop;
}

void NewProofManager::finalizeProof(ClauseId conflict_id)
{
  Assert(d_clauseIdToNode.find(conflict_id) != d_clauseIdToNode.end());
  Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
  Node clauseNode = d_clauseIdToNode[conflict_id];
  Debug("newproof::sat") << "NewProofManager::finalizeProof: conflict_id: "
                         << conflict_id << ", clauseNode: " << clauseNode
                         << "\n";
  // nothing to do
  if (clauseNode == falseNode)
  {
    return;
  }
  // retrive clause
  std::vector<prop::SatLiteral> conflict_clause;
  if (clauseNode.getKind() == kind::OR)
  {
    for (const Node& n : clauseNode)
    {
      Assert(d_nodeToLit.find(n) != d_nodeToLit.end());
      conflict_clause.push_back(d_nodeToLit[n]);
    }
  }
  else
  {
    Assert(d_nodeToLit.find(clauseNode) != d_nodeToLit.end());
    conflict_clause.push_back(d_nodeToLit[clauseNode]);
  }
  // since this clause is conflicting, I must be able to resolve away each of
  // its literals l_1...l_n. Each literal ~l_i must be justifiable
  //
  // Either ~l_i is the conclusion of some previous, already built, step or from
  // a subproof to be computed.
  //
  // For each l_i, a resolution step is created with the id of the step allowing
  // the derivation of ~l_i, whose pivot in the conflict_clause will be l_i. All
  // resolution steps will be saved in the given reasons vector.
  Debug("newproof::sat") << push;
  // premises and arguments for final resolution
  std::vector<Node> children{clauseNode}, args;
  for (unsigned i = 0, size = conflict_clause.size(); i < size; ++i)
  {
    Assert(d_litToNode.find(conflict_clause[i]) != d_litToNode.end());
    tryJustifyingLit(~conflict_clause[i]);
    // save to resolution chain premises / arguments
    children.push_back(d_litToNode[~conflict_clause[i]]);
    args.push_back(d_litToNode[conflict_clause[i]]);
  }
  Debug("newproof::sat") << pop;
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::finalizeProof: chain_res for false with clauses:\n";
    for (unsigned i = 0, size = children.size(); i < size; ++i)
    {
      Debug("newproof::sat")
          << "NewProofManager::finalizeProof:   " << children[i];
      if (i > 0)
      {
        Debug("newproof::sat") << " [" << args[i - 1] << "]";
      }
      Debug("newproof::sat") << "\n";
    }
  }
  // only build resolution if not cyclic
  d_cdproof->addStep(falseNode,
                     PfRule::CHAIN_RESOLUTION,
                     children,
                     args);
}

// case in which I addded a false unit clause
void NewProofManager::finalizeProof(Minisat::Solver::TLit lit)
{
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  Debug("newproof::sat")
      << "NewProofManager::finalizeProof: conflicting satLit: " << satLit
      << "\n";
  Assert(d_litToClauseId.find(satLit) != d_litToClauseId.end());
  finalizeProof(d_litToClauseId[satLit]);
}

void NewProofManager::printInternalProof()
{
  Trace("newproof-debug")
      << "NewProofManager::printInternalProof: Clauses and their proofs:\n";
  std::vector<Node> assumptions;
  for (const std::pair<ClauseId, Node>& p : d_clauseIdToNode)
  {
    std::stringstream out;
    // make this guy search for a proof module factoring and reordering
    ProofNode* pn = d_cdproof->getProofFor(p.second).get();
    pn->printDebug(out);
    Trace("newproof-debug") << "Proof of " << p.second << ":\n\t" << out.str()
                      << "\n";
    expr::getFreeAssumptions(pn, assumptions);
  }
  Trace("newproof-debug")
      << "NewProofManager::printInternalProof: all free assumptions:\n";
  LazyCDProof* teProof =
      smt::currentSmtEngine()->getTheoryEngine()->getLazyProof();
  for (unsigned i = 0, size = assumptions.size(); i < size; ++i)
  {
    Trace("newproof-debug") << "NewProofManager::printInternalProof:\t "
                      << assumptions[i] << "\n";
    std::shared_ptr<ProofNode> pn = teProof->getProofFor(assumptions[i]);
    std::stringstream out;
    pn->printDebug(out);
    Trace("newproof-debug") << "NewProofManager::printInternalProof:\t " << out.str()
                      << "\n";
    // update this proof in case the theory engine had anything better than
    // "assume"
    d_cdproof->addProof(pn);
  }
  Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
  Trace("newproof") << "NewProofManager::printInternalProof: proof node of "
                    << falseNode << ":\n";
  // Assert(d_cdproof->hasStep(falseNode))
  //     << "UNSAT but no proof step for " << falseNode << "\n";
  std::stringstream out;
  std::shared_ptr<ProofNode> pf = d_cdproof->getProofFor(falseNode);
  pf->printDebug(out);
  assumptions.clear();
  expr::getFreeAssumptions(pf.get(), assumptions);
  Trace("newproof") << out.str() << "\nAssumptions: " << assumptions.size()
                    << "\n"
                    << push;
  for (unsigned i = 0, size = assumptions.size(); i < size; ++i)
  {
    Trace("newproof") << "- " << assumptions[i] << "\n";
  }
  Trace("newproof") << pop;
}

}  // namespace CVC4
