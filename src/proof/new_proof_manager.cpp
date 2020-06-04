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
#include "context/context.h"
#include "options/bv_options.h"
#include "options/proof_options.h"
#include "proof/clause_id.h"
#include "proof/proof_utils.h"
#include "proof/resolution_bitvector_proof.h"
#include "proof/sat_proof_implementation.h"
#include "proof/theory_proof.h"
#include "prop/minisat/core/Solver.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arrays/theory_arrays.h"
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
  if (n.getKind() != kind::OR)
  {
    return n;
  }
  NodeManager* nm = NodeManager::currentNM();
  // remove duplicates
  std::unordered_set<Node, NodeHashFunction> clauseSet;
  clauseSet.insert(n.begin(), n.end());
  std::vector<Node> children{clauseSet.begin(), clauseSet.end()};
  // if factoring changed
  if (children.size() < n.getNumChildren())
  {
    Node factored = children.empty()
                             ? nm->mkConst<bool>(false)
                             : children.size() == 1
                                   ? children[0]
                                   : nm->mkNode(kind::OR, children);
    d_cdproof->addStep(factored, PfRule::FACTORING, {n}, {factored});
    n = factored;
    // nothing to order
    if (children.size() < 2)
    {
      return factored;
    }
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

void NewProofManager::registerClause(Minisat::Solver::TLit lit)
{
  registerClause(toSatLiteral<Minisat::Solver>(lit));
}

void NewProofManager::addLitDef(prop::SatLiteral lit, Node litNode)
{
  Debug("newproof::sat") << "NewProofManager::addLitDef: lit/def: " << lit
                         << " / " << litNode << "\n";
  d_litToNode[lit] = litNode;
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
    Assert(d_clauseIdToClause.find(clause.proofId())
           != d_clauseIdToClause.end());
    Debug("newproof::sat") << "NewProofManager::registerClause: id "
                           << clause.proofId()
                           << " of clause already registered\n";
    return;
  }
  ClauseId id = d_nextId++;
  clause.setProofId(id);
  d_clauseIdToClause[id] = &clause;
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
    Debug("newproof::sat") << "NewProofManager::startResChain: " << id << ": ";
    printClause(start);
    Debug("newproof::sat") << "\n";
  }
  d_resolution.push_back(Resolution(id));
}

void NewProofManager::addResolutionStep(Minisat::Solver::TLit lit)
{
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  Assert(d_litToNode.find(satLit) != d_litToNode.end());
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::addResolutionStep: justify lit "
                           << lit << "\n";
  }
  Debug("newproof::sat") << push;
  ClauseId id = justifyLit(~lit);
  bool sign = !Minisat::sign(~lit);
  d_resolution.push_back(
      Resolution(id, d_litToNode[satLit], sign));
  Debug("newproof::sat") << pop;
  Debug("newproof::sat") << "NewProofManager::addResolutionStep: " << id << ": "
                         << toSatLiteral<Minisat::Solver>(~lit) << "["
                         << d_litToNode[satLit] << "], sign: " << sign << "\n";
}

void NewProofManager::addResolutionStep(Minisat::Solver::TClause& clause,
                                        Minisat::Solver::TLit lit,
                                        bool sign)
{
  Assert(clause.proofId() != 0);
  ClauseId id = clause.proofId();
  // pivot is given as in the second clause, so we store its negation (which
  // will be removed positivly from the first clause and negatively from the
  // second)
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(~lit);
  Assert(d_litToNode.find(satLit) != d_litToNode.end());
  if (Debug.isOn("newproof::sat"))
  {
    Debug("newproof::sat") << "NewProofManager::addResolutionStep: " << id << ": ";
    printClause(clause);
    Debug("newproof::sat") << "[" << d_litToNode[satLit] << "], sign: " << sign
                           << "\n";
  }
  d_resolution.push_back(
      Resolution(clause.proofId(), d_litToNode[satLit], sign));
}

void NewProofManager::endResChain(Minisat::Solver::TLit lit)
{
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  Assert(d_litToClauseId.find(satLit) != d_litToClauseId.end())
      << "literal " << satLit << " not registered yet\n";
  Debug("newproof::sat") << "NewProofManager::endResChain: chain_res for "
                         << d_litToClauseId[satLit] << ": " << satLit;
  endResChain(d_litToClauseId[satLit]);
}

void NewProofManager::endResChain(Minisat::Solver::TClause& clause)
{
  Assert(clause.proofId() != 0);
  if (Debug.isOn("newproof::sat"))
  {
    Assert(d_clauseIdToClause.find(clause.proofId()) != d_clauseIdToClause.end());
    Debug("newproof::sat") << "NewProofManager::endResChain: chain_res for "
                           << clause.proofId() << ": ";
    printClause(*d_clauseIdToClause[clause.proofId()]);
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
    children.push_back(d_clauseIdToNode[d_resolution[i].d_id]);
    Debug("newproof::sat") << "NewProofManager::endResChain:   "
                           << children.back();
    if (i > 0)
    {
      args.push_back(d_resolution[i].d_piv);
      Debug("newproof::sat") << " [" << args.back() << "]";
    }
    Debug("newproof::sat") << "\n";
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
    CVC4_UNUSED Node reducedChainConclusion = factorAndReorder(chainConclusion);
    Assert(reducedChainConclusion == conclusion)
        << "given res chain conclusion " << conclusion
        << " different from chain_res + reordering + factoring "
        << reducedChainConclusion;
  }
}

ClauseId NewProofManager::justifyLit(Minisat::Solver::TLit lit)
{
  ClauseId id;
  prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(lit);
  Debug("newproof::sat") << "NewProofManager::justifyLit: Lit: " << satLit
                         << "[" << d_litToNode[satLit] << "]\n";
  // see if already computed
  if (d_litToClauseId.find(satLit) != d_litToClauseId.end())
  {
    id = d_litToClauseId[satLit];
    Debug("newproof::sat") << "NewProofManager::justifyLit: already has id "
                           << id << "\n";
    return id;
  }
  // register literal
  registerClause(satLit);
  Assert(d_litToClauseId.find(satLit) != d_litToClauseId.end());
  id = d_litToClauseId[satLit];
  Debug("newproof::sat")
      << "NewProofManager::justifyLit: computing justification...\n";
  Minisat::Solver::TCRef reason_ref = d_solver->reason(Minisat::var(lit));
  if (reason_ref == Minisat::Solver::TCRef_Undef)
  {
    Debug("newproof::sat") << "NewProofManager::justifyLit: no justification\n";
    return id;
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
    Debug("newproof::sat") << "NewProofManager::justifyLit: with clause: ";
    printClause(initial_reason);
    Debug("newproof::sat") << "\n";
  }
  std::vector<Resolution> reasons;
  // add the reason clause first
  Assert(initial_reason.proofId() != 0);
  reasons.push_back(Resolution(initial_reason.proofId()));
  Debug("newproof::sat") << push;
  for (unsigned i = 0; i < current_reason_size; ++i)
  {
    const Minisat::Solver::TClause& current_reason = d_solver->ca[reason_ref];
    Assert(current_reason_size == static_cast<unsigned>(current_reason.size()));
    current_reason_size = current_reason.size();
    Minisat::Solver::TLit curr_lit = current_reason[i];
    // ignore the lit we are trying to justify...
    if (curr_lit == lit)
    {
      continue;
    }
    prop::SatLiteral curr_satLit = toSatLiteral<Minisat::Solver>(curr_lit);
    Assert(d_litToNode.find(curr_satLit) != d_litToNode.end());
    Resolution res(justifyLit(~curr_lit),
                   d_litToNode[curr_satLit],
                   Minisat::sign(curr_lit) ? 0 : 1);
    reasons.push_back(res);
  }
  Debug("newproof::sat") << pop;
  // retrieve lit's node definition
  Assert(d_litToNode.find(satLit) != d_litToNode.end());
  Node litDef = d_litToNode[satLit];
  Debug("newproof::sat") << "NewProofManager::justifyLit: chain_res for "
                         << litDef << " with clauses:\n";
  std::vector<Node> children, args;
  for (unsigned i = 0, size = reasons.size(); i < size; ++i)
  {
    children.push_back(d_clauseIdToNode[reasons[i].d_id]);
    Debug("newproof::sat") << "NewProofManager::justifyLit:   "
                           << children.back();
    if (i > 0)
    {
      args.push_back(reasons[i].d_piv);
      Debug("newproof::sat") << " [" << args.back() << "]";
    }
    Debug("newproof::sat") << "\n";
  }
  d_cdproof->addStep(litDef, PfRule::CHAIN_RESOLUTION, children, args);
  return id;
}

void NewProofManager::finalizeProof(ClauseId conflict_id)
{
  std::vector<Resolution> reasons;
  reasons.push_back(Resolution(conflict_id));
  // retrive clause
  std::vector<Minisat::Solver::TLit> conflict_clause;
  auto it = d_clauseIdToClause.find(conflict_id);
  if (it != d_clauseIdToClause.end())
  {
    for (unsigned i = 0, size = it->second->size(); i < size; ++i)
    {
      conflict_clause.push_back((*it->second)[i]);
    }
  }
  else
  {
    Assert(d_clauseIdToLit.find(conflict_id) != d_clauseIdToLit.end());
    conflict_clause.push_back(
        prop::MinisatSatSolver::toMinisatLit(d_clauseIdToLit[conflict_id]));
  }
  Debug("newproof::sat") << "NewProofManager::finalizeProof: conflict_id: "
                         << conflict_id << "\n";
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
  for (unsigned i = 0, size = conflict_clause.size(); i < size; ++i)
  {
    prop::SatLiteral satLit = toSatLiteral<Minisat::Solver>(conflict_clause[i]);
    Assert(d_litToNode.find(satLit) != d_litToNode.end());
    Resolution res(justifyLit(~conflict_clause[i]),
                   d_litToNode[satLit],
                   Minisat::sign(conflict_clause[i]) ? 0 : 1);
    reasons.push_back(res);
  }
  Debug("newproof::sat") << pop;
  Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
  std::vector<Node> children, args;
  Debug("newproof::sat") << "NewProofManager::finalizeProof: chain_res for "
                         << falseNode << " with clauses:\n";
  bool hasFalsePremise = false;
  for (unsigned i = 0, size = reasons.size(); i < size; ++i)
  {
    Assert(d_clauseIdToNode.find(reasons[i].d_id) != d_clauseIdToNode.end());
    children.push_back(d_clauseIdToNode[reasons[i].d_id]);
    if (children.back() == falseNode)
    {
      hasFalsePremise = true;
      break;
    }
    Debug("newproof::sat") << "NewProofManager::finalizeProof:   "
                           << children.back();
    if (i > 0)
    {
      args.push_back(reasons[i].d_piv);
      Debug("newproof::sat") << " [" << args.back() << "]";
    }
    Debug("newproof::sat") << "\n";
  }
  // only build resolution if the flase conclusion is not already in the
  // premises
  if (!hasFalsePremise)
  {
    d_cdproof->addStep(falseNode, PfRule::CHAIN_RESOLUTION, children, args);
  }
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

void NewProofManager::finalizeProof()
{
  // last added clause is the conflicting one
  finalizeProof(d_nextId - 1);
}

void NewProofManager::printInternalProof()
{
  Trace("newproof")
      << "NewProofManager::printInternalProof: Clauses and their proofs:\n";
  std::vector<Node> assumptions;
  for (const std::pair<ClauseId, Node>& p : d_clauseIdToNode)
  {
    std::stringstream out;
    // make this guy search for a proof module factoring and reordering
    ProofNode* pn = d_cdproof->mkProof(p.second).get();
    pn->printDebug(out);
    Trace("newproof") << "Proof of " << p.second << ":\n\t" << out.str()
                      << "\n";
    pn->getFreeAssumptions(assumptions);
  }
  Trace("newproof")
      << "NewProofManager::printInternalProof: all free assumptions:\n";
  LazyCDProof* teProof =
      smt::currentSmtEngine()->getTheoryEngine()->getLazyProof();
  for (unsigned i = 0, size = assumptions.size(); i < size; ++i)
  {
    Trace("newproof") << "NewProofManager::printInternalProof:\t "
                      << assumptions[i] << "\n";
    std::shared_ptr<ProofNode> pn = teProof->mkProof(assumptions[i]);
    std::stringstream out;
    pn->printDebug(out);
    Trace("newproof") << "NewProofManager::printInternalProof:\t " << out.str()
                      << "\n";
    // update this proof in case the theory engine had anything better than
    // "assume"
    d_cdproof->addProof(pn);
  }
  Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
  Trace("newproof") << "NewProofManager::printInternalProof: proof node of "
                    << falseNode << ":\n";
  Assert(d_cdproof->hasStep(falseNode))
      << "UNSAT but no proof step for " << falseNode << "\n";
  std::stringstream out;
  d_cdproof->mkProof(falseNode)->printDebug(out);
  Trace("newproof") << out.str() << "\n";
}

}  // namespace CVC4
