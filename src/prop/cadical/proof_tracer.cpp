/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * CaDiCaL proof tracer.
 *
 * Implementation of a CaDiCaL proof tracer.
 */

#include "prop/cadical/proof_tracer.h"

#include <unordered_set>

#include "proof/proof_node.h"
#include "prop/cadical/cadical.h"
#include "prop/cadical/cdclt_propagator.h"

namespace cvc5::internal::prop::cadical {

namespace {

Node toNode(NodeManager* nm, TheoryProxy* proxy, const SatClause& clause)
{
  if (clause.empty())
  {
    return nm->mkConst(false);
  }
  std::vector<Node> lits;
  for (const auto& lit : clause)
  {
    lits.push_back(proxy->getNode(lit));
  }
  // Sat clause is sorted by literal id. Ensure that node-level clause is
  // sorted by node ids.
  std::sort(lits.begin(), lits.end());
  return lits.size() == 1 ? lits[0] : nm->mkNode(Kind::OR, lits);
}

}  // namespace

ProofTracer::ProofTracer(const CadicalPropagator& propagator)
    : d_propagator(propagator)
{
  d_clauses.emplace_back();
}

void ProofTracer::add_original_clause(uint64_t clause_id,
                                      bool redundant,
                                      const std::vector<int>& clause,
                                      bool restored)
{
  ClauseType ctype =
      d_propagator.in_search() ? ClauseType::THEORY : ClauseType::INPUT;
  d_clauses.emplace_back(clause_id, ctype, clause);
  Trace("cadical::prooftracer") << d_clauses[clause_id] << std::endl;
}

void ProofTracer::add_derived_clause(uint64_t clause_id,
                                     bool redundant,
                                     const std::vector<int>& clause,
                                     const std::vector<uint64_t>& antecedents)
{
  (void)clause;
  (void)redundant;
  d_clauses.emplace_back(clause_id, ClauseType::DERIVED, clause, antecedents);
  Trace("cadical::prooftracer") << d_clauses[clause_id] << std::endl;
}

void ProofTracer::add_assumption_clause(
    uint64_t clause_id,
    const std::vector<int>& clause,
    const std::vector<uint64_t>& antecedents)
{
  // Assumption clauses are the negation of the core of failed/unsat
  // assumptions.
  d_clauses.emplace_back(
      clause_id, ClauseType::ASSUMPTION, clause, antecedents);
  Trace("cadical::prooftracer") << d_clauses[clause_id] << std::endl;
}

void ProofTracer::conclude_unsat(CaDiCaL::ConclusionType type,
                                 const std::vector<uint64_t>& clause_ids)
{
  // Store final clause ids that concluded unsat.
  d_final_clauses = clause_ids;
}

void ProofTracer::compute_proof_core(std::vector<uint64_t>& core) const
{
  std::vector<uint64_t> visit{d_final_clauses};
  std::unordered_set<uint64_t> visited;

  // Trace back from final clause ids (empty clause) to original clauses.
  while (!visit.empty())
  {
    const uint64_t clause_id = visit.back();
    visit.pop_back();

    if (visited.insert(clause_id).second)
    {
      core.push_back(clause_id);
      const auto& antecedents = d_clauses[clause_id].antecedents;
      visit.insert(visit.end(), antecedents.begin(), antecedents.end());
    }
  }

  std::sort(core.begin(), core.end());

  if (TraceIsOn("cadical::prooftracer"))
  {
    Trace("cadical::prooftracer") << "proof core:" << std::endl;
    for (const auto& cid : core)
    {
      const auto& clause = d_clauses[cid];
      Trace("cadical::prooftracer") << clause << std::endl;
    }
  }
}

std::shared_ptr<ProofNode> ProofTracer::get_chain_resolution_proof(
    ProofNodeManager* pnm, NodeManager* nm, TheoryProxy* proxy)
{
  std::vector<uint64_t> core;
  compute_proof_core(core);

  std::unordered_set<int64_t> alits;
  for (const auto& lit : d_propagator.activation_literals())
  {
    alits.insert(lit.getSatVariable());
  }

  std::unordered_map<uint64_t, std::shared_ptr<ProofNode>> steps;
  for (const uint64_t cid : core)
  {
    const auto& clause = d_clauses[cid];
    if (clause.type == ClauseType::DERIVED)
    {
      Assert(clause.antecedents.size() > 1);
      steps.emplace(cid,
                    chain_resolution_step(cid, proxy, pnm, nm, steps, alits));
    }
    else
    {
      SatClause sat_clause = toSatClause(alits, clause.literals);
      if (clause.type == ClauseType::ASSUMPTION)
      {
        Assert(cid == core.back());
        Assert(sat_clause.empty());
        // Only happens with constraint feature
        Assert(!clause.antecedents.empty());
        steps.emplace(cid, steps.at(core[core.size() - 2]));
      }
      else
      {
        Node assump = toNode(nm, proxy, sat_clause);
        steps.emplace(cid, pnm->mkAssume(assump));
      }
    }
  }
  // Last clause id corresponds to empty clause.
  auto pf = steps.at(core.back());
  return pf;
}

bool ProofTracer::mark_var(std::unordered_map<int32_t, uint8_t>& marked_vars,
                           int32_t lit)
{
  int32_t var = std::abs(lit);
  uint8_t mask = (lit < 0) ? 2 : 1;
  uint8_t marked = marked_vars[var];
  if (!(marked & mask))
  {
    marked_vars[var] |= mask;
  }
  return marked & ~mask;
}

std::shared_ptr<ProofNode> ProofTracer::chain_resolution_step(
    uint64_t cid,
    TheoryProxy* proxy,
    ProofNodeManager* pnm,
    NodeManager* nm,
    const std::unordered_map<uint64_t, std::shared_ptr<ProofNode>>& steps,
    const std::unordered_set<int64_t>& activation_literals)
{
  const auto& cl = d_clauses[cid];
  SatClause expected_cl = toSatClause(activation_literals, cl.literals);
  Node conclusion = toNode(nm, proxy, expected_cl);
  const auto& antecedents = cl.antecedents;
  std::vector<std::shared_ptr<ProofNode>> children;
  std::vector<Node> polarities, literals;
  std::unordered_map<int32_t, uint8_t> marked_vars;
  // Create chain resolution step for each derived clause
  for (size_t i = 0, size = antecedents.size(); i < size; ++i)
  {
    // Antecedants are stored in the order they were resolved. Thus, we have
    // to process them in reverse order, starting from the last id.
    size_t idx = size - i - 1;
    uint64_t aid = antecedents[idx];
    const auto& clause = d_clauses[aid];
    for (int32_t lit : clause.literals)
    {
      if (!mark_var(marked_vars, lit))
      {
        continue;
      }
      // Found pivot literal
      literals.push_back(proxy->getNode(toSatLiteral(lit).getSatVariable()));
      // Polarity of pivot literal in first clause
      polarities.push_back(nm->mkConst(!(lit > 0)));
    }

    auto it = steps.find(aid);
    Assert(it != steps.end());
    children.push_back(it->second);
  }
  std::vector<Node> args{conclusion};
  args.push_back(nm->mkNode(Kind::SEXPR, polarities));
  args.push_back(nm->mkNode(Kind::SEXPR, literals));
  return pnm->mkNode(ProofRule::CHAIN_M_RESOLUTION, children, args);
}

std::ostream& operator<<(std::ostream& os, const ProofTracer::ClauseInfo& ci)
{
  char ct = ' ';
  switch (ci.type)
  {
    case ProofTracer::ClauseType::DERIVED: ct = 'd'; break;
    case ProofTracer::ClauseType::INPUT: ct = 'i'; break;
    case ProofTracer::ClauseType::THEORY: ct = 't'; break;
    case ProofTracer::ClauseType::ASSUMPTION: ct = 'a'; break;
  }

  os << ci.clause_id << " " << ct << ": ( ";
  for (const auto lit : ci.literals)
  {
    os << lit << " ";
  }
  os << ")";
  os << " [ ";
  for (const auto lit : ci.antecedents)
  {
    os << lit << " ";
  }
  os << "] ";
  return os;
}

}  // namespace cvc5::internal::prop::cadical
