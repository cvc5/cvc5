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

ProofTracer::ProofTracer(const CadicalPropagator& propagator)
    : d_propagator(propagator)
{
  d_antecedents.emplace_back();  // clauses start with id 1
}

void ProofTracer::add_original_clause(uint64_t clause_id,
                                      bool redundant,
                                      const std::vector<int>& clause,
                                      bool restored)
{
  Assert(d_antecedents.size() == clause_id);
  d_antecedents.emplace_back();  // no antecedents
  ClauseType ctype =
      d_propagator.in_search() ? ClauseType::THEORY : ClauseType::INPUT;
  d_orig_clauses.try_emplace(clause_id, clause, ctype);

  if (TraceIsOn("cadical::prooftracer"))
  {
    Trace("cadical::prooftracer")
        << (ctype == ProofTracer::ClauseType::INPUT ? "i: " : "t: ");
    for (const auto lit : clause)
    {
      Trace("cadical::prooftracer") << lit << " ";
    }
    Trace("cadical::prooftracer") << "0" << std::endl;
  }
}

void ProofTracer::add_derived_clause(uint64_t clause_id,
                                     bool redundant,
                                     const std::vector<int>& clause,
                                     const std::vector<uint64_t>& antecedents)
{
  Assert(d_antecedents.size() == clause_id);
  (void)clause;
  (void)redundant;
  // Only store antecedents for a derived clause, no need to store the
  // literals.
  d_antecedents.emplace_back(antecedents);
}

void ProofTracer::add_assumption_clause(
    uint64_t clause_id,
    const std::vector<int>& clause,
    const std::vector<uint64_t>& antecedents)
{
  Assert(d_antecedents.size() == clause_id);
  // Assumption clauses are the negation of the core of failed/unsat
  // assumptions.
  d_antecedents.emplace_back(antecedents);
  // Assumptions are original clauses.
  d_orig_clauses.try_emplace(clause_id, clause, ClauseType::ASSUMPTION);

  if (TraceIsOn("cadical::prooftracer"))
  {
    Trace("cadical::prooftracer") << "a: ~(";
    for (const auto lit : clause)
    {
      Trace("cadical::prooftracer") << lit << " ";
    }
    Trace("cadical::prooftracer") << "0)" << std::endl;
  }
}

void ProofTracer::conclude_unsat(CaDiCaL::ConclusionType type,
                                 const std::vector<uint64_t>& clause_ids)
{
  // Store final clause ids that concluded unsat.
  d_final_clauses = clause_ids;
}

void ProofTracer::compute_unsat_core(std::vector<SatClause>& unsat_core,
                                     bool include_theory_lemmas) const
{
  std::vector<uint64_t> core;
  std::vector<uint64_t> visit{d_final_clauses};
  std::vector<bool> visited(d_antecedents.size() + 1, false);

  // Trace back from final clause ids (empty clause) to original clauses.
  while (!visit.empty())
  {
    const uint64_t clause_id = visit.back();
    visit.pop_back();

    if (!visited[clause_id])
    {
      visited[clause_id] = true;
      if (d_orig_clauses.find(clause_id) != d_orig_clauses.end())
      {
        core.push_back(clause_id);
      }
      Assert(clause_id < d_antecedents.size());
      const auto& antecedents = d_antecedents[clause_id];
      visit.insert(visit.end(), antecedents.begin(), antecedents.end());
    }
  }

  // Get activation literals, required for filtering below.
  std::unordered_set<int64_t> alits;
  for (const auto& lit : d_propagator.activation_literals())
  {
    Trace("cadical::prooftracer")
        << "act. lit: " << lit.getSatVariable() << std::endl;
    alits.insert(lit.getSatVariable());
  }

  Trace("cadical::prooftracer") << "unsat core:" << std::endl;

  // Get the core in terms of SatClause/SatLiteral, filters out activation
  // literals.
  for (const uint64_t cid : core)
  {
    const auto& [clause, ctype] = d_orig_clauses.at(cid);

    // Skip theory lemmas if not requested.
    if (!include_theory_lemmas && ctype == ProofTracer::ClauseType::THEORY)
    {
      continue;
    }

    // Filter out activation literals
    std::vector<int64_t> cl;
    for (const auto& lit : clause)
    {
      if (alits.find(std::abs(lit)) == alits.end())
      {
        cl.push_back(lit);
      }
    }

    if (cl.empty())
    {
      continue;
    }

    if (TraceIsOn("cadical::prooftracer"))
    {
      char ct = ' ';
      switch (ctype)
      {
        case ProofTracer::ClauseType::ASSUMPTION: ct = 'a'; break;
        case ProofTracer::ClauseType::INPUT: ct = 'i'; break;
        case ProofTracer::ClauseType::THEORY: ct = 't'; break;
      }
      Trace("cadical::prooftracer") << ct << ": ";
    }

    // Assumption clauses are the negation of a core of failed/unsat
    // assumptions. Add each assumption as a unit clause.
    if (ctype == ProofTracer::ClauseType::ASSUMPTION)
    {
      for (const auto lit : cl)
      {
        auto& sat_clause = unsat_core.emplace_back();
        sat_clause.emplace_back(toSatLiteral(-lit));
        Trace("cadical::prooftracer") << -lit << " 0" << std::endl;
      }
    }
    else
    {
      auto& sat_clause = unsat_core.emplace_back();
      for (const auto& lit : cl)
      {
        Trace("cadical::prooftracer") << lit << " ";
        sat_clause.emplace_back(toSatLiteral(lit));
      }
      Trace("cadical::prooftracer") << "0" << std::endl;
    }
  }
}

}  // namespace cvc5::internal::prop::cadical
