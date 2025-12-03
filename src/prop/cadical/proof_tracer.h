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

#ifndef CVC5__PROP__CADICAL__PROOF_TRACER_H
#define CVC5__PROP__CADICAL__PROOF_TRACER_H

#include <cadical/tracer.hpp>
#include <cstdint>
#include <vector>

#include "proof/proof_node.h"
#include "prop/sat_solver_types.h"
#include "prop/theory_proxy.h"

namespace cvc5::internal::prop::cadical {

class CadicalPropagator;

/**
 * Proof tracer implementation for computing unsat cores from CaDiCaL.
 *
 * This tracer keeps track of the original clauses sent to CaDiCaL (input
 * clauses and theory lemmas) as well as the antecedents of each derived clause.
 * Derived clauses are not stored since they are not needed for unsat cores.
 *
 * When the empty clause (ProofTracer::conclude_unsat) is derived we store
 * the final clause ids that were used to derive the empty clause in
 * d_final_clauses. The original clauses that are reachable from the
 * final clause ids through the stored antecedents correspond to the unsat core,
 * which is computed in ProofTracer::compute_unsat_core.
 */

class ProofTracer : public CaDiCaL::Tracer
{
 public:
  enum class ClauseType
  {
    ASSUMPTION,  // assumption clause
    INPUT,       // input clause
    THEORY,      // theory lemmas
  };

  struct ClauseInfo
  {
    ClauseInfo() = default;
    ClauseInfo(uint64_t id,
               ClauseType ctype,
               const std::vector<int32_t>& lits,
               const std::vector<uint64_t>& ants = {})
        : clause_id(id), type(ctype), literals(lits), antecedents(ants)
    {
    }

    uint64_t clause_id;
    ClauseType type;
    std::vector<int32_t> literals;
    std::vector<uint64_t> antecedents;
  };

  ProofTracer(const CadicalPropagator& propagator);

  void add_original_clause(uint64_t clause_id,
                           bool redundant,
                           const std::vector<int>& clause,
                           bool restored) override;

  void add_derived_clause(uint64_t clause_id,
                          bool redundant,
                          const std::vector<int>& clause,
                          const std::vector<uint64_t>& antecedents) override;

  void add_assumption_clause(uint64_t clause_id,
                             const std::vector<int>& clause,
                             const std::vector<uint64_t>& antecedents) override;

  void conclude_unsat(CaDiCaL::ConclusionType type,
                      const std::vector<uint64_t>& clause_ids) override;

  void compute_unsat_core(std::vector<SatClause>& unsat_core,
                          bool include_theory_lemmas = true) const;

 private:
  const CadicalPropagator& d_propagator;
  // Maps clause id to its antecedents.
  std::vector<std::vector<uint64_t>> d_antecedents;
  // Maps original clause ids to their literals and clause type.
  std::unordered_map<uint64_t, std::pair<std::vector<int>, ClauseType>>
      d_orig_clauses;
  // Stores the final clause ids used to conclude unsat.
  std::vector<uint64_t> d_final_clauses;
};

}  // namespace cvc5::internal::prop::cadical

#endif
