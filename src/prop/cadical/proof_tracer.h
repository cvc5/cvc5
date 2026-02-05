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
 * Proof tracer implementation for tracing CaDiCaL LRUP proofs.
 *
 * This tracer keeps track of the original clauses sent to CaDiCaL (input
 * clauses and theory lemmas) as well as derived clauses and their the
 * antecedents. All input clauses added during solving are considered theory
 * lemmas.
 *
 * When the empty clause (ProofTracer::conclude_unsat) is derived we store
 * the final clause ids that were used to derive the empty clause in
 * d_final_clauses. The input clauses that are reachable from the
 * final clause ids through the stored antecedents correspond to the unsat core.
 */

class ProofTracer : public CaDiCaL::Tracer
{
 public:
  enum class ClauseType : uint8_t
  {
    ASSUMPTION,  // assumption clause
    INPUT,       // input clause
    THEORY,      // theory lemma
    DERIVED,     // derived clause
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

  /**
   * Backwards traversal of clausal proof starting from the empty clause.
   * @param core Proof core containing visited clause ids.
   */
  void compute_proof_core(std::vector<uint64_t>& core) const;

  /**
   * Generates the chain resolution proof from CaDiCaL's LRUP proof.
   */
  std::shared_ptr<ProofNode> get_chain_resolution_proof(ProofNodeManager* pnm,
                                                        NodeManager* nm,
                                                        TheoryProxy* proxy);

 private:
  /**
   * Helper to find pivot literals.
   * @param marked_vars Cache of already marked variables.
   * @param lit Current literal to mark.
   * @return Whether other polarity of given literal has been already marked.
   */
  bool mark_var(std::unordered_map<int32_t, uint8_t>& marked_vars, int32_t lit);

  /**
   * Helper to produce chain resolution proof step for a derived clause.
   *
   * Produces a chain resolution proof step for the given derived clause cid.
   * From the extracted SAT proof core we get that a clause C was derived by
   * resolving antecedents A0,...,An. For each resolution step we compute the
   * pivot literal and its polarity, starting by resolving An and An-1
   * (backwards resolution). The children of this chain resolution step are the
   * proof steps of each antecedent, i.e., steps[A0],...,steps[An]. The
   * arguments are the pivot literals and their polarities and the derived
   * clause C as a node.
   *
   *              steps[A0],...,steps[An] | C,(polarities...),(pivots...)
   * CHAIN_M_RES --------------------------------------------------------
   *                                      C
   *
   * @param cid Clause id of derived clause to produce proof step for.
   * @param proxy Theory proxy to get node mapping.
   * @param pnm Proof node manager instance.
   * @param nm Node manager instance.
   * @param steps Maps derived clauses to chain resolution proof step that
   *              derived that clause.
   * @param activation_literals Set of current activation literals.
   * @return A chain resolution step for producing clause cid.
   */
  std::shared_ptr<ProofNode> chain_resolution_step(
      uint64_t cid,
      TheoryProxy* proxy,
      ProofNodeManager* pnm,
      NodeManager* nm,
      const std::unordered_map<uint64_t, std::shared_ptr<ProofNode>>& steps,
      const std::unordered_set<int64_t>& activation_literals);

  const CadicalPropagator& d_propagator;
  /** Maps clause ids to clause info. */
  std::vector<ClauseInfo> d_clauses;
  /** Stores the final clause ids used to conclude unsat. */
  std::vector<uint64_t> d_final_clauses;
};

}  // namespace cvc5::internal::prop::cadical

#endif
