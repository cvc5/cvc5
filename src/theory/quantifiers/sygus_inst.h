/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SyGuS instantiator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_INST_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_INST_H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashset.h"
#include "smt/env_obj.h"
#include "theory/decision_strategy.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

/**
 * SyGuS quantifier instantion module.
 *
 * This module uses SyGuS techniques to find terms for instantiation and
 * combines it with counterexample guided instantiation. It uses the datatypes
 * solver to find instantiation for each variable based on a specified SyGuS
 * grammar.
 *
 * The CE lemma generated for a quantified formula
 *
 *   \forall x . P[x]
 *
 * is
 *
 *   ce_lit => ~P[DT_SYGUS_EVAL(dt_x)]
 *
 * where ce_lit is a the counterexample literal for the quantified formula and
 * dt_x is a fresh datatype variable with the SyGuS grammar for x as type.
 *
 * While checking, for active quantifiers, we add (full) evaluation unfolding
 * lemmas as follows (see Reynolds at al. CAV 2019b for more information):
 *
 *   explain(dt_x=dt_x^M) => DT_SYGUS_EVAL(dt_x) = t
 *
 * where t = sygusToBuiltin(dt_x^M).
 *
 * We collect the t_i for each bound variable x_i and use them to instantiate
 * the quantified formula.
 */
class SygusInst : public QuantifiersModule
{
 public:
  SygusInst(Env& env,
            QuantifiersState& qs,
            QuantifiersInferenceManager& qim,
            QuantifiersRegistry& qr,
            TermRegistry& tr);
  ~SygusInst() = default;

  bool needsCheck(Theory::Effort e) override;

  QEffort needsModel(Theory::Effort e) override;

  void reset_round(Theory::Effort e) override;

  void check(Theory::Effort e, QEffort quant_e) override;

  bool checkCompleteFor(Node q) override;

  /* Called once for every quantifier 'q' globally (not dependent on context).
   */
  void registerQuantifier(Node q) override;

  /* Called once for every quantifier 'q' per context. */
  void preRegisterQuantifier(Node q) override;

  /* For collecting global terms from all available assertions. */
  void ppNotifyAssertions(const std::vector<Node>& assertions);

  std::string identify() const override { return "SygusInst"; }

 private:
  /* Lookup counterexample literal or create a new one for quantifier 'q'. */
  Node getCeLiteral(Node q);

  /* Generate counterexample lemma for quantifier 'q'. This is done once per
   * quantifier on registerQuantifier() calls. */
  void registerCeLemma(Node q, std::vector<TypeNode>& dtypes);

  /* Add counterexample lemma for quantifier 'q'. This is done on every
   * preRegisterQuantifier() call.*/
  void addCeLemma(Node q);

  /* Send evaluation unfolding lemmas and cache them.
   * Returns true if a new lemma (not cached) was added, and false otherwise.
   */
  bool sendEvalUnfoldLemmas(const std::vector<Node>& lemmas);

  /** Return true if this module should process quantified formula q */
  bool shouldProcess(Node q);

  /* Maps quantifiers to a vector of instantiation constants. */
  std::unordered_map<Node, std::vector<Node>> d_inst_constants;

  /* Maps quantifiers to a vector of DT_SYGUS_EVAL terms. */
  std::unordered_map<Node, std::vector<Node>> d_var_eval;

  /* Maps quantified formulas to registered counterexample literals. */
  std::unordered_map<Node, Node> d_ce_lits;

  /* Decision strategies registered for quantified formulas. */
  std::unordered_map<Node, std::unique_ptr<DecisionStrategy>> d_dstrat;

  /* Currently active quantifiers. */
  std::unordered_set<Node> d_active_quant;

  /* Currently inactive quantifiers. */
  std::unordered_set<Node> d_inactive_quant;

  /* Registered counterexample lemma cache. */
  std::unordered_map<Node, Node> d_ce_lemmas;

  /* Indicates whether a counterexample lemma was added for a quantified
   * formula in the current context. */
  context::CDHashSet<Node> d_ce_lemma_added;

  /* Set of global ground terms in assertions (outside of quantifiers). */
  context::CDHashMap<TypeNode, std::unordered_set<Node>> d_global_terms;

  /* Assertions sent by ppNotifyAssertions. */
  context::CDHashSet<Node> d_notified_assertions;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
