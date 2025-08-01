/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Lydia Kondylidou
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model-based quantifier instantiation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_MBQI_H
#define CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_MBQI_H

#include <map>
#include <unordered_map>
#include <unordered_set>

#include "context/cdhashset.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
    
class SolverEngine;

namespace theory {
namespace quantifiers {

class MbqiEnum;

/**
 * InstStrategyMbqi
 *
 * A basic implementation of Ge/de Moura CAV 2009. This class can be used to
 * check whether the current model satisfies quantified formulas using
 * subsolvers. The negation of the quantified formula is added as an assertion,
 * along with embeddings of the models of uninterpreted sorts. If the query
 * to the subsolver is unsat, then the quantified formula is satisfied.
 * Otherwise, the model from the subsolver is used to construct an
 * instantiation.
 */
class InstStrategyMbqi : public QuantifiersModule
{
  friend class MbqiEnum;
 public:
  InstStrategyMbqi(Env& env,
                   QuantifiersState& qs,
                   QuantifiersInferenceManager& qim,
                   QuantifiersRegistry& qr,
                   TermRegistry& tr);
  ~InstStrategyMbqi() {}
  /** reset round */
  void reset_round(Theory::Effort e) override;
  /** needs check */
  bool needsCheck(Theory::Effort e) override;
  /** needs model */
  QEffort needsModel(Theory::Effort e) override;
  /** check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Check was complete for quantified formula q */
  bool checkCompleteFor(Node q) override;
  /** For collecting global terms from all available assertions. */
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;
  /** Get the symbols appearing in assertions */
  const context::CDHashSet<Node>& getGlobalSyms() const;
  /** identify */
  std::string identify() const override { return "mbqi"; }

 private:
  /**
   * Process quantified formula q, which may add q to d_quantChecked, add an
   * instantiation for q, or do nothing if something went wrong (e.g. if the
   * query to the subsolver could not be constructed).
   */
  void process(Node q);
  /**
   * Convert to query.
   *
   * This converts term t that is the body of a quantified
   * formula into a term that can be sent to the subsolver. Its free constants
   * are replaced by their model values. The map freshVarType maintains fresh
   * variables that were introduced corresponding to values of uninterpreted
   * sort constants.
   *
   * cmap caches the results of the conversion.
   */
  Node convertToQuery(
      Node t,
      std::unordered_map<Node, Node>& cmap,
      std::map<TypeNode, std::unordered_set<Node> >& freshVarType);
  /**
   * Convert from model
   *
   * This converts a term t that was returned as a model
   * value by a subsolver. We use the mapping mvToFreshVar to convert
   * uninterpreted constants to the fresh variables that were used for
   * that value in the model from the subsolver.
   *
   * cmap caches the results of the conversion.
   */
  Node convertFromModel(Node t,
                        std::unordered_map<Node, Node>& cmap,
                        const std::map<Node, Node>& mvToFreshVar);
  /**
   * Make skolem for term. We use a separate skolem identifier MBQI_INPUT
   * to refer to the variables of a quantified formula. While purification
   * skolems could also suffice, this avoids further complications due to
   * purification skolems for Boolean variables being treated as UF atoms,
   * which can lead to logic exceptions in subsolvers.
   */
  Node mkMbqiSkolem(const Node& t);
  /**
   * Try instantiation. This attempts to add the instantiation mvs for q,
   * where mvs may require post-processing, e.g. to map from uninterpreted
   * sort values to canonical skolems.
   *
   * @param q The quantified formula.
   * @param mvs The vector of terms to instantiate with.
   * @param id The identifier (for stats, debugging).
   * @param mvToFreshVar Maps from uninterpreted sort values to the skolems
   * we should replace them with.
   * @return true if we successfully converted mvs to a legal instantiation
   * and successfully added it to the inference manager of this class.
   */
  bool tryInstantiation(const Node& q,
                        const std::vector<Node>& mvs,
                        InferenceId id,
                        const std::map<Node, Node>& mvToFreshVar);
  /** The quantified formulas that we succeeded in checking */
  std::unordered_set<Node> d_quantChecked;
  /** Kinds that cannot appear in queries */
  std::unordered_set<Kind, kind::KindHashFunction> d_nonClosedKinds;
  /** Submodule for sygus enum */
  std::unique_ptr<MbqiEnum> d_msenum;
  /** The options for subsolver calls */
  Options d_subOptions;
  /* Set of global ground terms in assertions (outside of quantifiers). */
  context::CDHashSet<Node> d_globalSyms;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_MBQI_H */
