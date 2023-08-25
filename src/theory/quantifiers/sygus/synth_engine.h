/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The quantifiers module for managing all approaches to synthesis,
 * in particular, those described in Reynolds et al CAV 2015.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYNTH_ENGINE_H
#define CVC5__THEORY__QUANTIFIERS__SYNTH_ENGINE_H

#include "context/cdhashmap.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/sygus/sygus_qe_preproc.h"
#include "theory/quantifiers/sygus/sygus_stats.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class SynthEngine : public QuantifiersModule
{
  typedef context::CDHashMap<Node, bool> NodeBoolMap;

 public:
  SynthEngine(Env& env,
              QuantifiersState& qs,
              QuantifiersInferenceManager& qim,
              QuantifiersRegistry& qr,
              TermRegistry& tr);
  ~SynthEngine();
  /** presolve
   *
   * Called at the beginning of each call to solve a synthesis problem, which
   * may be e.g. a check-synth or get-abduct call.
   */
  void presolve() override;
  /** needs check, return true if e is last call */
  bool needsCheck(Theory::Effort e) override;
  /** always needs model at effort QEFFORT_MODEL */
  QEffort needsModel(Theory::Effort e) override;
  /* Call during quantifier engine's check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** check ownership */
  void checkOwnership(Node q) override;
  /* Called for new quantifiers */
  void registerQuantifier(Node q) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override;
  /** get synth solutions
   *
   * This function adds entries to sol_map that map functions-to-synthesize
   * with their solutions, for all active conjectures (currently just the one
   * assigned to d_conj). This should be called immediately after the solver
   * answers unsat for sygus input.
   *
   * For details on what is added to sol_map, see
   * SynthConjecture::getSynthSolutions.
   */
  bool getSynthSolutions(std::map<Node, std::map<Node, Node> >& sol_map);
  /** preprocess notify assertion (before rewrite)
   *
   * The purpose of this method is to inform the solution reconstruction
   * techniques within the single invocation module that n is an original
   * assertion. This is used as a heuristic to remember terms that are likely
   * to help when trying to reconstruct a solution that fits a given input
   * syntax.
   */
  void ppNotifyAssertion(Node n);

 private:
  /** The synthesis conjectures that this class is managing. */
  std::vector<std::unique_ptr<SynthConjecture> > d_conjs;
  /**
   * The first conjecture in the above vector. We track this conjecture
   * so that a synthesis conjecture can be preregistered during a call to
   * preregisterAssertion.
   */
  SynthConjecture* d_conj;
  /** The statistics */
  SygusStatistics d_statistics;
  /** assign quantified formula q as a conjecture
   *
   * This method either assigns q to a synthesis conjecture object in d_conjs,
   * or otherwise reduces q to an equivalent form. This method does the latter
   * if this class determines that it would rather rewrite q to an equivalent
   * form r (in which case this method returns the lemma q <=> r). An example of
   * this is the quantifier elimination step option::sygusQePreproc().
   */
  void assignConjecture(Node q);
  /** check conjecture
   *
   * This method returns true if the conjecture is finished processing solutions
   * for this call to SynthEngine::check().
   */
  bool checkConjecture(SynthConjecture* conj);
}; /* class SynthEngine */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
