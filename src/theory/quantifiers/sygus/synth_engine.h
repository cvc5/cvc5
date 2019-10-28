/*********************                                                        */
/*! \file synth_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The quantifiers module for managing all approaches to synthesis,
 ** in particular, those described in Reynolds et al CAV 2015.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYNTH_ENGINE_H
#define CVC4__THEORY__QUANTIFIERS__SYNTH_ENGINE_H

#include "context/cdhashmap.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SynthEngine : public QuantifiersModule
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;

 private:
  /** the conjecture formula(s) we are waiting to assign */
  std::vector<Node> d_waiting_conj;
  /** The synthesis conjectures that this class is managing. */
  std::vector<std::unique_ptr<SynthConjecture> > d_conjs;
  /**
   * The first conjecture in the above vector. We track this conjecture
   * so that a synthesis conjecture can be preregistered during a call to
   * preregisterAssertion.
   */
  SynthConjecture* d_conj;
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

 public:
  SynthEngine(QuantifiersEngine* qe, context::Context* c);
  ~SynthEngine();

  bool needsCheck(Theory::Effort e) override;
  QEffort needsModel(Theory::Effort e) override;
  /* Call during quantifier engine's check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /* Called for new quantifiers */
  void registerQuantifier(Node q) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override { return "SynthEngine"; }
  /** print solution for synthesis conjectures */
  void printSynthSolution(std::ostream& out);
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
  void getSynthSolutions(std::map<Node, Node>& sol_map);
  /** preregister assertion (before rewrite)
   *
   * The purpose of this method is to inform the solution reconstruction
   * techniques within the single invocation module that n is an original
   * assertion. This is used as a heuristic to remember terms that are likely
   * to help when trying to reconstruct a solution that fits a given input
   * syntax.
   */
  void preregisterAssertion(Node n);

 public:
  class Statistics
  {
   public:
    IntStat d_cegqi_lemmas_ce;
    IntStat d_cegqi_lemmas_refine;
    IntStat d_cegqi_si_lemmas;
    IntStat d_solutions;
    IntStat d_filtered_solutions;
    IntStat d_candidate_rewrites_print;
    Statistics();
    ~Statistics();
  }; /* class SynthEngine::Statistics */
  Statistics d_statistics;
}; /* class SynthEngine */

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

#endif
