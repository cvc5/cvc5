/*********************                                                        */
/*! \file synth_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The quantifiers module for managing all approaches to synthesis,
 ** in particular, those described in Reynolds et al CAV 2015.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYNTH_ENGINE_H
#define __CVC4__THEORY__QUANTIFIERS__SYNTH_ENGINE_H

#include "context/cdhashmap.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SynthEngine : public QuantifiersModule
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;

 private:
  /** the quantified formula stating the synthesis conjecture */
  SynthConjecture* d_conj;
  /** last instantiation by single invocation module? */
  bool d_last_inst_si;
  /** the conjecture we are waiting to assign */
  Node d_waiting_conj;

 private:
  /** assign quantified formula q as the conjecture
   *
   * This method returns true if q was successfully assigned as the synthesis
   * conjecture considered by this class. This method may return false, for
   * instance, if this class determines that it would rather rewrite q to
   * an equivalent form r (in which case this method returns the lemma
   * q <=> r). An example of this is the quantifier elimination step
   * option::sygusQePreproc().
   */
  bool assignConjecture(Node q);
  /** check conjecture */
  void checkConjecture(SynthConjecture* conj);

 public:
  SynthEngine(QuantifiersEngine* qe, context::Context* c);
  ~SynthEngine();

 public:
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
  /** preregister assertion (before rewrite) */
  void preregisterAssertion(Node n);

 public:
  class Statistics
  {
   public:
    IntStat d_cegqi_lemmas_ce;
    IntStat d_cegqi_lemmas_refine;
    IntStat d_cegqi_si_lemmas;
    IntStat d_solutions;
    IntStat d_candidate_rewrites_print;
    IntStat d_candidate_rewrites;
    Statistics();
    ~Statistics();
  }; /* class SynthEngine::Statistics */
  Statistics d_statistics;
}; /* class SynthEngine */

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

#endif
