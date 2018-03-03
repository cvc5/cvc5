/*********************                                                        */
/*! \file inv_synth.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for specialized approaches for invariant synthesis
 **/
#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS__INVBE_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS__INVBE_H

#include <map>
#include <string>
#include <vector>

#include "theory/quantifiers/sygus/sygus_module.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Synthesizes invariants in a "by-examples" approach
 *
 * Successively performs strengthening and weakining of candidate invariants
 * based on counterexamples produced while verifying that a candidate invariant
 * satisfies the constraints
 *
 * Synthesis is used for deriving "features", atomic expressions that are used
 * to separate "good", "bad", and "conditional" valuations to the state
 * variables in the transition system. Once points can be separated without
 * conflicts, a CNF is built (not using synthesis) with the features, thus
 * yielding the invariant.
 *
 * Strengthening occurs when testing the candidate yields a "bad" or a
 * "conditional" valuation, while weakining occurs when testing yields a "good"
 * point. "Good" points are those in which the invariant must always hold, "bad"
 * in which it must never hold, and "conditional" those in which the invariant
 * cannot hold then fail to hold (representing the invariant not being
 * inductive, as applying a transition invalidates it). Good and bad points are
 * independent of the candidate being derived, while conditional points are
 * those in which an specific candidate went from good points to bad points .
 *
 * This approach is inspired by Padhi et al. PLDI 2016
 */
class InvBE : public SygusModule
{
 public:
  InvBE(QuantifiersEngine* qe, CegConjecture* p) : SygusModule(qe, p) {}
  ~InvBE() {}
  /** initialize this class
   *
   * If n can be broken into an invariant synthesis problem, i.e. some processed
   * form equisatisfiable to
   *
   *     Pre(x) => Inv(x)
   * &&  Inv(x) && Trans(x, x') => Inv(x')
   * &&  Inv(x) => Pos(x)
   *
   * then this module takes onwership of the conjecture.

 */
  virtual void initialize(Node n,
                          const std::vector<Node>& candidates,
                          std::vector<Node>& lemmas) override;
  /** get term list */
  virtual void getTermList(const std::vector<Node>& candidates,
                           std::vector<Node>& enums) override;
  /** construct candidate */
  virtual bool constructCandidates(const std::vector<Node>& enums,
                                   const std::vector<Node>& enum_values,
                                   const std::vector<Node>& candidates,
                                   std::vector<Node>& candidate_values,
                                   std::vector<Node>& lems) override;

  /** register refinement lemma
   *
   * Performs conflict analysis to obtain the counterexamples to guide invariant
   * synthesis
   *
   * This function does not modify lems since it does not require solutions to
   * be blocked externally */
  virtual void registerRefinementLemma(const std::vector<Node>& vars,
                                       Node lem,
                                       std::vector<Node>& lems) override;

 private:


}; /* class InvBE */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
