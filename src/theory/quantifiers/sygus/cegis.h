/*********************                                                        */
/*! \file cegis.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief cegis
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CEGIS_H
#define __CVC4__THEORY__QUANTIFIERS__CEGIS_H

#include <map>
#include "theory/quantifiers/sygus/sygus_module.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Cegis
 *
 * The default sygus module for synthesis, counterexample-guided inductive
 * synthesis (CEGIS).
 *
 * It initializes a list of sygus enumerators that are one-to-one with
 * candidates, and returns a list of candidates that are the model values
 * of these enumerators on calls to constructCandidates.
 *
 * It implements an optimization (getRefinementEvalLemmas) that evaluates all
 * previous refinement lemmas for a term before returning it as a candidate
 * in calls to constructCandidates.
 */
class Cegis : public SygusModule
{
 public:
  Cegis(QuantifiersEngine* qe, CegConjecture* p);
  ~Cegis() {}
  /** initialize */
  virtual bool initialize(Node n,
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
   * This function stores lem as a refinement lemma, and adds it to lems.
   */
  virtual void registerRefinementLemma(const std::vector<Node>& vars,
                                       Node lem,
                                       std::vector<Node>& lems) override;

 private:
  /** If CegConjecture::d_base_inst is exists y. P( d, y ), then this is y. */
  std::vector<Node> d_base_vars;
  /**
   * If CegConjecture::d_base_inst is exists y. P( d, y ), then this is the
   * formula P( CegConjecture::d_candidates, y ).
   */
  Node d_base_body;

  //-----------------------------------refinement lemmas
  /** refinement lemmas */
  std::vector<Node> d_refinement_lemmas;
  /** get number of refinement lemmas we have added so far */
  unsigned getNumRefinementLemmas() { return d_refinement_lemmas.size(); }
  /** get refinement lemma
   *
   * If d_embed_quant is forall d. exists y. P( d, y ), then a refinement
   * lemma is one of the form ~P( d_candidates, c ) for some c.
   */
  Node getRefinementLemma(unsigned i) { return d_refinement_lemmas[i]; }
  /** sample add refinement lemma
   *
   * This function will check if there is a sample point in d_sampler that
   * refutes the candidate solution (d_quant_vars->vals). If so, it adds a
   * refinement lemma to the lists d_refinement_lemmas that corresponds to that
   * sample point, and adds a lemma to lems if cegisSample mode is not trust.
   */
  bool sampleAddRefinementLemma(const std::vector<Node>& candidates,
                                const std::vector<Node>& vals,
                                std::vector<Node>& lems);
  //-----------------------------------end refinement lemmas

  /** Get refinement evaluation lemmas
   *
   * Given a candidate solution ms for candidates vs, this function adds lemmas
   * to lems based on evaluating the conjecture, instantiated for ms, on lemmas
   * for previous refinements (d_refinement_lemmas).
   */
  void getRefinementEvalLemmas(const std::vector<Node>& vs,
                               const std::vector<Node>& ms,
                               std::vector<Node>& lems);
  /** sampler object for the option cegisSample()
   *
   * This samples points of the type of the inner variables of the synthesis
   * conjecture (d_base_vars).
   */
  SygusSampler d_cegis_sampler;
  /** cegis sample refine points
   *
   * Stores the list of indices of sample points in d_cegis_sampler we have
   * added as refinement lemmas.
   */
  std::unordered_set<unsigned> d_cegis_sample_refine;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__CEGIS_H */
