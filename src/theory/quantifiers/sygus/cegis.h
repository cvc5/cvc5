/*********************                                                        */
/*! \file cegis.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief cegis
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEGIS_H
#define CVC4__THEORY__QUANTIFIERS__CEGIS_H

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
  Cegis(QuantifiersEngine* qe, SynthConjecture* p);
  ~Cegis() override {}
  /** initialize */
  virtual bool initialize(Node conj,
                          Node n,
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
  /** using repair const */
  virtual bool usingRepairConst() override;

 protected:
  /** the evaluation unfold utility of d_tds */
  SygusEvalUnfold* d_eval_unfold;
  /** If SynthConjecture::d_base_inst is exists y. P( d, y ), then this is y. */
  std::vector<Node> d_base_vars;
  /**
   * If SynthConjecture::d_base_inst is exists y. P( d, y ), then this is the
   * formula P( SynthConjecture::d_candidates, y ).
   */
  Node d_base_body;
  //----------------------------------cegis-implementation-specific
  /**
   * Do cegis-implementation-specific initialization for this class. The return
   * value and behavior of this function is the same as initialize(...) above.
   */
  virtual bool processInitialize(Node conj,
                                 Node n,
                                 const std::vector<Node>& candidates,
                                 std::vector<Node>& lemmas);
  /** do cegis-implementation-specific post-processing for construct candidate
   *
   * satisfiedRl is whether all refinement lemmas are satisfied under the
   * substitution { enums -> enum_values }.
   *
   * The return value and behavior of this function is the same as
   * constructCandidates(...) above.
   */
  virtual bool processConstructCandidates(const std::vector<Node>& enums,
                                          const std::vector<Node>& enum_values,
                                          const std::vector<Node>& candidates,
                                          std::vector<Node>& candidate_values,
                                          bool satisfiedRl,
                                          std::vector<Node>& lems);
  //----------------------------------end cegis-implementation-specific

  //-----------------------------------refinement lemmas
  /** refinement lemmas */
  std::vector<Node> d_refinement_lemmas;
  /** (processed) conjunctions of refinement lemmas that are not unit */
  std::unordered_set<Node, NodeHashFunction> d_refinement_lemma_conj;
  /** (processed) conjunctions of refinement lemmas that are unit */
  std::unordered_set<Node, NodeHashFunction> d_refinement_lemma_unit;
  /** substitution entailed by d_refinement_lemma_unit */
  std::vector<Node> d_rl_eval_hds;
  std::vector<Node> d_rl_vals;
  /** all variables appearing in refinement lemmas */
  std::unordered_set<Node, NodeHashFunction> d_refinement_lemma_vars;

  /** adds lem as a refinement lemma */
  void addRefinementLemma(Node lem);
  /** add refinement lemma conjunct
   *
   * This is a helper function for addRefinementLemma.
   *
   * This adds waiting[wcounter] to the proper vector (d_refinement_lemma_conj
   * or d_refinement_lemma_unit). In the case that waiting[wcounter] corresponds
   * to a value propagation, e.g. it is of the form:
   *   (eval x c1...cn) = c
   * then it is added to d_refinement_lemma_unit, (eval x c1...cn) -> c is added
   * as a substitution in d_rl_eval_hds/d_rl_eval_vals, and applied to previous
   * lemmas in d_refinement_lemma_conj and lemmas waiting[k] for k>wcounter.
   * Each lemma in d_refinement_lemma_conj that is modifed in this process is
   * moved to the vector waiting.
   */
  void addRefinementLemmaConjunct(unsigned wcounter,
                                  std::vector<Node>& waiting);
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

  /** evaluates candidate values on current refinement lemmas
   *
   * This method performs techniques that ensure that
   * { candidates -> candidate_values } is a candidate solution that should
   * be checked by the solution verifier of the CEGIS loop. This method
   * invokes two sub-methods which may reject the current solution.
   * The first is "refinement evaluation", described above the method
   * getRefinementEvalLemmas below. The second is "evaluation unfolding",
   * which eagerly unfolds applications of evaluation functions (see
   * sygus_eval_unfold.h for details).
   *
   * If this method returns true, then { candidates -> candidate_values }
   * is not ready to be tried as a candidate solution. In this case, it may add
   * lemmas to lems.
   *
   * Notice that this method may return true without adding any lemmas to
   * lems, in the case that terms from candidates are "actively-generated
   * enumerators", since the model values of such terms are managed
   * explicitly within getEnumeratedValue. In this case, the owner of the
   * actively-generated enumerators (e.g. SynthConjecture) is responsible for
   * blocking the current value of candidates.
   */
  bool addEvalLemmas(const std::vector<Node>& candidates,
                     const std::vector<Node>& candidate_values,
                     std::vector<Node>& lems);
  /** Get the node corresponding to the conjunction of all refinement lemmas. */
  Node getRefinementLemmaFormula();
  //-----------------------------------end refinement lemmas

  /** Get refinement evaluation lemmas
   *
   * This method performs "refinement evaluation", that is, it tests
   * whether the current solution, given by { vs -> ms },
   * satisfies all current refinement lemmas. If it does not, it may add
   * blocking lemmas L to lems which exclude (a generalization of) the current
   * solution.
   *
   * Given a candidate solution ms for candidates vs, this function adds lemmas
   * to lems based on evaluating the conjecture, instantiated for ms, on lemmas
   * for previous refinements (d_refinement_lemmas).
   *
   * Returns true if any such lemma exists.
   */
  bool getRefinementEvalLemmas(const std::vector<Node>& vs,
                               const std::vector<Node>& ms,
                               std::vector<Node>& lems);
  /** Check refinement evaluation lemmas
   *
   * This method is similar to above, but does not perform any generalization
   * techniques. It is used when we are using only fast enumerators for
   * all functions-to-synthesize.
   *
   * Returns true if a refinement lemma is false for the solution
   * { vs -> ms }.
   */
  bool checkRefinementEvalLemmas(const std::vector<Node>& vs,
                                 const std::vector<Node>& ms);
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

  //---------------------------------for symbolic constructors
  /** are we using symbolic constants?
   *
   * This flag is set ot true if at least one of the enumerators allocated
   * by this class has been configured to allow model values with symbolic
   * constructors, such as the "any constant" constructor.
   */
  bool d_usingSymCons;
  //---------------------------------end for symbolic constructors
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__CEGIS_H */
