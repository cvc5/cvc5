/*********************                                                        */
/*! \file cegis_unif.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief cegis with unification techinques
 **/
#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS__CEGIS_UNIF_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS__CEGIS_UNIF_H

#include <map>
#include <vector>

#include "theory/quantifiers/sygus/sygus_module.h"
#include "theory/quantifiers/sygus/sygus_unif_rl.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

using BoolNodePair = std::pair<bool, Node>;
using BoolNodePairHashFunction =
    PairHashFunction<bool, Node, BoolHashFunction, NodeHashFunction>;
using BoolNodePairMap =
    std::unordered_map<BoolNodePair, Node, BoolNodePairHashFunction>;

/** Synthesizes functions in a data-driven SyGuS approach
 *
 * Data is derived from refinement lemmas generated through the regular CEGIS
 * approach. SyGuS is used to generate terms for classifying the data
 * (e.g. using decision tree learning) and thus generate a candidate for a
 * function-to-synthesize.
 *
 * This approach is inspired by the divide and conquer synthesis through
 * unification approach by Alur et al. TACAS 2017, by ICE-based invariant
 * synthesis from Garg et al. CAV 2014 and POPL 2016, and Padhi et al. PLDI 2016
 *
 * This module mantains a function-to-synthesize and a set of term
 * enumerators. When new terms are enumerated it tries to learn a new candidate
 * function, which is verified outside this module. If verification fails a
 * refinement lemma is generated, which this module sends to the utility that
 * learns candidates.
 */
class CegisUnif : public SygusModule
{
 public:
  CegisUnif(QuantifiersEngine* qe, CegConjecture* p);
  ~CegisUnif();
  /** initialize this class
   *
   * The module takes ownership of a conjecture when it contains a single
   * function-to-synthesize
  */
  bool initialize(Node n,
                  const std::vector<Node>& candidates,
                  std::vector<Node>& lemmas) override;
  /** adds the candidate itself to enums */
  void getTermList(const std::vector<Node>& candidates,
                   std::vector<Node>& enums) override;
  /** Tries to build a new candidate solution with new enumerated expresion
   *
   * This function relies on a data-driven unification-based approach for
   * constructing a solutions for the function-to-synthesize. See SygusUnifRl
   * for more details.
   *
   * Calls to this function are such that terms is the list of active
   * enumerators (returned by getTermList), and term_values are their current
   * model values. This function registers { terms -> terms_values } in
   * the database of values that have been enumerated, which are in turn used
   * for constructing candidate solutions when possible.
   *
   * This function also excludes models where (terms = terms_values) by adding
   * blocking clauses to lems. For example, for grammar:
   *   A -> A+A | x | 1 | 0
   * and a call where terms = { d } and term_values = { +( x, 1 ) }, it adds:
   *   ~G V ~is_+( d ) V ~is_x( d.1 ) V ~is_1( d.2 )
   * to lems, where G is active guard of the enumerator d (see
   * TermDatabaseSygus::getActiveGuardForEnumerator). This blocking clause
   * indicates that d should not be given the model value +( x, 1 ) anymore,
   * since { d -> +( x, 1 ) } has now been added to the database of this class.
   */
  bool constructCandidates(const std::vector<Node>& enums,
                           const std::vector<Node>& enum_values,
                           const std::vector<Node>& candidates,
                           std::vector<Node>& candidate_values,
                           std::vector<Node>& lems) override;

  /** Communicate refinement lemma to unification utility and external modules
   *
   * For the lemma to be sent to the external modules it adds a guard from the
   * parent conjecture which establishes that if the conjecture has a solution
   * then it must satisfy this refinement lemma
   *
   * For the lemma to be sent to the unification utility it purifies the
   * arguments of the function-to-synthensize such that all of its applications
   * are over concrete values. E.g.:
   *   f(f(f(0))) > 1
   * becomes
   *   f(0) != c1 v f(c1) != c2 v f(c2) > 1
   * in which c1 and c2 are concrete integer values
   *
   * Note that the lemma is in the deep embedding, which means that the above
   * example would actually correspond to
   *   eval(d, 0) != c1 v eval(d, c1) != c2 v eval(d, c2) > 1
   * in which d is the deep embedding of the function-to-synthesize f
  */
  void registerRefinementLemma(const std::vector<Node>& vars,
                               Node lem,
                               std::vector<Node>& lems) override;

 private:
  /** sygus term database of d_qe */
  TermDbSygus* d_tds;
  /**
   * Sygus unif utility. This class implements the core algorithm (e.g. decision
   * tree learning) that this module relies upon.
   */
  SygusUnifRl d_sygus_unif;
  /* Function-to-synthesize (in deep embedding) */
  Node d_candidate;
  /**
   * list of enumerators being used to build solutions for candidate by the
   * above utility.
   */
  std::vector<Node> d_enums;
  /** map from enumerators to active guards */
  std::map<Node, Node> d_enum_to_active_guard;
  /* list of learned refinement lemmas */
  std::vector<Node> d_refinement_lemmas;
  /**
  * This is called on the refinement lemma and will replace the arguments of the
  * function-to-synthesize by their model values (constants).
  *
  * When the traversal hits a function application of the function-to-synthesize
  * it will proceed to ensure that the arguments of that function application
  * are constants (the ensureConst becomes "true"). It populates a vector of
  * guards with the (negated) equalities between the original arguments and
  * their model values.
  */
  Node purifyLemma(Node n,
                   bool ensureConst,
                   std::vector<Node>& model_guards,
                   BoolNodePairMap& cache);

}; /* class CegisUnif */

/** Cegis Unif Enumeration Manager
 *
 *
 */
class CegisUnifEnumManager
{
 public:
  CegisUnifEnumManager(QuantifiersEngine* qe, CegConjecture* parent);
  /** initialize candidates
   *
   * Notify this class that it will be managing enumerators for the vector
   * of functions-to-synthesize (candidate variables) in candidates.
   *
   * Each c in candidates should be such that we are using a
   * synthesis-by-unification approach for c.
   */
  void initializeCandidates(std::vector<Node>& candidates);
  /** register evaluation point for candidate
   *
   * This notifies this class that eis is a set of evaluation points for
   * the given candidate. Each ei in eis should be of the same type as
   * candidate.
   */
  void registerEvalPtsForEnumerator(std::vector<Node>& eis, Node candidate);
  /** get next decision request
   *
   * This function has the same contract as Theory::getNextDecisionRequest.
   *
   */
  Node getNextDecisionRequest(unsigned& priority);

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** sygus term database of d_qe */
  TermDbSygus* d_tds;
  /** reference to the parent conjecture */
  CegConjecture* d_parent;
  /** candidate info */
  class CandidateEnumInfo
  {
   public:
    CandidateEnumInfo() {}
    /** initialize */
    void initialize();
    /** enumerators */
    std::vector<Node> d_enums;
    /** */
    std::vector<Node> d_eval_points;
  };
  std::map<Node, CandidateEnumInfo> d_ce_info;
  /** the global cost function */
  Node d_cfun;
  /** literals of the form d_cfun <= n for each n */
  std::map<unsigned, Node> d_cfun_lit;
  /**
   * The minimal n such that d_cfun <= n is asserted positively in the
   * current SAT context.
   */
  context::CDO<unsigned> d_curr_cfun_val;
  /** increment the number of enumerators */
  void incrementNumEnumerators();
  /** get current cost fun literal */
  Node getOrMkCurrentLiteral();
  /** get literal at n */
  Node getOrMkLiteral(unsigned n);
  /** register evaluation point at cost function value
   *
   * TODO
   */
  void registerEvalPtAtCostFunValue(Node c, Node ei, Node lit, unsigned n);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
