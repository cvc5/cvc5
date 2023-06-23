/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * cegis with unification techinques.
 */
#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__CEGIS_UNIF_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__CEGIS_UNIF_H

#include <map>
#include <vector>

#include "smt/env_obj.h"
#include "theory/decision_strategy.h"
#include "theory/quantifiers/sygus/cegis.h"
#include "theory/quantifiers/sygus/sygus_unif_rl.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/** Cegis Unif Enumerators Decision Strategy
 *
 * This class enforces a decision strategy that limits the number of
 * unique values given to the set of heads of evaluation points and conditions
 * enumerators for these points, which are variables of sygus datatype type that
 * are introduced by CegisUnif.
 *
 * It maintains a set of guards, call them G_uq_1 ... G_uq_n, where the
 * semantics of G_uq_i is "for each type, the heads of evaluation points of that
 * type are interpreted as a value in a set whose cardinality is at most i".
 * We also enforce that the number of condition enumerators for evaluation
 * points is equal to (n-1).
 *
 * To enforce this, we introduce sygus enumerator(s) of the same type as the
 * heads of evaluation points and condition enumerators registered to this class
 * and add lemmas that enforce that these terms are equal to at least one
 * enumerator (see registerEvalPtAtSize).
 */
class CegisUnifEnumDecisionStrategy : public DecisionStrategyFmf
{
 public:
  CegisUnifEnumDecisionStrategy(Env& env,
                                QuantifiersState& qs,
                                QuantifiersInferenceManager& qim,
                                TermDbSygus* tds,
                                SynthConjecture* parent);
  /** Make the n^th literal of this strategy (G_uq_n).
   *
   * This call may add new lemmas of the form described above
   * registerEvalPtAtValue on the output channel of d_qe.
   */
  Node mkLiteral(unsigned n) override;
  /** identify */
  std::string identify() const override
  {
    return std::string("cegis_unif_num_enums");
  }

  /** initialize candidates
   *
   * Notify this class that it will be managing enumerators for the vector
   * of strategy points es. This function should only be called once.
   *
   * Each strategy point in es should be such that we are using a
   * synthesis-by-unification approach for its candidate.
   */
  void initialize(const std::vector<Node>& es,
                  const std::map<Node, Node>& e_to_cond,
                  const std::map<Node, std::vector<Node>>& strategy_lemmas);

  /*
   * Do not hide the zero-argument version of initialize() inherited from the
   * base class
   */
  using DecisionStrategy::initialize;

  /** get the current set of enumerators for strategy point e
   *
   * Index 0 adds the set of return value enumerators to es, index 1 adds the
   * set of condition enumerators to es.
   */
  void getEnumeratorsForStrategyPt(Node e,
                                   std::vector<Node>& es,
                                   unsigned index) const;
  /** register evaluation point for candidate
   *
   * This notifies this class that eis is a set of heads of evaluation points
   * for strategy point e, where e was passed to initialize in the vector es.
   *
   * This may add new lemmas of the form described above
   * registerEvalPtAtSize on the output channel of d_qe.
   */
  void registerEvalPts(const std::vector<Node>& eis, Node e);

 private:
  /** Reference to the quantifiers inference manager */
  QuantifiersInferenceManager& d_qim;
  /** sygus term database of d_qe */
  TermDbSygus* d_tds;
  /** reference to the parent conjecture */
  SynthConjecture* d_parent;
  /**
   * Whether we are using condition pool enumeration (Section 4 of Barbosa et al
   * FMCAD 2019). This is determined by option::sygusUnifPi().
   */
  bool d_useCondPool;
  /** whether this module has been initialized */
  bool d_initialized;
  /** null node */
  Node d_null;
  /** information per initialized type */
  class StrategyPtInfo
  {
   public:
    StrategyPtInfo() {}
    /** strategy point for this type */
    Node d_pt;
    /** the set of enumerators we have allocated for this strategy point
     *
     * Index 0 stores the return value enumerators, and index 1 stores the
     * conditional enumerators. We have that
     *   d_enums[0].size()==d_enums[1].size()+1.
     */
    std::vector<Node> d_enums[2];
    /** the type of conditional enumerators for this strategy point  */
    TypeNode d_ce_type;
    /**
     * The set of evaluation points of this type. In models, we ensure that
     * each of these are equal to one of d_enums[0].
     */
    std::vector<Node> d_eval_points;
    /** symmetry breaking lemma template for this strategy point
     *
     * Each pair stores (the symmetry breaking lemma template, argument (to be
     * instantiated) of symmetry breaking lemma template).
     *
     * Index 0 stores the symmetry breaking lemma template for return values,
     * index 1 stores the template for conditions.
     */
    std::pair<Node, Node> d_sbt_lemma_tmpl[2];
  };
  /** map strategy points to the above info */
  std::map<Node, StrategyPtInfo> d_ce_info;
  /** the "virtual" enumerator
   *
   * This enumerator is used for enforcing fairness. In particular, we relate
   * its size to the number of conditions allocated by this class such that:
   *    ~G_uq_i => size(d_virtual_enum) >= floor( log2( i-1 ) )
   * In other words, if we are using (i-1) conditions in our solution,
   * the size of the virtual enumerator is at least the floor of the log (base
   * two) of (i-1). Due to the default fairness scheme in the quantifier-free
   * datatypes solver (if --sygus-fair-max is enabled), this ensures that other
   * enumerators are allowed to have at least this size. This affect other
   * fairness schemes in an analogous fashion. In particular, we enumerate
   * based on the tuples for (term size, #conditions):
   *   (0,0), (0,1)                                             [size 0]
   *   (0,2), (0,3), (1,1), (1,2), (1,3)                        [size 1]
   *   (0,4), ..., (0,7), (1,4), ..., (1,7), (2,0), ..., (2,7)  [size 2]
   *   (0,8), ..., (0,15), (1,8), ..., (1,15), ...              [size 3]
   */
  Node d_virtual_enum;
  /** Registers an enumerator and adds symmetry breaking lemmas
   *
   * The symmetry breaking lemmas are generated according to the stored
   * information from the enumerator's respective strategy point and whether it
   * is a condition or return value enumerator. For the latter we add symmetry
   * breaking lemmas that force enumerators to consider values in an increasing
   * order of size.
   */
  void setUpEnumerator(Node e, StrategyPtInfo& si, unsigned index);
  /** register evaluation point at size
   *
   * This sends a lemma of the form:
   *   G_uq_n => ei = d1 V ... V ei = dn
   * on the output channel of d_qe, where d1...dn are sygus enumerators of the
   * same type as e and ei, and ei is an evaluation point of strategy point e.
   */
  void registerEvalPtAtSize(Node e, Node ei, Node guq_lit, unsigned n);
};

/** Synthesizes functions in a data-driven SyGuS approach
 *
 * Data is derived from refinement lemmas generated through the regular CEGIS
 * approach. SyGuS is used to generate terms for classifying the data
 * (e.g. using decision tree learning) and thus generate a candidates for
 * functions-to-synthesize.
 *
 * This approach is inspired by the divide and conquer synthesis through
 * unification approach by Alur et al. TACAS 2017, by ICE-based invariant
 * synthesis from Garg et al. CAV 2014 and POPL 2016, and Padhi et al. PLDI 2016
 *
 * This module mantains a set of functions-to-synthesize and a set of term
 * enumerators. When new terms are enumerated it tries to learn new candidate
 * solutions, which are verified outside this module. If verification fails a
 * refinement lemma is generated, which this module sends to the utility that
 * learns candidates.
 */
class CegisUnif : public Cegis
{
 public:
  CegisUnif(Env& env,
            QuantifiersState& qs,
            QuantifiersInferenceManager& qim,
            TermDbSygus* tds,
            SynthConjecture* p);
  ~CegisUnif() override;
  /** Retrieves enumerators for constructing solutions
   *
   * Non-unification candidates have themselves as enumerators, while for
   * unification candidates we add their conditonal enumerators to enums if
   * their respective guards are set in the current model
   */
  void getTermList(const std::vector<Node>& candidates,
                   std::vector<Node>& enums) override;

  /** Communicates refinement lemma to unification utility and external modules
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
                               Node lem) override;

 private:
  /** do cegis-implementation-specific initialization for this class */
  bool processInitialize(Node conj,
                         Node n,
                         const std::vector<Node>& candidates) override;
  /** Tries to build new candidate solutions with new enumerated expressions
   *
   * This function relies on a data-driven unification-based approach for
   * constructing solutions for the functions-to-synthesize. See SygusUnifRl for
   * more details.
   *
   * Calls to this function are such that terms is the list of active
   * enumerators (returned by getTermList), and term_values are their current
   * model values. This function registers { terms -> terms_values } in
   * the database of values that have been enumerated, which are in turn used
   * for constructing candidate solutions when possible.
   *
   * This function also excludes models where (terms = terms_values) by adding
   * blocking clauses to d_qim pending lemmas. For example, for grammar:
   *   A -> A+A | x | 1 | 0
   * and a call where terms = { d } and term_values = { +( x, 1 ) }, it adds:
   *   ~G V ~is_+( d ) V ~is_x( d.1 ) V ~is_1( d.2 )
   * to d_qim pending lemmas, where G is active guard of the enumerator d (see
   * TermDatabaseSygus::getActiveGuardForEnumerator). This blocking clause
   * indicates that d should not be given the model value +( x, 1 ) anymore,
   * since { d -> +( x, 1 ) } has now been added to the database of this class.
   */
  bool processConstructCandidates(const std::vector<Node>& enums,
                                  const std::vector<Node>& enum_values,
                                  const std::vector<Node>& candidates,
                                  std::vector<Node>& candidate_values,
                                  bool satisfiedRl) override;
  /** communicate condition values to solution building utility
   *
   * for each unification candidate and for each strategy point associated with
   * it, set in d_sygus_unif the condition values (unif_cvalues) for respective
   * condition enumerators (unif_cenums)
   */
  void setConditions(const std::map<Node, std::vector<Node>>& unif_cenums,
                     const std::map<Node, std::vector<Node>>& unif_cvalues);
  /** set values of condition enumerators based on current enumerator assignment
   *
   * enums and enum_values are the enumerators registered in getTermList and
   * their values retrieved by the parent SynthConjecture module, respectively.
   *
   * unif_cenums and unif_cvalues associate the conditional enumerators of each
   * strategy point of each unification candidate with their respective model
   * values
   *
   * This function also generates inter-enumerator symmetry breaking for return
   * values, such that their model values are ordered by size
   *
   * returns true if no symmetry breaking lemmas were generated for the return
   * value enumerators, false otherwise
   */
  bool getEnumValues(const std::vector<Node>& enums,
                     const std::vector<Node>& enum_values,
                     std::map<Node, std::vector<Node>>& unif_cenums,
                     std::map<Node, std::vector<Node>>& unif_cvalues);

  /**
   * Whether we are using condition pool enumeration (Section 4 of Barbosa et al
   * FMCAD 2019). This is determined by option::sygusUnifPi().
   */
  bool usingConditionPool() const;
  /**
   * Sygus unif utility. This class implements the core algorithm (e.g. decision
   * tree learning) that this module relies upon.
   */
  SygusUnifRl d_sygus_unif;
  /** enumerator manager utility */
  CegisUnifEnumDecisionStrategy d_u_enum_manager;
  /* The null node */
  Node d_null;
  /** the unification candidates */
  std::vector<Node> d_unif_candidates;
  /** the non-unification candidates */
  std::vector<Node> d_non_unif_candidates;
  /** list of strategy points per candidate */
  std::map<Node, std::vector<Node>> d_cand_to_strat_pt;
  /** map from conditional enumerators to their strategy point */
  std::map<Node, Node> d_cenum_to_strat_pt;
}; /* class CegisUnif */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
