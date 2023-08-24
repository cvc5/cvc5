/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for processing programming by examples synthesis conjectures.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_PBE_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_PBE_H

#include "smt/env_obj.h"
#include "theory/quantifiers/sygus/sygus_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class SygusUnifIo;
class SynthConjecture;

/** SygusPbe
 *
 * This class implements optimizations that target synthesis conjectures
 * that are in Programming-By-Examples (PBE) form.
 *
 * [EX#1] An example of a synthesis conjecture in PBE form is :
 * exists f. forall x.
 * ( f( 0 ) = 2 ) ^ ( f( 5 ) = 7 ) ^ ( f( 6 ) = 8 )
 *
 * We say that the above conjecture has I/O examples (0)->2, (5)->7, (6)->8.
 *
 * Internally, this class does the following for SyGuS inputs:
 *
 * (1) Infers whether the input conjecture is in PBE form or not, which
 *     is based on looking up information in the ExampleInfer utility.
 * (2) Based on this information and on the syntactic restrictions, it
 *     devises a strategy for enumerating terms and construction solutions,
 *     which is inspired by Alur et al. "Scaling Enumerative Program Synthesis
 *     via Divide and Conquer" TACAS 2017. In particular, it may consider
 *     strategies for constructing decision trees when the grammar permits ITEs
 *     and a strategy for divide-and-conquer string synthesis when the grammar
 *     permits string concatenation. This is managed through the SygusUnif
 *     utilities, d_sygus_unif.
 * (3) It makes (possibly multiple) calls to
 *     TermDatabaseSygus::regstierEnumerator(...) based
 *     on the strategy, which inform the rest of the system to enumerate values
 *     of particular types in the grammar through use of fresh variables which
 *     we call "enumerators".
 *
 * Points (1)-(3) happen within a call to SygusPbe::initialize(...).
 *
 * Notice that each enumerator is associated with a single
 * function-to-synthesize, but a function-to-sythesize may be mapped to multiple
 * enumerators. Some public functions of this class expect an enumerator as
 * input, which we map to a function-to-synthesize via
 * TermDatabaseSygus::getSynthFunFor(e).
 *
 * An enumerator is initially "active" but may become inactive if the
 * enumeration exhausts all possible values in the datatype corresponding to
 * syntactic restrictions for it. The search may continue unless all enumerators
 * become inactive.
 *
 * (4) When the extension of quantifier-free datatypes procedure for SyGuS
 *     datatypes terminates with a model, the parent of this class calls
 *     SygusPbe::getCandidateList(...), where this class returns the list
 *     of active enumerators.
 * (5) The parent class subsequently calls
 *     SygusPbe::constructValues(...), which informs this class that new
 *     values have been enumerated for active enumerators, as indicated by the
 *     current model. This call also requests that based on these
 *     newly enumerated values, whether this class is now able to construct a
 *     solution based on the high-level strategy (stored in d_sygus_unif).
 *
 * This class is not designed to work in incremental mode, since there is no way
 * to specify incremental problems in SyguS.
 */
class SygusPbe : public SygusModule
{
 public:
  SygusPbe(Env& env,
           QuantifiersState& qs,
           QuantifiersInferenceManager& qim,
           TermDbSygus* tds,
           SynthConjecture* p);
  ~SygusPbe();

  /** initialize this class
   *
   * This function may add lemmas via the inference manager corresponding
   * to initial lemmas regarding static analysis of enumerators it
   * introduced. For example, we may say that the top-level symbol
   * of an enumerator is not ITE if it is being used to construct
   * return values for decision trees.
   */
  bool initialize(Node conj,
                  Node n,
                  const std::vector<Node>& candidates) override;
  /** get term list
   *
  * Adds all active enumerators associated with functions-to-synthesize in
  * candidates to terms.
  */
  void getTermList(const std::vector<Node>& candidates,
                   std::vector<Node>& terms) override;
  /**
   * PBE allows partial models to handle multiple enumerators if we are not
   * using a strictly fair enumeration strategy.
   */
  bool allowPartialModel() override;
  /** construct candidates
   *
   * This function attempts to use unification-based approaches for constructing
   * solutions for all functions-to-synthesize (indicated by candidates). These
   * approaches include decision tree learning and a divide-and-conquer
   * algorithm based on string concatenation.
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
   * to d_qim, where G is active guard of the enumerator d (see
   * TermDatabaseSygus::getActiveGuardForEnumerator). This blocking clause
   * indicates that d should not be given the model value +( x, 1 ) anymore,
   * since { d -> +( x, 1 ) } has now been added to the database of this class.
   */
  bool constructCandidates(const std::vector<Node>& terms,
                           const std::vector<Node>& term_values,
                           const std::vector<Node>& candidates,
                           std::vector<Node>& candidate_values) override;
  /** is PBE enabled for any enumerator? */
  bool isPbe() { return d_is_pbe; }

 private:
  /** true and false nodes */
  Node d_true;
  Node d_false;
  /** is this a PBE conjecture for any function? */
  bool d_is_pbe;
  /**
   * Map from candidates to sygus unif utility. This class implements
   * the core algorithm (e.g. decision tree learning) that this module relies
   * upon.
   */
  std::map<Node, std::unique_ptr<SygusUnifIo> > d_sygus_unif;
  /**
   * map from candidates to the list of enumerators that are being used to
   * build solutions for that candidate by the above utility.
   */
  std::map<Node, std::vector<Node> > d_candidate_to_enum;
  /** reverse map of above */
  std::map<Node, Node> d_enum_to_candidate;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
