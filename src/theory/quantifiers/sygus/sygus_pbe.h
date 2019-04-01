/*********************                                                        */
/*! \file sygus_pbe.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing programming by examples synthesis conjectures
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_PBE_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_PBE_H

#include "context/cdhashmap.h"
#include "theory/quantifiers/sygus/sygus_module.h"
#include "theory/quantifiers/sygus/sygus_unif_io.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SynthConjecture;

/** SygusPbe
 *
 * This class implements optimizations that target synthesis conjectures
 * that are in Programming-By-Examples (PBE) form.
 *
 * [EX#1] An example of a synthesis conjecture in PBE form is :
 * exists f. forall x.
 * ( x = 0 => f( x ) = 2 ) ^ ( x = 5 => f( x ) = 7 ) ^ ( x = 6 => f( x ) = 8 )
 *
 * We say that the above conjecture has I/O examples (0)->2, (5)->7, (6)->8.
 *
 * Internally, this class does the following for SyGuS inputs:
 *
 * (1) Infers whether the input conjecture is in PBE form or not.
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
 * (4) During search, the extension of quantifier-free datatypes procedure for
 *     SyGuS datatypes may ask this class whether current candidates can be
 *     discarded based on inferring when two candidate solutions are equivalent
 *     up to examples. For example, the candidate solutions:
 *     f = \x ite( x < 0, x+1, x ) and f = \x x
 *     are equivalent up to examples on the above conjecture, since they have
 * the same value on the points x = 0,5,6. Hence, we need only consider one of
 *     them. The interface for querying this is
 *       SygusPbe::addSearchVal(...).
 *     For details, see Reynolds et al. SYNT 2017.
 *
 * (5) When the extension of quantifier-free datatypes procedure for SyGuS
 *     datatypes terminates with a model, the parent of this class calls
 *     SygusPbe::getCandidateList(...), where this class returns the list
 *     of active enumerators.
 * (6) The parent class subsequently calls
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
  SygusPbe(QuantifiersEngine* qe, SynthConjecture* p);
  ~SygusPbe();

  /** initialize this class
  *
  * This function may add lemmas to the vector lemmas corresponding
  * to initial lemmas regarding static analysis of enumerators it
  * introduced. For example, we may say that the top-level symbol
  * of an enumerator is not ITE if it is being used to construct
  * return values for decision trees.
  */
  bool initialize(Node n,
                  const std::vector<Node>& candidates,
                  std::vector<Node>& lemmas) override;
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
   * blocking clauses to lems. For example, for grammar:
   *   A -> A+A | x | 1 | 0
   * and a call where terms = { d } and term_values = { +( x, 1 ) }, it adds:
   *   ~G V ~is_+( d ) V ~is_x( d.1 ) V ~is_1( d.2 )
   * to lems, where G is active guard of the enumerator d (see
   * TermDatabaseSygus::getActiveGuardForEnumerator). This blocking clause
   * indicates that d should not be given the model value +( x, 1 ) anymore,
   * since { d -> +( x, 1 ) } has now been added to the database of this class.
   */
  bool constructCandidates(const std::vector<Node>& terms,
                           const std::vector<Node>& term_values,
                           const std::vector<Node>& candidates,
                           std::vector<Node>& candidate_values,
                           std::vector<Node>& lems) override;
  /** is PBE enabled for any enumerator? */
  bool isPbe() { return d_is_pbe; }
  /** is the enumerator e associated with I/O example pairs? */
  bool hasExamples(Node e);
  /** get number of I/O example pairs for enumerator e */
  unsigned getNumExamples(Node e);
  /** get the input arguments for i^th I/O example for e, which is added to the
   * vector ex */
  void getExample(Node e, unsigned i, std::vector<Node>& ex);
  /** get the output value of the i^th I/O example for enumerator e */
  Node getExampleOut(Node e, unsigned i);

  /** add the search val
  * This function is called by the extension of quantifier-free datatypes
  * procedure for SyGuS datatypes when we are considering a value of
  * enumerator e of sygus type tn whose analog in the signature of builtin
  * theory is bvr.
  *
  * For example, bvr = x + 1 when e is the datatype value Plus( x(), One() ) and
  * tn is a sygus datatype that encodes a subsignature of the integers.
  *
  * This returns either:
  * - A SyGuS term whose analog is equivalent to bvr up to examples
  *   In the above example,
  *   it may return a term t of the form Plus( One(), x() ), such that this
  *   function was previously called with t as input.
  * - e, indicating that no previous terms are equivalent to e up to examples.
  */
  Node addSearchVal(TypeNode tn, Node e, Node bvr);
  /** evaluate builtin
  * This returns the evaluation of bn on the i^th example for the
  * function-to-synthesis
  * associated with enumerator e. If there are not at least i examples, it
  * returns the rewritten form of bn.
  * For example, if bn = x+5, e is an enumerator for f in the above example
  * [EX#1], then
  *   evaluateBuiltin( tn, bn, e, 0 ) = 7
  *   evaluateBuiltin( tn, bn, e, 1 ) = 9
  *   evaluateBuiltin( tn, bn, e, 2 ) = 10
  */
  Node evaluateBuiltin(TypeNode tn, Node bn, Node e, unsigned i);

 private:
  /** true and false nodes */
  Node d_true;
  Node d_false;
  /** is this a PBE conjecture for any function? */
  bool d_is_pbe;
  /** for each candidate variable f (a function-to-synthesize), whether the
  * conjecture is purely PBE for that variable
  * In other words, all occurrences of f are guarded by equalities that
  * constraint its arguments to constants.
  */
  std::map<Node, bool> d_examples_invalid;
  /** for each candidate variable (function-to-synthesize), whether the
  * conjecture is purely PBE for that variable.
  * An example of a conjecture for which d_examples_invalid is false but
  * d_examples_out_invalid is true is:
  *   exists f. forall x. ( x = 0 => f( x ) > 2 )
  * another example is:
  *   exists f. forall x. ( ( x = 0 => f( x ) = 2 ) V ( x = 3 => f( x ) = 3 ) )
  * since the formula is not a conjunction (the example values are not
  * entailed).
  * However, the domain of f in both cases is finite, which can be used for
  * search space pruning.
  */
  std::map<Node, bool> d_examples_out_invalid;
  /**
   * Map from candidates to sygus unif utility. This class implements
   * the core algorithm (e.g. decision tree learning) that this module relies
   * upon.
   */
  std::map<Node, SygusUnifIo> d_sygus_unif;
  /**
   * map from candidates to the list of enumerators that are being used to
   * build solutions for that candidate by the above utility.
   */
  std::map<Node, std::vector<Node> > d_candidate_to_enum;
  /** reverse map of above */
  std::map<Node, Node> d_enum_to_candidate;
  /** for each candidate variable (function-to-synthesize), input of I/O
   * examples */
  std::map<Node, std::vector<std::vector<Node> > > d_examples;
  /** for each candidate variable (function-to-synthesize), output of I/O
   * examples */
  std::map<Node, std::vector<Node> > d_examples_out;
  /** the list of example terms
   * For the example [EX#1] above, this is f( 0 ), f( 5 ), f( 6 )
   */
  std::map<Node, std::vector<Node> > d_examples_term;
  /**
   * Map from example input terms to their output, for example [EX#1] above,
   * this is { f( 0 ) -> 2, f( 5 ) -> 7, f( 6 ) -> 8 }.
   */
  std::map<Node, Node> d_exampleTermMap;
  /** collect the PBE examples in n
   * This is called on the input conjecture, and will populate the above
   * vectors, where hasPol/pol denote the polarity of n in the conjecture. This
   * function returns false if it finds two examples that are contradictory.
   */
  bool collectExamples(Node n,
                       std::map<Node, bool>& visited,
                       bool hasPol,
                       bool pol);

  //--------------------------------- PBE search values
  /**
   * This class is an index of candidate solutions for PBE synthesis and their
   * (concrete) evaluation on the set of input examples. For example, if the
   * set of input examples for (x,y) is (0,1), (1,3), then:
   *   term x is indexed by 0,1
   *   term x+y is indexed by 1,4
   *   term 0 is indexed by 0,0.
   */
  class PbeTrie
  {
   public:
    PbeTrie() {}
    ~PbeTrie() {}
    /** the children for this node in the trie */
    std::map<Node, PbeTrie> d_children;
    /** clear this trie */
    void clear() { d_children.clear(); }
    /**
     * Add term b whose value on examples is exOut to the trie. Return
     * the first term registered to this trie whose evaluation was exOut.
     */
    Node addTerm(Node b, const std::vector<Node>& exOut);
  };
  /** trie of candidate solutions tried
  * This stores information for each (enumerator, type),
  * where type is a type in the grammar of the space of solutions for a subterm
  * of e. This is used for symmetry breaking in quantifier-free reasoning
  * about SyGuS datatypes.
  */
  std::map<Node, std::map<TypeNode, PbeTrie> > d_pbe_trie;
  //--------------------------------- end PBE search values
};

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
