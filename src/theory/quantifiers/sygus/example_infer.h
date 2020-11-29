/*********************                                                        */
/*! \file example_infer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for inferring whether a formula is in examples form
 ** (functions applied to concrete arguments only).
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__EXAMPLE_INFER_H
#define CVC4__THEORY__QUANTIFIERS__EXAMPLE_INFER_H

#include "context/cdhashmap.h"
#include "theory/quantifiers/sygus/sygus_module.h"
#include "theory/quantifiers/sygus/sygus_unif_io.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Example Inference
 *
 * This class determines whether a formula "has examples", for details
 * see the method hasExamples below. This is important for certain
 * optimizations in enumerative SyGuS, include example-based symmetry breaking
 * (discarding terms that are equivalent to a previous one up to examples).
 *
 * Additionally, it provides helper methods for retrieving the examples
 * for a function-to-synthesize and for evaluating terms under the inferred
 * set of examples.
 */
class ExampleInfer
{
 public:
  ExampleInfer(TermDbSygus* tds);
  ~ExampleInfer();
  /** initialize
   *
   * This method initializes the data of this class so that examples are
   * inferred for functions-to-synthesize candidates in n, where
   * n is the "base instantiation" of the deep-embedding version of the
   * synthesis conjecture under candidates (see SynthConjecture::d_base_inst).
   *
   * Returns false if and only if n has a conflicting example input/output,
   * for example if n is ( f(0) = 1 ^ f(0) = 2 ).
   */
  bool initialize(Node n, const std::vector<Node>& candidates);
  /** does the conjecture have examples for all candidates? */
  bool isExamples() const { return d_isExamples; }
  /**
   * Is the enumerator e associated with examples? This is true if the
   * function-to-synthesize associated with e is only applied to concrete
   * arguments. Notice that the conjecture need not be in PBE form for this
   * to be the case. For example, f has examples in:
   *   exists f. f( 1 ) = 3 ^ f( 2 ) = 4
   *   exists f. f( 45 ) > 0 ^ f( 99 ) > 0
   *   exists f. forall x. ( x > 5 => f( 4 ) < x )
   * It does not have examples in:
   *   exists f. forall x. f( x ) > 5
   *   exists f. f( f( 4 ) ) = 5
   * This class implements techniques for functions-to-synthesize that
   * have examples. In particular, the method addSearchVal below can be
   * called.
   */
  bool hasExamples(Node f) const;
  /** get number of examples for enumerator e */
  unsigned getNumExamples(Node f) const;
  /**
   * Get the input arguments for i^th example for function-to-synthesize f,
   * which is added to the vector ex.
   */
  void getExample(Node f, unsigned i, std::vector<Node>& ex) const;
  /** get example terms
   *
   * Add the list of example terms (see d_examplesTerm below) for
   * function-to-synthesize f to the vector exTerms.
   */
  void getExampleTerms(Node f, std::vector<Node>& exTerms) const;
  /**
   * Get the output value of the i^th example for enumerator e, or null if
   * it does not exist (an example does not have an associate output if it is
   * not a top-level equality).
   */
  Node getExampleOut(Node f, unsigned i) const;
  /**
   * Is example output valid? Returns true if all examples are associated
   * with an output value, e.g. they return a non-null value for getExampleOut
   * above.
   */
  bool hasExamplesOut(Node f) const;

 private:
  /** collect the PBE examples in n
   * This is called on the input conjecture, and will populate the above
   * vectors, where hasPol/pol denote the polarity of n in the conjecture. This
   * function returns false if it finds two examples that are contradictory.
   *
   * visited[b] stores the cache of nodes we have visited with (hasPol, pol).
   */
  bool collectExamples(
      Node n,
      std::map<std::pair<bool, bool>,
               std::unordered_set<Node, NodeHashFunction>>& visited,
      bool hasPol,
      bool pol);
  /** Pointer to the sygus term database */
  TermDbSygus* d_tds;
  /** is this an examples conjecture for all functions-to-synthesize? */
  bool d_isExamples;
  /**
   * For each candidate variable f (a function-to-synthesize), whether the
   * conjecture has examples for that function. In other words, all occurrences
   * of f are applied to constants only.
   */
  std::map<Node, bool> d_examples_invalid;
  /**
   * For each function-to-synthesize , whether the conjecture is purely PBE for
   * f. In other words, is the specification for f a set of concrete I/O pairs?
   * An example of a conjecture for which d_examples_invalid is false but
   * d_examplesOut_invalid is true is:
   *   exists f. forall x. ( f( 0 ) > 2 )
   * another example is:
   *   exists f. forall x. f( 0 ) = 2 V f( 3 ) = 3
   * since the formula is not a conjunction (the example values are not
   * entailed). However, the domain of f in both cases is finite, which can be
   * used for search space pruning.
   */
  std::map<Node, bool> d_examplesOut_invalid;
  /**
   * For each function-to-synthesize f, the list of concrete inputs to f.
   */
  std::map<Node, std::vector<std::vector<Node>>> d_examples;
  /**
   * For each function-to-synthesize f, the list of outputs according to the
   * I/O specification for f.
   * The vector d_examplesOut[f] is valid only if d_examplesOut_invalid[f]=true.
   */
  std::map<Node, std::vector<Node>> d_examplesOut;
  /** the list of example terms
   * For example, if exists f. f( 1 ) = 3 ^ f( 2 ) = 4 is our conjecture,
   * this is f( 1 ), f( 2 ).
   */
  std::map<Node, std::vector<Node>> d_examplesTerm;
  /**
   * Map from example input terms to their output, for the example above,
   * this is { f( 0 ) -> 2, f( 5 ) -> 7, f( 6 ) -> 8 }.
   */
  std::map<Node, Node> d_exampleTermMap;
};

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

#endif
