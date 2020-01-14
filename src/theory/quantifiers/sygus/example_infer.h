/*********************                                                        */
/*! \file example_infer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__EXAMPLE_INFER_H
#define CVC4__THEORY__QUANTIFIERS__EXAMPLE_INFER_H

#include "context/cdhashmap.h"
#include "theory/quantifiers/sygus/sygus_module.h"
#include "theory/quantifiers/sygus/sygus_unif_io.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Example Inference
 */
class ExampleInfer
{
 public:
  ExampleInfer();
  ~ExampleInfer();
  /** initialize */
  void initialize(Node conj,
                  Node n,
                  const std::vector<Node>& candidates);
  /** does the conjecture have examples for all candidates? */
  bool isExamples() { return d_isExamples; }
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
  bool hasExamples(Node e);
  /** get number of examples for enumerator e */
  unsigned getNumExamples(Node e);
  /**
   * Get the input arguments for i^th example for e, which is added to the
   * vector ex
   */
  void getExample(Node e, unsigned i, std::vector<Node>& ex);
  /**
   * Get the output value of the i^th example for enumerator e, or null if
   * it does not exist (an example does not have an associate output if it is
   * not a top-level equality).
   */
  Node getExampleOut(Node e, unsigned i);
  //----------------------------------- evaluating terms
  /** evaluate node */
  void evaluate(Node e, Node bv, std::vector<Node>& exOut, bool doCache=false);
  /** clear evaluation cache */
  void clearEvaluationCache(Node e, Node bv);
  //----------------------------------- end evaluating terms
 private:
  /** is this an examples conjecture for all functions-to-synthesize? */
  bool d_isExamples;
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
};

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
