/*********************                                                        */
/*! \file example_eval_cache.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief 
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__EXAMPLE_EVAL_CACHE_H
#define CVC4__THEORY__QUANTIFIERS__EXAMPLE_EVAL_CACHE_H

#include "theory/quantifiers/sygus/example_infer.h"
#include "expr/node_trie.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SynthConjecture;
class TermDbSygus;

/** ExampleEvalCache
 *
 * A typical use case of this class is the following.
 * During search, the extension of quantifier-free datatypes procedure for
 * SyGuS datatypes may ask this class whether current candidates can be
 * discarded based on inferring when two candidate solutions are equivalent
 * up to examples. For example, the candidate solutions:
 *     f = \x ite( x < 0, x+1, x ) and f = \x x
 * are equivalent up to examples on the above conjecture, since they have
 * the same value on the points x = 0,5,6. Hence, we need only consider one of
 * them. The interface for querying this is
 *       ExampleEvalCache::addSearchVal(...).
 * For details, see Reynolds et al. SYNT 2017.
 */
class ExampleEvalCache
{
 public:
  ExampleEvalCache(TermDbSygus * tds, SynthConjecture* p, Node f, Node e);
  ~ExampleEvalCache();

  /** Add search value
   * 
   * This function is called by the extension of quantifier-free datatypes
   * procedure for SyGuS datatypes or the SyGuS fast enumerator when we are
   * considering a value of enumerator e of sygus type tn whose analog in the
   * signature of builtin theory is bvr.
   *
   * For example, bvr = x + 1 when e is the datatype value Plus( x(), One() )
   * and tn is a sygus datatype that encodes a subsignature of the integers.
   *
   * This returns either:
   * - A term that is equivalent to bvr up to examples
   *   In the above example, it may return a term t of the form
   *   Plus( One(), x() ), such that this function was previously called with t
   *   as input.
   * - bvr, indicating that no previous terms are equivalent to bvr up to
   * examples.
   */
  Node addSearchVal(Node bvr);
  //----------------------------------- evaluating terms
  /** Evaluate vector
   *
   * This adds the result of evaluating bv on the set of input examples managed
   * by this class. Term bv is the builtin version of a term generated for
   * enumerator e that is associated with a function-to-synthesize f.
   * It stores the resulting output for each example in exOut.
   */
  void evaluateVec(Node bv, std::vector<Node>& exOut, bool doCache = false);
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
  Node evaluate(Node bn, unsigned i);
  /** clear evaluation cache */
  void clearEvaluationCache(Node bv);
  //----------------------------------- end evaluating terms

 private:
  /** Version of evaluateVec that does not do caching */
  void evaluateVecInternal(Node bv, std::vector<Node>& exOut);
  /** Pointer to the sygus term database */
  TermDbSygus* d_tds;
  /** pointer to the example inference class */
  std::vector<std::vector<Node>> d_examples;
  /** The SyGuS type of the enumerator */
  TypeNode d_stn;
  /** trie of search values
   * 
   * This trie is an index of candidate solutions for PBE synthesis and their
   * (concrete) evaluation on the set of input examples. For example, if the
   * set of input examples for (x,y) is (0,1), (1,3), then:
   *   term x is indexed by 0,1
   *   term x+y is indexed by 1,4
   *   term 0 is indexed by 0,0.
  * This is used for symmetry breaking in quantifier-free reasoning
  * about SyGuS datatypes.
  */
  NodeTrie d_trie;
  /** cache for evaluate */
  std::map<Node, std::vector<Node>> d_exOutCache;
};

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
