/*********************                                                        */
/*! \file example_eval_cache.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__EXAMPLE_EVAL_CACHE_H
#define CVC4__THEORY__QUANTIFIERS__EXAMPLE_EVAL_CACHE_H

#include "expr/node_trie.h"
#include "theory/quantifiers/sygus/example_infer.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class SynthConjecture;
class TermDbSygus;

/** ExampleEvalCache
 *
 * This class caches the evaluation of nodes on a fixed list of examples. It
 * serves two purposes:
 * (1) To maintain a cache of the results of evaluation of nodes so that
 * evaluation is not recomputed in different contexts, and
 * (2) To maintain a trie of terms indexed by their evaluation on the list
 * of examples to recognize when two terms are equivalent up to examples.
 *
 * This class is associated with a function to synthesize and an enumerator,
 * which determine which examples are taken from the conjecture and how
 * to evaluate builtin terms.
 *
 * The use of (1) is required since we may be interested in computing the
 * evaluation of terms on a fixed set of points P, and reusing it in multiple
 * contexts, including:
 * - Computing whether a term evaluates the same as another one on P,
 * - Computing which I/O pairs a term satisfies (for decision tree learning)
 * whose inputs are P,
 * - Checking whether the term satisfies refinement lemmas where the function
 * to synthesize is solely applied to points in P.
 *
 * A typical use case of (2) is the following.
 * During search, the extension of quantifier-free datatypes procedure for
 * SyGuS datatypes may ask this class whether current candidates can be
 * discarded based on inferring when two candidate solutions are equivalent
 * up to examples. For example, the candidate solutions:
 *     f = \x ite( x < 0, x+1, x ) and f = \x x
 * are equivalent up to examples on a conjecture like:
 *     exists f. f(0) = 1 ^ f(5) = 2 ^ f(6) = 3
 * since they have the same value on the points x = 0,5,6. Hence, we need only
 * consider one of them. The interface for querying this is
 *       ExampleEvalCache::addSearchVal(...).
 * For details, see Reynolds et al. SYNT 2017.
 */
class ExampleEvalCache
{
 public:
  /** Construct this class
   *
   * This initializes this class for function-to-synthesize f and enumerator
   * e. In particular, the terms that will be evaluated by this class
   * are builtin terms that the analog of values taken by enumerator e that
   * is associated with f.
   */
  ExampleEvalCache(TermDbSygus* tds, SynthConjecture* p, Node f, Node e);
  ~ExampleEvalCache();

  /** Add search value
   *
   * This function can be called by the extension of quantifier-free datatypes
   * procedure for SyGuS datatypes or the SyGuS fast enumerator when we are
   * considering a value of enumerator e passed to the constructor of this
   * class whose analog in the signature of builtin theory is bvr.
   * 
   * The type tn passed to this function is the sygus type of the term whose
   * builtin equivalent is bvr. Terms with distinct types must be cached
   * independently since two sygus types may not generate the same terms.
   *
   * This returns either:
   * - A term that is equivalent to bvr up to examples that was passed as the
   * argument to a previous call to addSearchVal, or
   * - bvr, indicating that no previous terms are equivalent to bvr up to
   * examples,
   * - null, indicating that symmetry breaking could not be applied (e.g.
   * if the enumerator of this class is variable agnostic).
   *
   * If this method returns bvr (indicating it is not redundant), the
   * result of the evaluation of bvr is cached by this class, and can be
   * later accessed by evaluateVec below.
   */
  Node addSearchVal(TypeNode tn, Node bvr);
  //----------------------------------- evaluating terms
  /** Evaluate vector
   *
   * This adds to exOut the result of evaluating builtin term bv on the set of
   * examples managed by this class. Term bv is the builtin version of a term
   * generated for enumerator e that is associated with a
   * function-to-synthesize f, which were passed to the constructor of this
   * class. It stores the resulting output for each example in exOut.
   *
   * If doCache is true, the result of the evaluation is cached internally.
   */
  void evaluateVec(Node bv, std::vector<Node>& exOut, bool doCache = false);
  /** evaluate builtin
   *
   * This returns the evaluation of bn on the i^th example for the
   * function-to-synthesis associated with enumerator e. If there are not at
   * least i examples, it returns the rewritten form of bn. For example, if bn =
   * x+5, e is an enumerator for f in the example [EX#1] from SygusPbe, then
   *   evaluateBuiltin( tn, bn, e, 0 ) = 7
   *   evaluateBuiltin( tn, bn, e, 1 ) = 9
   *   evaluateBuiltin( tn, bn, e, 2 ) = 10
   */
  Node evaluate(Node bv, unsigned i) const;
  /** clear evaluation cache for bv */
  void clearEvaluationCache(Node bv);
  /** clear the entire evaluation cache */
  void clearEvaluationAll();
  //----------------------------------- end evaluating terms

 private:
  /** Version of evaluateVec that does not do caching */
  void evaluateVecInternal(Node bv, std::vector<Node>& exOut) const;
  /** Pointer to the sygus term database */
  TermDbSygus* d_tds;
  /** pointer to the example inference class */
  std::vector<std::vector<Node>> d_examples;
  /** The SyGuS type of the enumerator */
  TypeNode d_stn;
  /**
   * Whether we should index search values. This flag is false if the enumerator
   * of this class is variable agnostic.
   */
  bool d_indexSearchVals;
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
  std::map< TypeNode, NodeTrie> d_trie;
  /** cache for evaluate */
  std::map<Node, std::vector<Node>> d_exOutCache;
};

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

#endif
