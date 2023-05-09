/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The Evaluator class.
 *
 * The Evaluator class can be used to evaluate terms with constant leaves
 * quickly, without going through the rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__EVALUATOR_H
#define CVC5__THEORY__EVALUATOR_H

#include <utility>
#include <vector>

#include "base/output.h"
#include "expr/node.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/string.h"
#include "util/uninterpreted_sort_value.h"

namespace cvc5::internal {
namespace theory {

/**
 * Struct that holds the result of an evaluation. The actual value is stored in
 * a union to avoid the overhead of a class hierarchy with virtual methods.
 */
struct EvalResult
{
  /* Describes which type of result is being stored */
  enum
  {
    BOOL,
    BITVECTOR,
    RATIONAL,
    STRING,
    UVALUE,
    INVALID
  } d_tag;

  /* Stores the actual result */
  union
  {
    bool d_bool;
    BitVector d_bv;
    Rational d_rat;
    String d_str;
    UninterpretedSortValue d_av;
  };

  EvalResult(const EvalResult& other);
  EvalResult() : d_tag(INVALID) {}
  EvalResult(bool b) : d_tag(BOOL), d_bool(b) {}
  EvalResult(const BitVector& bv) : d_tag(BITVECTOR), d_bv(bv) {}
  EvalResult(const Rational& i) : d_tag(RATIONAL), d_rat(i) {}
  EvalResult(const String& str) : d_tag(STRING), d_str(str) {}
  EvalResult(const UninterpretedSortValue& av) : d_tag(UVALUE), d_av(av) {}

  EvalResult& operator=(const EvalResult& other);

  ~EvalResult();

  /**
   * Converts the result to a Node. If the result is not valid, this function
   * returns the null node. This method takes a type to distinguish integer
   * and real constants, which are both represented as RATIONAL results.
   */
  Node toNode(const TypeNode& tn) const;
};

class Rewriter;

/**
 * The class that performs the actual evaluation of a term under a
 * substitution. Right now, the class does not cache anything between different
 * calls to `eval` but this might change in the future.
 */
class Evaluator
{
 public:
  /**
   * @param rr (optional) the rewriter to use when a node cannot be evaluated.
   * @param strAlphaCard The assumed cardinality of the alphabet for strings.
   */
  Evaluator(Rewriter* rr, uint32_t strAlphaCard = 196608);
  /**
   * Evaluates node `n` under the substitution described by the variable names
   * `args` and the corresponding values `vals`. This method uses evaluation
   * for subterms that evaluate to constants supported in the EvalResult
   * class and substitution with rewriting for the others.
   *
   * The nodes in vals are typically intended to be constant, although this
   * is not required.
   *
   * If the parameter useRewriter is true, then we may invoke calls to the
   * rewriter for computing the result of this method.
   *
   * The result of this call is either equivalent to:
   * (1) rewrite(n.substitute(args,vars))
   * (2) Node::null().
   * If d_rr is non-null, then we are always in the first case. If
   * useRewriter is null, then we may be in case (2) if computing the
   * rewritten, substituted form of n could not be determined by evaluation.
   */
  Node eval(TNode n,
            const std::vector<Node>& args,
            const std::vector<Node>& vals) const;
  /**
   * Same as above, but with a precomputed visited map.
   */
  Node eval(TNode n,
            const std::vector<Node>& args,
            const std::vector<Node>& vals,
            const std::unordered_map<Node, Node>& visited) const;

 private:
  /**
   * Evaluates node `n` under the substitution described by the variable names
   * `args` and the corresponding values `vals`. The internal version returns
   * an EvalResult which has slightly less overhead for recursive calls.
   *
   * The method returns an invalid EvalResult if the result of the substitution
   * on n does not result in a constant value that is one of those supported in
   * the EvalResult class. Notice that e.g. datatype constants are not supported
   * in this class.
   *
   * This method additionally adds subterms of n that could not be evaluated
   * (in the above sense) to the map evalAsNode. For each such subterm n', we
   * store the node corresponding to the result of applying the substitution
   * `args` to `vals` and rewriting. Notice that this map contains an entry
   * for n in the case that it cannot be evaluated.
   */
  EvalResult evalInternal(TNode n,
                          const std::vector<Node>& args,
                          const std::vector<Node>& vals,
                          std::unordered_map<TNode, Node>& evalAsNode,
                          std::unordered_map<TNode, EvalResult>& results) const;
  /** reconstruct
   *
   * This function reconstructs the result of evaluating n using a combination
   * of evaluation results (eresults) and substitution+rewriting (evalAsNode).
   *
   * Arguments eresults and evalAsNode are built within the context of the
   * above method for some args and vals. This method ensures that the return
   * value is equivalent to the rewritten form of n * { args -> vals }.
   */
  Node reconstruct(TNode n,
                   std::unordered_map<TNode, EvalResult>& eresults,
                   std::unordered_map<TNode, Node>& evalAsNode) const;
  /**
   * Process unhandled, called when n cannot be evaluated. This updates
   * evalAsNode and results with the proper entries for this case. The term
   * nv is the (Node) value of n if it exists, otherwise if needsReconstruct
   * is true, the value of n is reconstructed based on evalAsNode and results.
   */
  void processUnhandled(TNode n,
                        TNode nv,
                        std::unordered_map<TNode, Node>& evalAsNode,
                        std::unordered_map<TNode, EvalResult>& results,
                        bool needsReconstruct) const;
  /** The (optional) rewriter to be used */
  Rewriter* d_rr;
  /** The cardinality of the alphabet of strings */
  uint32_t d_alphaCard;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__EVALUATOR_H */
