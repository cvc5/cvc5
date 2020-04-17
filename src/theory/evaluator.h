/*********************                                                        */
/*! \file evaluator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The Evaluator class
 **
 ** The Evaluator class can be used to evaluate terms with constant leaves
 ** quickly, without going through the rewriter.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__EVALUATOR_H
#define CVC4__THEORY__EVALUATOR_H

#include <utility>
#include <vector>

#include "base/output.h"
#include "expr/node.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/string.h"

namespace CVC4 {
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
    INVALID
  } d_tag;

  /* Stores the actual result */
  union
  {
    bool d_bool;
    BitVector d_bv;
    Rational d_rat;
    String d_str;
  };

  EvalResult(const EvalResult& other);
  EvalResult() : d_tag(INVALID) {}
  EvalResult(bool b) : d_tag(BOOL), d_bool(b) {}
  EvalResult(const BitVector& bv) : d_tag(BITVECTOR), d_bv(bv) {}
  EvalResult(const Rational& i) : d_tag(RATIONAL), d_rat(i) {}
  EvalResult(const String& str) : d_tag(STRING), d_str(str) {}

  EvalResult& operator=(const EvalResult& other);

  ~EvalResult();

  /**
   * Converts the result to a Node. If the result is not valid, this function
   * returns the null node.
   */
  Node toNode() const;
};

/**
 * The class that performs the actual evaluation of a term under a
 * substitution. Right now, the class does not cache anything between different
 * calls to `eval` but this might change in the future.
 */
class Evaluator
{
 public:
  /**
   * Evaluates node `n` under the substitution described by the variable names
   * `args` and the corresponding values `vals`. This method uses evaluation
   * for subterms that evaluate to constants supported in the EvalResult
   * class and substitution with rewriting for the others.
   *
   * The nodes in the vals must be constant values, that is, they must return
   * true for isConst().
   */
  Node eval(TNode n,
            const std::vector<Node>& args,
            const std::vector<Node>& vals) const;
  /**
   * Same as above, but with a precomputed visited map.
   */
  Node eval(
      TNode n,
      const std::vector<Node>& args,
      const std::vector<Node>& vals,
      const std::unordered_map<Node, Node, NodeHashFunction>& visited) const;

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
  EvalResult evalInternal(
      TNode n,
      const std::vector<Node>& args,
      const std::vector<Node>& vals,
      std::unordered_map<TNode, Node, NodeHashFunction>& evalAsNode,
      std::unordered_map<TNode, EvalResult, TNodeHashFunction>& results) const;
  /** reconstruct
   *
   * This function reconstructs the result of evaluating n using a combination
   * of evaluation results (eresults) and substitution+rewriting (evalAsNode).
   *
   * Arguments eresults and evalAsNode are built within the context of the
   * above method for some args and vals. This method ensures that the return
   * value is equivalent to the rewritten form of n * { args -> vals }.
   */
  Node reconstruct(
      TNode n,
      std::unordered_map<TNode, EvalResult, TNodeHashFunction>& eresults,
      std::unordered_map<TNode, Node, NodeHashFunction>& evalAsNode) const;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__EVALUATOR_H */
