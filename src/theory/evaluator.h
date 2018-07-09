/*********************                                                        */
/*! \file evaluator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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

#ifndef __CVC4__THEORY__EVALUATOR_H
#define __CVC4__THEORY__EVALUATOR_H

#include <utility>
#include <vector>

#include "base/output.h"
#include "expr/node.h"
#include "util/bitvector.h"
#include "util/floatingpoint.h"
#include "util/hash.h"
#include "util/rational.h"
#include "util/regexp.h"

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
    ROUNDINGMODE,
    FLOATINGPOINT,
    RATIONAL,
    STRING,
    INVALID
  } d_tag;

  /* Stores the actual result */
  union
  {
    bool d_bool;
    BitVector d_bv;
    RoundingMode d_rm;
    FloatingPoint d_fp;
    Rational d_rat;
    String d_str;
  };

  EvalResult(const EvalResult& other);
  EvalResult() : d_tag(INVALID) {}
  EvalResult(bool b) : d_tag(BOOL), d_bool(b) {}
  EvalResult(const BitVector& bv) : d_tag(BITVECTOR), d_bv(bv) {}
  EvalResult(const RoundingMode& rm) : d_tag(ROUNDINGMODE), d_rm(rm) {}
  EvalResult(const FloatingPoint& fp) : d_tag(FLOATINGPOINT), d_fp(fp) {}
  EvalResult(const Rational& r) : d_tag(RATIONAL), d_rat(r) {}
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
   * `args` and the corresponding values `vals`. The function returns a null
   * node if there is a subterm that is not constant under the substitution or
   * if an operator is not supported by the evaluator.
   *
   * Note: The evaluator expects that `n` has been rewritten to the point where
   * it does not contain non-essential operators (e.g. FLOATINGPOINT_EQ).
   */
  Node eval(TNode n,
            const std::vector<Node>& args,
            const std::vector<Node>& vals);

 private:
  /**
   * Evaluates node `n` under the substitution described by the variable names
   * `args` and the corresponding values `vals`. The internal version returns
   * an EvalResult which has slightly less overhead for recursive calls. The
   * function returns an invalid result if there is a subterm that is not
   * constant under the substitution or if an operator is not supported by the
   * evaluator.
   */
  EvalResult evalInternal(TNode n,
                          const std::vector<Node>& args,
                          const std::vector<Node>& vals);
};

}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__EVALUATOR_H */
