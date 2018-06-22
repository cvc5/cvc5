/*********************                                                        */
/*! \file evaluator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
  // Describes which type of result is being stored
  enum
  {
    BOOL,
    BITVECTOR,
    RATIONAL,
    STRING,
    INVALID
  } d_tag;

  // Stores the actual result
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

class Evaluator
{
 public:
  /**
   * Evaluates node `n` under the substitution described by the variable names
   * `args` and the corresponding values `vals`.
   */
  Node eval(TNode n,
            const std::vector<Node>& args,
            const std::vector<Node>& vals);

 private:
  /**
   * Evaluates node `n` under the substitution described by the variable names
   * `args` and the corresponding values `vals`. The internal version returns
   * an EvalResult which has slightly less overhead for recursive calls.
   */
  EvalResult evalInternal(TNode n,
                          const std::vector<Node>& args,
                          const std::vector<Node>& vals);
};

}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__EVALUATOR_H */
