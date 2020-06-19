/*********************                                                        */
/*! \file operator_elim.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Operator elimination for arithmetic
 **/

#pragma once

#include <map>

#include "expr/node.h"
#include "theory/logic_info.h"

namespace CVC4 {
namespace theory {
namespace arith {

class OperatorElim
{
 public:
  OperatorElim(const LogicInfo& info);
  ~OperatorElim() {}
  /**
   * Eliminate operators in term n. If n has top symbol that is not a core
   * one (including division, int division, mod, to_int, is_int, syntactic sugar
   * transcendental functions), then we replace it by a form that eliminates
   * that operator. This may involve the introduction of witness terms.
   *
   * One exception to the above rule is that we may leave certain applications
   * like (/ 4 1) unchanged, since replacing this by 4 changes its type from
   * real to int. This is important for some subtyping issues during
   * expandDefinition. Moreover, applications like this can be eliminated
   * trivially later by rewriting.
   *
   * This method is called both during expandDefinition and during ppRewrite.
   *
   * @param n The node to eliminate operators from.
   * @return The (single step) eliminated form of n.
   */
  Node eliminateOperators(Node n);
  /**
   * Recursively ensure that n has no non-standard operators. This applies
   * the above method on all subterms of n.
   *
   * @param n The node to eliminate operators from.
   * @return The eliminated form of n.
   */
  Node eliminateOperatorsRec(Node n);

 private:
  /** Logic info of the owner of this class */
  const LogicInfo& d_info;

  /**
   *  Maps for Skolems for to-integer, real/integer div-by-k, and inverse
   *  non-linear operators that are introduced during ppRewriteTerms.
   */
  std::map<Node, Node> d_to_int_skolem;
  std::map<Node, Node> d_div_skolem;
  std::map<Node, Node> d_int_div_skolem;
  std::map<Node, Node> d_nlin_inverse_skolem;

  /** Arithmetic skolem identifier */
  enum class ArithSkolemId
  {
    /* an uninterpreted function f s.t. f(x) = x / 0.0 (real division) */
    DIV_BY_ZERO,
    /* an uninterpreted function f s.t. f(x) = x / 0 (integer division) */
    INT_DIV_BY_ZERO,
    /* an uninterpreted function f s.t. f(x) = x mod 0 */
    MOD_BY_ZERO,
    /* an uninterpreted function f s.t. f(x) = sqrt(x) */
    SQRT,
  };

  /**
   * Function symbols used to implement:
   * (1) Uninterpreted division-by-zero semantics.  Needed to deal with partial
   * division function ("/"),
   * (2) Uninterpreted int-division-by-zero semantics.  Needed to deal with
   * partial function "div",
   * (3) Uninterpreted mod-zero semantics.  Needed to deal with partial
   * function "mod".
   *
   * If the option arithNoPartialFun() is enabled, then the range of this map
   * stores Skolem constants instead of Skolem functions, meaning that the
   * function-ness of e.g. division by zero is ignored.
   */
  std::map<ArithSkolemId, Node> d_arith_skolem;
  /** get arithmetic skolem
   *
   * Returns the Skolem in the above map for the given id, creating it if it
   * does not already exist.
   */
  Node getArithSkolem(ArithSkolemId asi);
  /** get arithmetic skolem application
   *
   * By default, this returns the term f( n ), where f is the Skolem function
   * for the identifier asi.
   *
   * If the option arithNoPartialFun is enabled, this returns f, where f is
   * the Skolem constant for the identifier asi.
   */
  Node getArithSkolemApp(Node n, ArithSkolemId asi);

  /**
   * Called when a non-linear term n is given to this class. Throw an exception
   * if the logic is linear.
   */
  void checkNonLinearLogic(Node term);
};

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
