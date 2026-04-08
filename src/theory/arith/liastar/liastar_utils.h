/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for liastar extension.
 */

#ifndef CVC5__THEORY__LIASTAR__UTILS_H
#define CVC5__THEORY__LIASTAR__UTILS_H

#ifdef CVC5_USE_NORMALIZ

#include "expr/node.h"
#include "smt/env.h"
#include "theory/arith/linear/normal_form.h"
#include "util/result.h"
namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

typedef mpz_class Integer;

class LiaStarUtils
{
 public:
  /**
   * @param n a node of the form
   * (int.star-contains (lambda ((x_1 Int) ... (x_n Int)) p) (y_1 ... y_n))
   * @return <(p y_1 ... y_n), (and (>= y_1 0) ... (>= y_n 0))>
   */
  static std::pair<Node, Node> getVectorPredicate(Node n, NodeManager* nm);
  /**
   * @param a node in LIA that only contains =, >=, ite in its tree
   * @return a node in DNF where ite and = are eliminated
   */
  static Node toDNF(Node n, Env* e);

  /**
   * @param a node in LIA that only contains =, >=, ite in its tree
   * @return an equivalent node that does not contain ite expressions
   * without introducing new variables
   */
  static Node removeItes(Node n, Env* e);

  static Node distribute(Node n, Env* e);

  static Result areAssertionsUnsat(const std::vector<Node>& assertions, Env* e);

  static Result cvc5CheckSat(const std::vector<Node>& freeVariables,
                             Node assertion,
                             Env* e);
  static Result normalizCheckSat(Node variables, Node assertion);

  /**
   * This function returns a list of matrices representing cones (disjunctions)
   * where the rows of each matrix are constraints of the form a1 x_1 + ... +
   * an_xn + b >= 0
   * @param variables is a node of Kind BOUND_VAR_LIST
   * @param predicate is a LIA predicate in DNF format
   */
  static std::vector<std::pair<std::vector<std::string>, Node>> getMatrices(
      Node variables, Node n);

 private:
  static std::vector<std::pair<Node, Node>> removeIntegerItes(Node n, Env* e);
  static Node removeNot(Node n, Env* e);
  static Node recursiveFlatten(NodeManager* nm, Node n);
  static std::string getString(Node variables, linear::Polynomial& p);
};
}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__LIASTAR__UTILS_H */

#endif /* CVC5_USE_NORMALIZ */