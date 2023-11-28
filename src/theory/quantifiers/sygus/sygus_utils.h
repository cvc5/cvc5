/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generic sygus utilities.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_H

#include <vector>

#include "expr/node.h"
#include "expr/subs.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class SygusUtils
{
 public:
  /**
   * Make (negated) sygus conjecture of the form
   *   forall fs. conj
   * with instantiation attributes in iattrs. Notice that the marker for
   * sygus conjecture is automatically prepended to this list.
   *
   * @param fs The functions
   * @param conj The (negated) conjecture body
   * @param iattrs The attributes of the conjecture. Notice this does not
   * require the "sygus attribute" marker, which is automatically generated
   * by this method.
   */
  static Node mkSygusConjecture(const std::vector<Node>& fs,
                                Node conj,
                                const std::vector<Node>& iattrs);
  /** Same as above, without auxiliary instantiation attributes */
  static Node mkSygusConjecture(const std::vector<Node>& fs, Node conj);

  /**
   * Make conjecture, with a set of solved functions. In particular,
   * solvedf is a substitution of the form { f1 -> t1, ... fn -> tn } where
   * each f1 ... fn are in fs.
   *
   * In the implementation, solutions for solved functions are stored
   * in the instantiation attribute list of the returned conjecture.
   */
  static Node mkSygusConjecture(const std::vector<Node>& fs,
                                Node conj,
                                const Subs& solvedf);
  /**
   * Decompose (negated) sygus conjecture.
   *
   * @param q The (negated) sygus conjecture to decompose, of kind FORALL
   * @param fs The functions-to-synthesize
   * @param unsf The functions that have not been marked as solved.
   * @param solvedf The substitution corresponding to the solved functions.
   *
   * The vector unsf and the domain of solved are a parition of fs.
   */
  static void decomposeSygusConjecture(Node q,
                                       std::vector<Node>& fs,
                                       std::vector<Node>& unsf,
                                       Subs& solvedf);
  /**
   * Decompose the negated body. This takes as input the body of the negated
   * sygus conjecture, which is of the form (NOT (FORALL V G)) or
   * quantifier-free formula G. It returns the conjecture without quantified
   * variables (G), and adds the quantified variables (V) to vs.
   */
  static Node decomposeSygusBody(Node conj, std::vector<Node>& vs);

  /**
   * Set the formal argument list for a function-to-synthesize.
   */
  static void setSygusArgumentList(Node f, const Node& bvl);
  /**
   * Get the formal argument list for a function-to-synthesize. This returns
   * a node of kind BOUND_VAR_LIST that corresponds to the formal argument list
   * of the function to synthesize.
   *
   * Note that if f is constant, then this returns null, since f has no
   * arguments in this case.
   */
  static Node getOrMkSygusArgumentList(Node f);
  /**
   * Same as above, but adds the variables to formals.
   */
  static void getOrMkSygusArgumentList(Node f, std::vector<Node>& formals);
  /**
   * Wrap a solution sol for f in the proper lambda, return the lambda
   * expression. Notice the returned expression is sol itself if f has no
   * formal arguments.
   */
  static Node wrapSolution(Node f, Node sol);

  /**
   * Set the sygus datatype type that encodes the syntax restrictions for
   * function-to-synthesize f.
   */
  static void setSygusType(Node f, const TypeNode& tn);
  /**
   * Get the sygus datatype type that encodes the syntax restrictions for
   * function-to-synthesize f.
   */
  static TypeNode getSygusType(const Node& f);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS__SYGUS_UTILS_H */
