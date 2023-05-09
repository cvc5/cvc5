/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Check for some monomial lemmas.
 */

#ifndef CVC5__THEORY__ARITH__NL__EXT__MONOMIAL_CHECK_H
#define CVC5__THEORY__ARITH__NL__EXT__MONOMIAL_CHECK_H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/arith/nl/ext/monomial.h"
#include "theory/theory_inference.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

class ExtState;

class MonomialCheck : protected EnvObj
{
 public:
  MonomialCheck(Env& env, ExtState* data);

  void init(const std::vector<Node>& xts);

  /** check monomial sign
   *
   * Returns a set of valid theory lemmas, based on a
   * lemma schema which ensures that non-linear monomials
   * respect sign information based on their facts.
   * For more details, see Section 5 of "Design Theory
   * Solvers with Extensions" by Reynolds et al., FroCoS 2017,
   * Figure 5, this is the schema "Sign".
   *
   * Examples:
   *
   * x > 0 ^ y > 0 => x*y > 0
   * x < 0 => x*y*y < 0
   * x = 0 => x*y*z = 0
   */
  void checkSign();

  /** check monomial magnitude
   *
   * Returns a set of valid theory lemmas, based on a
   * lemma schema which ensures that comparisons between
   * non-linear monomials respect the magnitude of their
   * factors.
   * For more details, see Section 5 of "Design Theory
   * Solvers with Extensions" by Reynolds et al., FroCoS 2017,
   * Figure 5, this is the schema "Magnitude".
   *
   * Examples:
   *
   * |x|>|y| => |x*z|>|y*z|
   * |x|>|y| ^ |z|>|w| ^ |x|>=1 => |x*x*z*u|>|y*w|
   *
   * Argument c indicates the class of inferences to perform for the
   * (non-linear) monomials in the vector d_ms. 0 : compare non-linear monomials
   * against 1, 1 : compare non-linear monomials against variables, 2 : compare
   * non-linear monomials against other non-linear monomials.
   */
  void checkMagnitude(unsigned c);

 private:
  /** In the following functions, status states a relationship
   * between two arithmetic terms, where:
   * 0 : equal
   * 1 : greater than or equal
   * 2 : greater than
   * -X : (greater -> less)
   * TODO (#1287) make this an enum?
   */
  /** compute the sign of a.
   *
   * Calls to this function are such that :
   *    exp => ( oa = a ^ a <status> 0 )
   *
   * This function iterates over the factors of a,
   * where a_index is the index of the factor in a
   * we are currently looking at.
   *
   * This function returns a status, which indicates
   * a's relationship to 0.
   * We add lemmas to lem of the form given by the
   * lemma schema checkSign(...).
   */
  int compareSign(
      Node oa, Node a, unsigned a_index, int status, std::vector<Node>& exp);
  /** compare monomials a and b
   *
   * Initially, a call to this function is such that :
   *    exp => ( oa = a ^ ob = b )
   *
   * This function returns true if we can infer a valid
   * arithmetic lemma of the form :
   *    P => abs( a ) >= abs( b )
   * where P is true and abs( a ) >= abs( b ) is false in the
   * current model.
   *
   * This function is implemented by "processing" factors
   * of monomials a and b until an inference of the above
   * form can be made. For example, if :
   *   a = x*x*y and b = z*w
   * Assuming we are trying to show abs( a ) >= abs( c ),
   * then if abs( M( x ) ) >= abs( M( z ) ) where M is the current model,
   * then we can add abs( x ) >= abs( z ) to our explanation, and
   * mark one factor of x as processed in a, and
   * one factor of z as processed in b. The number of processed factors of a
   * and b are stored in a_exp_proc and b_exp_proc respectively.
   *
   * cmp_infers stores information that is helpful
   * in discarding redundant inferences.  For example,
   * we do not want to infer abs( x ) >= abs( z ) if
   * we have already inferred abs( x ) >= abs( y ) and
   * abs( y ) >= abs( z ).
   * It stores entries of the form (status,t1,t2)->F,
   * which indicates that we constructed a lemma F that
   * showed t1 <status> t2.
   *
   * We add lemmas to lem of the form given by the
   * lemma schema checkMagnitude(...).
   */
  bool compareMonomial(
      Node oa,
      Node a,
      NodeMultiset& a_exp_proc,
      Node ob,
      Node b,
      NodeMultiset& b_exp_proc,
      std::vector<Node>& exp,
      std::vector<SimpleTheoryLemma>& lem,
      std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers);
  /** helper function for above
   *
   * The difference is the inputs a_index and b_index, which are the indices of
   * children (factors) in monomials a and b which we are currently looking at.
   */
  bool compareMonomial(
      Node oa,
      Node a,
      unsigned a_index,
      NodeMultiset& a_exp_proc,
      Node ob,
      Node b,
      unsigned b_index,
      NodeMultiset& b_exp_proc,
      int status,
      std::vector<Node>& exp,
      std::vector<SimpleTheoryLemma>& lem,
      std::map<int, std::map<Node, std::map<Node, Node> > >& cmp_infers);
  /** Check whether we have already inferred a relationship between monomials
   * x and y based on the information in cmp_infers. This computes the
   * transitive closure of the relation stored in cmp_infers.
   */
  bool cmp_holds(Node x,
                 Node y,
                 std::map<Node, std::map<Node, Node> >& cmp_infers,
                 std::vector<Node>& exp,
                 std::map<Node, bool>& visited);
  /** assign order ids */
  void assignOrderIds(std::vector<Node>& vars,
                      NodeMultiset& d_order,
                      bool isConcrete,
                      bool isAbsolute);
  /** Make literal */
  Node mkLit(Node a, Node b, int status, bool isAbsolute = false) const;
  /** register monomial */
  void setMonomialFactor(Node a, Node b, const NodeMultiset& common);

  /** Basic data that is shared with other checks */
  ExtState* d_data;

  std::map<Node, bool> d_ms_proc;
  // ordering, stores variables and 0,1,-1
  std::map<Node, unsigned> d_order_vars;
  std::vector<Node> d_order_points;

  // list of monomials with factors whose model value is non-constant in model
  //  e.g. y*cos( x )
  std::map<Node, bool> d_m_nconst_factor;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
