/*********************                                                        */
/*! \file extended_rewrite.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief extended rewriting class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H
#define __CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H

#include <unordered_map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Extended rewriter
 *
 * This class is used for all rewriting that is not necessarily
 * helpful for quantifier-free solving, but is helpful
 * in other use cases. An example of this is SyGuS, where rewriting
 * can be used for generalizing refinement lemmas, and hence
 * should be highly aggressive.
 *
 * This class extended the standard techniques for rewriting
 * with techniques, including but not limited to:
 * - Redundant child elimination,
 * - Sorting children of commutative operators,
 * - Boolean constraint propagation,
 * - Equality chain normalization,
 * - Negation normal form,
 * - Simple ITE pulling,
 * - ITE conditional variable elimination,
 * - ITE condition subsumption.
 */
class ExtendedRewriter
{
 public:
  ExtendedRewriter(bool aggr = true);
  ~ExtendedRewriter() {}
  /** return the extended rewritten form of n */
  Node extendedRewrite(Node n);

 private:
  /**
   * Whether this extended rewriter applies aggressive rewriting techniques,
   * which are more expensive. Examples of aggressive rewriting include:
   * - conditional rewriting,
   * - condition merging,
   * - sorting childing of commutative operators with more than 5 children.
   *
   * Aggressive rewriting is applied for SyGuS, whereas non-aggressive rewriting
   * may be applied as a preprocessing step.
   */
  bool d_aggr;
  /** cache that the extended rewritten form of n is ret */
  void setCache(Node n, Node ret);

  //--------------------------------------generic utilities
  /** Rewrite ITE, for example:
   *
   * ite( ~C, s, t ) ---> ite( C, t, s )
   * ite( A or B, s, t ) ---> ite( ~A and ~B, t, s )
   * ite( x = c, x, t ) --> ite( x = c, c, t )
   * t * { x -> c } = s => ite( x = c, s, t ) ---> t
   *
   * The parameter "full" indicates an effort level that this rewrite will
   * take. If full is false, then we do only perform rewrites that
   * strictly decrease the term size of n.
   */
  Node extendedRewriteIte(Kind itek, Node n, bool full = true);
  /** Pull ITE, for example:
   *
   *   D=C2 ---> false
   *     implies
   *   D=ite( C, C1, C2 ) --->  C ^ D=C1
   *
   *   f(t,t1) --> s  and  f(t,t2)---> s
   *     implies
   *   f(t,ite(C,t1,t2)) ---> s
   *
   * If this function returns a non-null node ret, then n ---> ret.
   */
  Node extendedRewritePullIte(Kind itek, Node n);
  /** Negation Normal Form (NNF), for example:
   *
   *   ~( A & B ) ---> ( ~ A | ~B )
   *   ~( ite( A, B, C ) ---> ite( A, ~B, ~C )
   *
   * If this function returns a non-null node ret, then n ---> ret.
   */
  Node extendedRewriteNnf(Node n);
  /** (type-independent) Boolean constraint propagation, for example:
   *
   *   ~A & ( B V A ) ---> ~A & B
   *   A & ( B = ( A V C ) ) ---> A & B
   *
   * This function takes as arguments the kinds that specify AND, OR, and NOT.
   * It additionally takes as argument a map bcp_kinds. If this map is
   * non-empty, then all terms that have a Kind that is *not* in this map should
   * be treated as immutable. This is for instance to prevent propagation
   * beneath illegal terms. As an example:
   *   (bvand A (bvor A B)) is equivalent to (bvand A (bvor 1...1 B)), but
   *   (bvand A (bvplus A B)) is not equivalent to (bvand A (bvplus 1..1 B)),
   * hence, when using this function to do BCP for bit-vectors, we have that
   * BITVECTOR_AND is a bcp_kind, but BITVECTOR_PLUS is not.
   *
   * If this function returns a non-null node ret, then n ---> ret.
   */
  Node extendedRewriteBcp(
      Kind andk, Kind ork, Kind notk, std::map<Kind, bool>& bcp_kinds, Node n);
  /** (type-independent) Equality chain rewriting, for example:
   *
   *   A = ( A = B ) ---> B
   *   ( A = D ) = ( C = B ) ---> A = ( B = ( C = D ) )
   *   A = ( A & B ) ---> ~A | B
   *
   * If this function returns a non-null node ret, then n ---> ret.
   * This function takes as arguments the kinds that specify EQUAL, AND, OR,
   * and NOT. If the flag isXor is true, the eqk is treated as XOR.
   */
  Node extendedRewriteEqChain(
      Kind eqk, Kind andk, Kind ork, Kind notk, Node n, bool isXor = false);
  /** extended rewrite aggressive
   *
   * All aggressive rewriting techniques (those that should be prioritized
   * at a lower level) go in this function.
   */
  Node extendedRewriteAggr(Node n);
  /** Decompose right associative chain
   *
   * For term f( ... f( f( base, tn ), t{n-1} ) ... t1 ), returns term base, and
   * appends t1...tn to children.
   */
  Node decomposeRightAssocChain(Kind k, Node n, std::vector<Node>& children);
  /** Make right associative chain
   *
   * Sorts children to obtain list { tn...t1 }, and returns the term
   * f( ... f( f( base, tn ), t{n-1} ) ... t1 ).
   */
  Node mkRightAssocChain(Kind k, Node base, std::vector<Node>& children);
  /** Partial substitute
   *
   * Applies the substitution specified by assign to n, recursing only beneath
   * terms whose Kind appears in rec_kinds.
   */
  Node partialSubstitute(Node n,
                         std::map<Node, Node>& assign,
                         std::map<Kind, bool>& rkinds);
  /** solve equality
   *
   * If this function returns a non-null node n', then n' is equivalent to n
   * and is of the form that can be used by inferSubstitution below.
   */
  Node solveEquality(Node n);
  /** infer substitution
   *
   * If n is an equality of the form x = t, where t is either:
   * (1) a constant, or
   * (2) a variable y such that x < y based on an ordering,
   * then this method adds x to vars and y to subs and return true, otherwise
   * it returns false.
   */
  bool inferSubstitution(Node n,
                         std::vector<Node>& vars,
                         std::vector<Node>& subs);
  /** extended rewrite
   *
   * Prints debug information, indicating the rewrite n ---> ret was found.
   */
  inline void debugExtendedRewrite(Node n, Node ret, const char* c) const;
  //--------------------------------------end generic utilities

  //--------------------------------------theory-specific top-level calls
  /** extended rewrite arith */
  Node extendedRewriteArith(Node ret, bool& pol);
  //--------------------------------------end theory-specific top-level calls
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H */
