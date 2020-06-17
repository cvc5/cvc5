/*********************                                                        */
/*! \file extended_rewrite.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief extended rewriting class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H
#define CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H

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
  /** true/false nodes */
  Node d_true;
  Node d_false;
  /** cache that the extended rewritten form of n is ret */
  void setCache(Node n, Node ret);
  /** get the cache for n */
  Node getCache(Node n);
  /** add to children
   *
   * Adds nc to the vector of children, if dropDup is true, we do not add
   * nc if it already occurs in children. This method returns false in this
   * case, otherwise it returns true.
   */
  bool addToChildren(Node nc, std::vector<Node>& children, bool dropDup);

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
  /** Rewrite AND/OR
   *
   * This implements BCP, factoring, and equality resolution for the Boolean
   * term n whose top symbolic is AND/OR.
   */
  Node extendedRewriteAndOr(Node n);
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
  /** (type-independent) factoring, for example:
   *
   *   ( A V B ) ^ ( A V C ) ----> A V ( B ^ C )
   *   ( A ^ B ) V ( A ^ C ) ----> A ^ ( B V C )
   *
   * This function takes as arguments the kinds that specify AND, OR, NOT.
   * We assume that the children of n do not contain duplicates.
   */
  Node extendedRewriteFactoring(Kind andk, Kind ork, Kind notk, Node n);
  /** (type-independent) equality resolution, for example:
   *
   *   ( A V C ) & ( A = B ) ---> ( B V C ) & ( A = B )
   *   ( A V ~B ) & ( A = B ) ----> ( A = B )
   *   ( A V B ) & ( A xor B ) ----> ( A xor B )
   *   ( A & B ) V ( A xor B ) ----> B V ( A xor B )
   *
   * This function takes as arguments the kinds that specify AND, OR, EQUAL,
   * and NOT. The equal kind eqk is interpreted as XOR if isXor is true.
   * It additionally takes as argument a map bcp_kinds, which
   * serves the same purpose as the above function.
   * If this function returns a non-null node ret, then n ---> ret.
   */
  Node extendedRewriteEqRes(Kind andk,
                            Kind ork,
                            Kind eqk,
                            Kind notk,
                            std::map<Kind, bool>& bcp_kinds,
                            Node n,
                            bool isXor = false);
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
   * If usePred is true, we may additionally add n -> true, or n[0] -> false
   * is n is a negation.
   */
  bool inferSubstitution(Node n,
                         std::vector<Node>& vars,
                         std::vector<Node>& subs,
                         bool usePred = false);
  /** extended rewrite
   *
   * Prints debug information, indicating the rewrite n ---> ret was found.
   */
  inline void debugExtendedRewrite(Node n, Node ret, const char* c) const;
  //--------------------------------------end generic utilities

  //--------------------------------------theory-specific top-level calls
  /** extended rewrite arith
   *
   * If this method returns a non-null node ret', then ret is equivalent to
   * ret'.
   */
  Node extendedRewriteArith(Node ret);
  /** extended rewrite strings
   *
   * If this method returns a non-null node ret', then ret is equivalent to
   * ret'.
   */
  Node extendedRewriteStrings(Node ret);
  //--------------------------------------end theory-specific top-level calls
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H */
