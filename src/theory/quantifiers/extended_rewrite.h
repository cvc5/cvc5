/*********************                                                        */
/*! \file extended_rewrite.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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
  Node extendedRewriteArith(Node ret);
  /** extended rewrite bv */
  Node extendedRewriteBv(Node ret);
  //--------------------------------------end theory-specific top-level calls

  //--------------------------------------bit-vectors
  /** bitvector subsume
   *
   * If this function returns 1, then a's 1 bits are a superset of b's 1 bits,
   * in other words, (bvand (bvnot a) b) = 0 holds.
   *
   * If this function returns 2, then additionally at least one bit of a
   * is 1 that is 0 in bit, that is (bvand a (bvnot b)) != 0 holds.
   *
   * Otherwise, this function returns 0.
   *
   * If strict is false, then this function will only return 0 or 1.
   *
   * If tryNot is true, we will try to show the subsumption by calling
   * bitVectorSubsume( ~b, ~a ).
   */
  int bitVectorSubsume(Node a, Node b, bool strict = false, bool tryNot = true);
  /** bitvector arithmetic compare
   *
   * If this function returns 1, then bvuge( a, b ) holds.
   *
   * If this function returns 2, then bvugt( a, b ) holds.
   *
   * Otherwise this function returns 0.
   *
   * If strict is false, then this function will only return 0 or 1.
   */
  int bitVectorArithComp(Node a, Node b, bool strict = false);
  /** bitvector disjoint
   *
   * Returns true if there are no bits where a and b are both 1.
   * That is, if this function returns true, then
   *   (bvand a b) = 0.
   * Note that this function is equivalent to
   *   bitvectorSubsume( ~a, b ) && bitvectorSubsume( ~b, a ).
   */
  bool bitVectorDisjoint(Node a, Node b);

  /** mk const as the same type as n, 0 if !isNot, 1s if isNot */
  Node mkConstBv(Node n, bool isNot);
  /** is const bv zero
   *
   * Returns true if n is constant 0..0 and isNot = false,
   * Returns true if n is constant 1..1 and isNot = true,
   * return false otherwise.
   */
  bool isConstBv(Node n, bool isNot);
  /** get const child 
   * 
   * Returns the constant child of n if it has one, and adds all the
   * non-constant children of n to nconst.
   */
  Node getConstBvChild(Node n, std::vector<Node>& nconst);
  /** has const child 
   * 
   * Returns true iff n has a constant child.
   */
  bool hasConstBvChild(Node n);
  /** rewrite bit-vector arithmetic 
   * 
   * This is the entry point for rewriting nodes ret of the form (bvadd ...) or
   * (bvmul ...). It returns the rewritten form of ret, or null to indicate
   * ret is not rewritten.
   */
  Node rewriteBvArith(Node ret);
  /** rewrite bit-vector shift 
   * 
   * This is the entry point for rewriting nodes ret of the form (bvlshr n1 n2)
   * or (bvshl n1 n2). It returns the rewritten form of ret, or null to indicate
   * ret is not rewritten.
   */
  Node rewriteBvShift(Node ret);
  /** rewrite bit-vector shift 
   * 
   * This is the entry point for rewriting nodes ret of the form (bvand n1 n2)
   * or (bvor n1 n2). It returns the rewritten form of ret, or null to indicate
   * ret is not rewritten.
   */
  Node rewriteBvBool(Node ret);
  /** normalize bit-vector monomial
   * 
   * This converts n to a bitvector monomial representation, subsequently
   * performs aggressive factoring techniques, and returns the resulting
   * node from the (simplified) monomial, using the below two methods.
   */
  Node normalizeBvMonomial(Node n);
  /** get bit-vector monomial sum 
   * 
   * This constructs the monomial sum map msum that is equivalent to n. A
   * monomial sum map is a way of representing bit-vector arithmetic terms.
   * For example, the term bvadd( bvmul(#x0002,x), y, #x0004 ) is represented
   * as map:
   *   x -> #x0002
   *   y -> #x0001
   *   #x0001 -> #x0004
   * 
   * This method aggressively tries to infer when a node can be expressed as
   * a monomial, for example bvneg, bvnot, concat, and bvshl can often be
   * treated as special cases of addition and multiplication. For example,
   * given input bvshl(x,#x0003), this method will return the monomial sum:
   *   x -> #x0008
   * since bvshl(x,#x0003) is equivalent to bvmul(#x0008,x).
   */
  void getBvMonomialSum(Node n, std::map<Node, Node>& msum);
  /** make node from bit-vector monomial
   * 
   * This returns the bit-vector node of the same bit-width as n corresponding
   * to the monomial sum msum.
   */
  Node mkNodeFromBvMonomial(Node n, std::map<Node, Node>& msum);
  /** splice
   *
   * Adds k (non-concat) terms to n1v and n2v such that:
   *   n1 is equivalent to n1v[0] ++ ... ++ n1v[k-1] and
   *   n2 is equivalent to n2v[0] ++ ... ++ n2v[k-1],
   * and n1v[i] and n2v[i] have equal width for i=0...k-1.
   */
  void spliceBv(Node n1,
                Node n2,
                std::vector<Node>& n1v,
                std::vector<Node>& n2v);
  /** splice bv to constant bit
   *
   * If the return value of this method is a non-negative value i, it adds k
   * terms to nv such that:
   *   n1 is equivalent to nv[0] ++ ... ++ nv[i] ++ ... ++ nv[k-1],
   *   n2 is equivalent to nv[0] ++ ... ++ (~)nv[i] ++ ... ++ nv[k-1], and
   *   nv[i] is a constant of bit-width one.
   */
  int spliceBvConstBit(Node n1, Node n2, std::vector<Node>& nv);
  /** extend bit-vector
   *
   * This returns the concatentation node of the form
   *   concat( ((_ extract s1 e1) n) ... ((_ extract sn en) n))
   * where s1 = bitwidth(n)-1, s_{i+1} = e_i - 1 for each i=2,...n,
   * and for each i in the domain of ex_map, ex_map[i] is
   * ((_ extract sj ej) n) for some 1<=j<=n, and i=sj. 
   * 
   * For example, if
   *   ex_map = { 4 -> ((_ extract 4 2) n) } and bitwidth( n ) = 32
   * then this method returns
   *   (concat ((_ extract 31 5) n) ((_ extract 4 2) n) ((_ extract 1 0) n))
   */
  Node extendBv(Node n, std::map<unsigned, Node>& ex_map);
  /** extend bit-vector
   * 
   * The vector exs is a vector of non-overlapping extracts of n. This
   * calls the above function, mapping the high bits of each extract term t
   * in exts to t.
   */
  Node extendBv(Node n, std::vector<Node>& exs);
  //--------------------------------------end bit-vectors
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__EXTENDED_REWRITE_H */
