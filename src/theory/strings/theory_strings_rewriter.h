/*********************                                                        */
/*! \file theory_strings_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriter for the theory of strings
 **
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__THEORY_STRINGS_REWRITER_H
#define __CVC4__THEORY__STRINGS__THEORY_STRINGS_REWRITER_H

#include "theory/rewriter.h"
#include "theory/type_enumerator.h"
#include "expr/attribute.h"
#include <climits>

namespace CVC4 {
namespace theory {
namespace strings {

class TheoryStringsRewriter {
private:
  static Node simpleRegexpConsume( std::vector< Node >& mchildren, std::vector< Node >& children, int dir = -1 );
  static bool isConstRegExp( TNode t );
  static bool testConstStringInRegExp( CVC4::String &s, unsigned int index_start, TNode r );

  static void mergeInto(std::vector<Node> &t, const std::vector<Node> &s);
  static void shrinkConVec(std::vector<Node> &vec);
  static Node applyAX( TNode node );

  static Node prerewriteConcatRegExp(TNode node);
  static Node prerewriteOrRegExp(TNode node);
  static Node prerewriteAndRegExp(TNode node);
  static Node rewriteMembership(TNode node);

  static bool hasEpsilonNode(TNode node);
  /** check entail arithmetic internal
   * Returns true if we can show a >= 0 always.
   * a is in rewritten form.
   */
  static bool checkEntailArithInternal(Node a);
  /** return rewrite
   * Called when node rewrites to ret.
   * The string c indicates the justification
   * for the rewrite, which is printed by this
   * function for debugging.
   * This function returns ret.
   */
  static Node returnRewrite(Node node, Node ret, const char* c);

 public:
  static RewriteResponse postRewrite(TNode node);
  static RewriteResponse preRewrite(TNode node);

  static inline void init() {}
  static inline void shutdown() {}
  /** rewrite equality
   *
   * This method returns a formula that is equivalent to the equality between
   * two strings, given by node.
   */
  static Node rewriteEquality(Node node);
  /** rewrite concat
  * This is the entry point for post-rewriting terms node of the form
  *   str.++( t1, .., tn )
  * Returns the rewritten form of node.
  */
  static Node rewriteConcat(Node node);
  /** rewrite substr
  * This is the entry point for post-rewriting terms node of the form
  *   str.substr( s, i1, i2 )
  * Returns the rewritten form of node.
  */
  static Node rewriteSubstr(Node node);
  /** rewrite contains
  * This is the entry point for post-rewriting terms node of the form
  *   str.contains( t, s )
  * Returns the rewritten form of node.
  *
  * For details on some of the basic rewrites done in this function, see Figure
  * 7 of Reynolds et al "Scaling Up DPLL(T) String Solvers Using
  * Context-Dependent Rewriting", CAV 2017.
  */
  static Node rewriteContains(Node node);
  static Node rewriteIndexof(Node node);
  /** rewrite replace
  * This is the entry point for post-rewriting terms n of the form
  *   str.replace( s, t, r )
  * Returns the rewritten form of n.
  */
  static Node rewriteReplace(Node n);
  /** rewrite prefix/suffix
  * This is the entry point for post-rewriting terms n of the form
  *   str.prefixof( s, t ) / str.suffixof( s, t )
  * Returns the rewritten form of n.
  */
  static Node rewritePrefixSuffix(Node n);

  /** gets the "vector form" of term n, adds it to c.
  * For example:
  * when n = str.++( x, y ), c is { x, y }
  * when n = str.++( x, str.++( y, z ), w ), c is { x, str.++( y, z ), w )
  * when n = x, c is { x }
  *
  * Also applies to regular expressions (re.++ above).
  */
  static void getConcat( Node n, std::vector< Node >& c );
  static Node mkConcat( Kind k, std::vector< Node >& c );
  static Node splitConstant( Node a, Node b, int& index, bool isRev );
  /** can constant contain list
   * return true if constant c can contain the list l in order
   * firstc/lastc store which indices in l were used to determine the return
   * value.
   *   (This is typically used when this function returns false, for minimizing
   * explanations)
   *
   * For example:
   *   canConstantContainList( "abc", { x, "c", y } ) returns true
   *     firstc/lastc are updated to 1/1
   *   canConstantContainList( "abc", { x, "d", y } ) returns false
   *     firstc/lastc are updated to 1/1
   *   canConstantContainList( "abcdef", { x, "b", y, "a", z, "c", w } 
   *     returns false
   *     firstc/lastc are updated to 1/3
   *   canConstantContainList( "abcdef", { x, "b", y, "e", z, "c", w } 
   *     returns false
   *     firstc/lastc are updated to 1/5
   */
  static bool canConstantContainList( Node c, std::vector< Node >& l, int& firstc, int& lastc );
  /** can constant contain concat
  * same as above but with n = str.++( l ) instead of l
  */
  static bool canConstantContainConcat(Node c, Node n, int& firstc, int& lastc);
  static Node getNextConstantAt( std::vector< Node >& vec, unsigned& start_index, unsigned& end_index, bool isRev );
  static Node collectConstantStringAt( std::vector< Node >& vec, unsigned& end_index, bool isRev );

  /** strip symbolic length
   *
   * This function strips off components of n1 whose length is less than
   * or equal to argument curr, and stores them in nr. The direction
   * dir determines whether the components are removed from the start
   * or end of n1.
   *
   * In detail, this function updates n1 to n1' such that:
   *   If dir=1,
   *     n1 = str.++( nr, n1' )
   *   If dir=-1
   *     n1 = str.++( n1', nr )
   * It updates curr to curr' such that:
   *   curr' = curr - str.len( str.++( nr ) ), and
   *   curr' >= 0
   * where the latter fact is determined by checkArithEntail.
   *
   * This function returns true if n1 is modified.
   *
   * For example:
   *
   *  stripSymbolicLength( { x, "abc", y }, {}, 1, str.len(x)+1 )
   *    returns true
   *    n1 is updated to { "bc", y }
   *    nr is updated to { x, "a" }
   *    curr is updated to 0   *
   *
   * stripSymbolicLength( { x, "abc", y }, {}, 1, str.len(x)-1 )
   *    returns false
   *
   *  stripSymbolicLength( { y, "abc", x }, {}, 1, str.len(x)+1 )
   *    returns false
   *
   *  stripSymbolicLength( { x, "abc", y }, {}, -1, 2*str.len(y)+4 )
   *    returns true
   *    n1 is updated to { x }
   *    nr is updated to { "abc", y }
   *    curr is updated to str.len(y)+1
   */
  static bool stripSymbolicLength(std::vector<Node>& n1,
                                  std::vector<Node>& nr,
                                  int dir,
                                  Node& curr);
  /** component contains
  * This function is used when rewriting str.contains( t1, t2 ), where
  * n1 is the vector form of t1
  * n2 is the vector form of t2
  *
  * If this function returns n>=0 for some n, then
  *    n1 = { x1...x{n-1} xn...x{n+s} x{n+s+1}...xm },
  *    n2 = { y1...ys },
  *    y1 is a suffix of xn,
  *    y2...y{s-1} = x{n+1}...x{n+s-1}, and
  *    ys is a prefix of x{n+s}
  * Otherwise it returns -1.
  *
  * This function may update n1 if computeRemainder = true.
  *   We maintain the invariant that the resulting value n1'
  *   of n1 after this function is such that:
  *     n1 = str.++( nb, n1', ne )
  * The vectors nb and ne have the following properties.
  * If computeRemainder = true, then
  *   If remainderDir != -1, then
  *     ne is { x{n+s}' x{n+s+1}...xm }
  *     where x{n+s} = str.++( ys, x{n+s}' ).
  *   If remainderDir != 1, then
  *     nb is { x1, ..., x{n-1}, xn' }
  *     where xn = str.++( xn', y1 ).
  *
  * For example:
  *
  * componentContains({ x, "abc", x }, { "b" }, {}, true, 0)
  *   returns 1,
  *   n1 is updated to { "b" },
  *   nb is updated to { x, "a" },
  *   ne is updated to { "c", x }
  *
  * componentContains({ x, "abc", x }, { "b" }, {}, true, 1)
  *   returns 1,
  *   n1 is updated to { x, "ab" },
  *   ne is updated to { "c", x }
  *
  * componentContains({ y, z, "abc", x, "def" }, { "c", x, "de" }, {}, true, 1)
  *   returns 2,
  *   n1 is updated to { y, z, "abc", x, "de" },
  *   ne is updated to { "f" }
  *
  * componentContains({ y, "abc", x, "def" }, { "c", x, "de" }, {}, true, -1)
  *   returns 1,
  *   n1 is updated to { "c", x, "def" },
  *   nb is updated to { y, "ab" }
  */
  static int componentContains(std::vector<Node>& n1,
                               std::vector<Node>& n2,
                               std::vector<Node>& nb,
                               std::vector<Node>& ne,
                               bool computeRemainder = false,
                               int remainderDir = 0);
  /** component contains base
   *
   * This function is a helper for the above function.
   *
   * It returns true if n2 is contained in n1 with the following
   * restrictions:
   *   If dir=1, then n2 must be a suffix of n1.
   *   If dir=-1, then n2 must be a prefix of n1.
   *
   * If computeRemainder is true, then n1rb and n1re are
   * updated such that :
   *   n1 = str.++( n1rb, n2, n1re )
   * where a null value of n1rb and n1re indicates the
   * empty string.
   *
   * For example:
   *
   * componentContainsBase("cabe", "ab", n1rb, n1re, 1, false)
   *   returns false.
   *
   * componentContainsBase("cabe", "ab", n1rb, n1re, 0, true)
   *   returns true,
   *   n1rb is set to "c",
   *   n1re is set to "e".
   *
   * componentContainsBase(y, str.substr(y,0,5), n1rb, n1re, -1, true)
   *   returns true,
   *   n1re is set to str.substr(y,5,str.len(y)).
   */
  static bool componentContainsBase(
      Node n1, Node n2, Node& n1rb, Node& n1re, int dir, bool computeRemainder);
  /** strip constant endpoints
  * This function is used when rewriting str.contains( t1, t2 ), where
  * n1 is the vector form of t1
  * n2 is the vector form of t2
  *
  * It modifies n1 to a new vector n1' such that:
  * (1) str.contains( str.++( n1 ), str.++( n2 ) ) is equivalent to
  * str.contains( str.++( n1' ), str.++( n2 ) )
  * (2) str.++( n1 ) = str.++( nb, n1', ne )
  *
  * "dir" is the direction in which we can modify n1:
  * if dir = 1, then we allow dropping components from the front of n1,
  * if dir = -1, then we allow dropping components from the back of n1,
  * if dir = 0, then we allow dropping components from either.
  *
  * It returns true if n1 is modified.
  *
  * For example:
  * stripConstantEndpoints({ "ab", x, "de" }, { "c" }, {}, {}, 1)
  *   returns true,
  *   n1 is updated to { x, "de" }
  *   nb is updated to { "ab" }
  * stripConstantEndpoints({ "ab", x, "de" }, { "bd" }, {}, {}, 0)
  *   returns true,
  *   n1 is updated to { "b", x, "d" }
  *   nb is updated to { "a" }
  *   ne is updated to { "e" }
  */
  static bool stripConstantEndpoints(std::vector<Node>& n1,
                                     std::vector<Node>& n2,
                                     std::vector<Node>& nb,
                                     std::vector<Node>& ne,
                                     int dir = 0);
  /** check arithmetic entailment equal
   * Returns true if it is always the case that a = b.
   */
  static bool checkEntailArithEq(Node a, Node b);
  /** check arithmetic entailment
   * Returns true if it is always the case that a >= b,
   * and a>b if strict is true.
   */
  static bool checkEntailArith(Node a, Node b, bool strict = false);
  /** check arithmetic entailment
   * Returns true if it is always the case that a >= 0.
   */
  static bool checkEntailArith(Node a, bool strict = false);
  /** get arithmetic lower bound
   * If this function returns a non-null Node ret,
   * then ret is a rational constant and
   * we know that n >= ret always if isLower is true,
   * or n <= ret if isLower is false.
   *
   * Notice the following invariant.
   * If getConstantArithBound(a, true) = ret where ret is non-null, then for
   * strict = { true, false } :
   *   ret >= strict ? 1 : 0
   *     if and only if
   *   checkEntailArith( a, strict ) = true.
   */
  static Node getConstantArithBound(Node a, bool isLower = true);
};/* class TheoryStringsRewriter */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_REWRITER_H */
