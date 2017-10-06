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
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
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

  static Node rewriteConcatString(TNode node);

  static void mergeInto(std::vector<Node> &t, const std::vector<Node> &s);
  static void shrinkConVec(std::vector<Node> &vec);
  static Node applyAX( TNode node );

  static Node prerewriteConcatRegExp(TNode node);
  static Node prerewriteOrRegExp(TNode node);
  static Node prerewriteAndRegExp(TNode node);
  static Node rewriteMembership(TNode node);

  static bool hasEpsilonNode(TNode node);
public:
  static RewriteResponse postRewrite(TNode node);
  static RewriteResponse preRewrite(TNode node);

  static inline void init() {}
  static inline void shutdown() {}

  /** rewrite contains
  * This is the entry point for post-rewriting terms n of the form str.contains( t )
  * Returns the rewritten form of n.
  *
  * For details on some of the basic rewrites done in this function, see Figure 7 of Reynolds et al
  * "Scaling Up DPLL(T) String Solvers Using Context-Dependent Rewriting" CAV 2017.
  */
  static Node rewriteContains( Node n );
  static Node rewriteIndexof( Node n );
  static Node rewriteReplace( Node n );
  
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
  /** return true if constant c can contain the concat n/list l in order 
      firstc/lastc store which indices were used */
  static bool canConstantContainConcat( Node c, Node n, int& firstc, int& lastc );
  static bool canConstantContainList( Node c, std::vector< Node >& l, int& firstc, int& lastc );
  static Node getNextConstantAt( std::vector< Node >& vec, unsigned& start_index, unsigned& end_index, bool isRev );
  static Node collectConstantStringAt( std::vector< Node >& vec, unsigned& end_index, bool isRev );
  
  /** component contains 
  * This function is used when rewriting str.contains( t1, t2 ), where
  * n1 is the vector form of t1
  * n2 is the vector form of t2
  *
  * if this function returns n>=0 for some n, then 
  *    n1 = { x1...x{n-1} xn...x{n+s} x{n+s+1}...xm }, 
  *    n2 = { y1...ys }, 
  *    y1 is a suffix of xn, 
  *    y2...y{s-1} = x{n+1}...x{n+s-1}, and
  *    ys is a prefix of x{n+s}
  *    if computeRemainder = true, then 
  *      n1 is updated to { x1...x{n-1} xn... x{n+s-1} ys }, and
  *      nr is set to { ( x{n+s} \ ys ) x{n+s+1}...xm }
  *        where ( x{n+s} \ ys ) denotes string remainder (see operator "\" in Section 3.2 of Reynolds et al CAV 2017).
  * otherwise it returns -1.
  *
  * For example:
  * componentContains( { y, "abc", x, "def" }, { "c", x, "de" }, {}, true ) returns 1,
  *   n1 is updated to { y, "abc", x, "de" },
  *   nr is updated to { "f" }
  */
  static int componentContains( std::vector< Node >& n1, std::vector< Node >& n2, std::vector< Node >& nr, bool computeRemainder = false );
  /** strip constant endpoints 
  * This function is used when rewriting str.contains( t1, t2 ), where
  * n1 is the vector form of t1
  * n2 is the vector form of t2
  * 
  * It modifies n1 to a new vector n1' such that:
  * (1) str.contains( str.++( n1 ), str.++( n2 ) ) is equivalent to str.contains( str.++( n1' ), str.++( n2 ) )
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
  * stripConstantEndpoints( { "ab", x, "de" }, { "c" }, {}, {}, 1 ) returns true, 
  *   n1 is updated to { x, "de" }
  *   nb is updated to { "ab" }
  * stripConstantEndpoints( { "ab", x, "de" }, { "bd" }, {}, {}, 0 ) returns true, 
  *   n1 is updated to { "b", x, "d" }
  *   nb is updated to { "a" }
  *   ne is updated to { "e" }
  */
  static bool stripConstantEndpoints( std::vector< Node >& n1, std::vector< Node >& n2, std::vector< Node >& nb, std::vector< Node >& ne, int dir = 0 );
};/* class TheoryStringsRewriter */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_REWRITER_H */
