/*********************                                                        */
/*! \file theory_strings_rewriter.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

  static void getConcat( Node n, std::vector< Node >& c );
  static Node mkConcat( Kind k, std::vector< Node >& c );
  static Node splitConstant( Node a, Node b, int& index, bool isRev );
};/* class TheoryStringsRewriter */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_REWRITER_H */
