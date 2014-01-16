/*********************                                                        */
/*! \file theory_strings_rewriter.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

namespace CVC4 {
namespace theory {
namespace strings {

class TheoryStringsRewriter {
public:
  static bool checkConstRegExp( TNode t );
  static bool testConstStringInRegExp( CVC4::String &s, unsigned int index_start, TNode r );

  static Node rewriteConcatString(TNode node);
  static Node prerewriteConcatRegExp(TNode node);
  static Node prerewriteOrRegExp(TNode node);
  static Node rewriteMembership(TNode node);

  static RewriteResponse postRewrite(TNode node);

  static RewriteResponse preRewrite(TNode node);

  static inline void init() {}
  static inline void shutdown() {}

};/* class TheoryStringsRewriter */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_REWRITER_H */
