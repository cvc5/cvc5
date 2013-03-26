/*********************                                                        */
/*! \file theory_strings_rewriter.h
 ** \verbatim
 ** Original author: tiliang
 ** Major contributors: tiliang
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2013-2013  New York University and The University of Iowa
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

  static RewriteResponse postRewrite(TNode node) {
    Trace("strings-postrewrite") << "Strings::postRewrite start " << node << std::endl;

    Trace("strings-postrewrite") << "Strings::postRewrite returning " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline RewriteResponse preRewrite(TNode node) {
    Trace("strings-prerewrite") << "Strings::preRewrite start " << node << std::endl;

    Trace("strings-prerewrite") << "Strings::preRewrite returning " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}

};/* class TheoryStringsRewriter */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_REWRITER_H */
