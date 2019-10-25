/*********************                                                        */
/*! \file theory_strings_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Typing rules for the theory of strings and regexps
 **
 ** Typing rules for the theory of strings and regexps
 **/

#include "cvc4_private.h"
#include "options/strings_options.h"

#ifndef CVC4__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H
#define CVC4__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace strings {

class RegExpRangeTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    if( check ) {
      TNode::iterator it = n.begin();
      unsigned ch[2];

      for(int i=0; i<2; ++i) {
        TypeNode t = (*it).getType(check);
        if (!t.isString()) {
          throw TypeCheckingExceptionPrivate(n, "expecting a string term in regexp range");
        }
        if( (*it).getKind() != kind::CONST_STRING ) {
          throw TypeCheckingExceptionPrivate(n, "expecting a constant string term in regexp range");
        }
        if( (*it).getConst<String>().size() != 1 ) {
          throw TypeCheckingExceptionPrivate(n, "expecting a single constant string term in regexp range");
        }
        unsigned ci = (*it).getConst<String>().front();
        ch[i] = String::convertUnsignedIntToCode(ci);
        ++it;
      }
      if(ch[0] > ch[1]) {
        throw TypeCheckingExceptionPrivate(n, "expecting the first constant is less or equal to the second one in regexp range");
      }
      unsigned maxCh = options::stdPrintASCII() ? 127 : 255;
      if (ch[1] > maxCh)
      {
        std::stringstream ss;
        ss << "expecting characters whose code point is less than or equal to "
           << maxCh;
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
    return nodeManager->regExpType();
  }
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H */
