/*********************                                                        */
/*! \file theory_strings_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tianyi Liang, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Typing and cardinality rules for the theory of arrays
 **
 ** Typing and cardinality rules for the theory of arrays.
 **/

#include "cvc4_private.h"
#include "options/strings_options.h"

#ifndef __CVC4__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H
#define __CVC4__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace strings {

class StringConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    return nodeManager->stringType();
  }
};

class StringConcatTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ){
      TNode::iterator it = n.begin();
      TNode::iterator it_end = n.end();
      int size = 0;
      for (; it != it_end; ++ it) {
       TypeNode t = (*it).getType(check);
       if (!t.isString()) {
         throw TypeCheckingExceptionPrivate(n, "expecting string terms in string concat");
       }
       ++size;
      }
      if(size < 2) {
        throw TypeCheckingExceptionPrivate(n, "expecting at least 2 terms in string concat");
      }
    }
    return nodeManager->stringType();
  }
};

class StringLengthTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting string terms in string length");
      }
    }
    return nodeManager->integerType();
  }
};

class StringSubstrTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in substr");
      }
      t = n[1].getType(check);
      if (!t.isInteger()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a start int term in substr");
      }
      t = n[2].getType(check);
      if (!t.isInteger()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a length int term in substr");
      }
    }
    return nodeManager->stringType();
  }
};

class StringContainTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting an original string term in string contain");
      }
      t = n[1].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a target string term in string contain");
      }
    }
    return nodeManager->booleanType();
  }
};

class StringCharAtTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string char at 0");
      }
      t = n[1].getType(check);
      if (!t.isInteger()) {
        throw TypeCheckingExceptionPrivate(n, "expecting an integer term in string char at 1");
      }
    }
    return nodeManager->stringType();
  }
};

class StringIndexOfTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string indexof 0");
      }
      t = n[1].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string indexof 1");
      }
      t = n[2].getType(check);
      if (!t.isInteger()) {
        throw TypeCheckingExceptionPrivate(n, "expecting an integer term in string indexof 2");
      }
    }
    return nodeManager->integerType();
  }
};

class StringReplaceTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string replace 0");
      }
      t = n[1].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string replace 1");
      }
      t = n[2].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string replace 2");
      }
    }
    return nodeManager->stringType();
  }
};

class StringPrefixOfTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string prefixof 0");
      }
      t = n[1].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string prefixof 1");
      }
    }
    return nodeManager->booleanType();
  }
};

class StringSuffixOfTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string suffixof 0");
      }
      t = n[1].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string suffixof 1");
      }
    }
    return nodeManager->booleanType();
  }
};

class StringIntToStrTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isInteger()) {
        throw TypeCheckingExceptionPrivate(n, "expecting an integer term in int to string 0");
      }
    }
    return nodeManager->stringType();
  }
};

class StringStrToIntTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a string term in string to int 0");
      }
    }
    return nodeManager->integerType();
  }
};

class RegExpConstantTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    return nodeManager->regExpType();
  }
};

class RegExpConcatTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TNode::iterator it = n.begin();
      TNode::iterator it_end = n.end();
      int size = 0;
      for (; it != it_end; ++ it) {
         TypeNode t = (*it).getType(check);
         if (!t.isRegExp()) {
           throw TypeCheckingExceptionPrivate(n, "expecting regexp terms in regexp concat");
         }
         ++size;
      }
      if(size < 2) {
         throw TypeCheckingExceptionPrivate(n, "expecting at least 2 terms in regexp concat");
      }
    }
    return nodeManager->regExpType();
  }
};

class RegExpUnionTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TNode::iterator it = n.begin();
      TNode::iterator it_end = n.end();
      for (; it != it_end; ++ it) {
         TypeNode t = (*it).getType(check);
         if (!t.isRegExp()) {
           throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
         }
      }
    }
    return nodeManager->regExpType();
  }
};

class RegExpInterTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TNode::iterator it = n.begin();
      TNode::iterator it_end = n.end();
      for (; it != it_end; ++ it) {
       TypeNode t = (*it).getType(check);
       if (!t.isRegExp()) {
         throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
       }
      }
    }
    return nodeManager->regExpType();
  }
};

class RegExpStarTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isRegExp()) {
        throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
      }
    }
    return nodeManager->regExpType();
  }
};

class RegExpPlusTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isRegExp()) {
        throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
      }
    }
    return nodeManager->regExpType();
  }
};

class RegExpOptTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isRegExp()) {
        throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
      }
    }
    return nodeManager->regExpType();
  }
};

class RegExpRangeTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TNode::iterator it = n.begin();
      unsigned char ch[2];

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
        ch[i] = (*it).getConst<String>().getFirstChar();
        ++it;
      }
      if(ch[0] > ch[1]) {
        throw TypeCheckingExceptionPrivate(n, "expecting the first constant is less or equal to the second one in regexp range");
      }
      if(options::stdASCII() && ch[1] > '\x7f') {
        throw TypeCheckingExceptionPrivate(n, "expecting standard ASCII characters in regexp range, or please set the option strings-std-ascii to be false");
      }
    }
    return nodeManager->regExpType();
  }
};

class RegExpLoopTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TNode::iterator it = n.begin();
      TNode::iterator it_end = n.end();
      TypeNode t = (*it).getType(check);
      if (!t.isRegExp()) {
        throw TypeCheckingExceptionPrivate(n, "expecting a regexp term in regexp loop 1");
      }
      ++it; t = (*it).getType(check);
      if (!t.isInteger()) {
        throw TypeCheckingExceptionPrivate(n, "expecting an integer term in regexp loop 2");
      }
      //if(!(*it).isConst()) {
        //throw TypeCheckingExceptionPrivate(n, "expecting an const integer term in regexp loop 2");
      //}
      ++it;
      if(it != it_end) {
        t = (*it).getType(check);
        if (!t.isInteger()) {
          throw TypeCheckingExceptionPrivate(n, "expecting an integer term in regexp loop 3");
        }
        //if(!(*it).isConst()) {
          //throw TypeCheckingExceptionPrivate(n, "expecting an const integer term in regexp loop 3");
        //}
        //if(++it != it_end) {
        //  throw TypeCheckingExceptionPrivate(n, "too many regexp");
        //}
      }
    }
    return nodeManager->regExpType();
  }
};

class StringToRegExpTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting string terms");
      }
      //if( (*it).getKind() != kind::CONST_STRING ) {
      //  throw TypeCheckingExceptionPrivate(n, "expecting constant string terms");
      //}
    }
    return nodeManager->regExpType();
  }
};

class StringInRegExpTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TNode::iterator it = n.begin();
      TypeNode t = (*it).getType(check);
      if (!t.isString()) {
        throw TypeCheckingExceptionPrivate(n, "expecting string terms");
      }
      ++it;
      t = (*it).getType(check);
      if (!t.isRegExp()) {
        throw TypeCheckingExceptionPrivate(n, "expecting regexp terms");
      }
    }
    return nodeManager->booleanType();
  }
};

class EmptyRegExpTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {

    Assert(n.getKind() == kind::REGEXP_EMPTY);
    return nodeManager->regExpType();
  }
};

class SigmaRegExpTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw (TypeCheckingExceptionPrivate, AssertionException) {

    Assert(n.getKind() == kind::REGEXP_SIGMA);
    return nodeManager->regExpType();
  }
};

class RegExpRVTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
      throw (TypeCheckingExceptionPrivate, AssertionException) {
    if( check ) {
      TypeNode t = n[0].getType(check);
      if (!t.isInteger()) {
        throw TypeCheckingExceptionPrivate(n, "expecting an integer term in RV");
      }
    }
    return nodeManager->regExpType();
  }
};


}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__THEORY_STRINGS_TYPE_RULES_H */
