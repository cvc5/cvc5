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

class StringConcatTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    TypeNode tret;
    for (const Node& nc : n)
    {
      TypeNode t = nc.getType(check);
      if (tret.isNull())
      {
        tret = t;
        if (check)
        {
          if (!t.isStringLike())
          {
            throw TypeCheckingExceptionPrivate(
                n, "expecting string-like terms in concat");
          }
        }
        else
        {
          break;
        }
      }
      else if (t != tret)
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting all children to have the same type in concat");
      }
    }
    return tret;
  }
};

class StringSubstrTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    TypeNode t = n[0].getType(check);
    if (check)
    {
      if (!t.isStringLike())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting a string-like term in substr");
      }
      TypeNode t2 = n[1].getType(check);
      if (!t2.isInteger())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting an integer start term in substr");
      }
      t2 = n[2].getType(check);
      if (!t2.isInteger())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting an integer length term in substr");
      }
    }
    return t;
  }
};

class StringAtTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    TypeNode t = n[0].getType(check);
    if (check)
    {
      if (!t.isStringLike())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting a string-like term in str.at");
      }
      TypeNode t2 = n[1].getType(check);
      if (!t2.isInteger())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting an integer start term in str.at");
      }
    }
    return t;
  }
};

class StringIndexOfTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    if (check)
    {
      TypeNode t = n[0].getType(check);
      if (!t.isStringLike())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting a string-like term in indexof");
      }
      TypeNode t2 = n[1].getType(check);
      if (t != t2)
      {
        throw TypeCheckingExceptionPrivate(
            n,
            "expecting a term in second argument of indexof that is the same "
            "type as the first argument");
      }
      t = n[2].getType(check);
      if (!t.isInteger())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting an integer term in third argument of indexof");
      }
    }
    return nodeManager->integerType();
  }
};

class StringReplaceTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    TypeNode t = n[0].getType(check);
    if (check)
    {
      if (!t.isStringLike())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting a string-like term in replace");
      }
      TypeNode t2 = n[1].getType(check);
      if (t != t2)
      {
        throw TypeCheckingExceptionPrivate(
            n,
            "expecting a term in second argument of replace that is the same "
            "type as the first argument");
      }
      t2 = n[2].getType(check);
      if (t != t2)
      {
        throw TypeCheckingExceptionPrivate(
            n,
            "expecting a term in third argument of replace that is the same "
            "type as the first argument");
      }
    }
    return t;
  }
};

class StringStrToBoolTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    if (check)
    {
      TypeNode t = n[0].getType(check);
      if (!t.isStringLike())
      {
        std::stringstream ss;
        ss << "expecting a string-like term in argument of " << n.getKind();
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
    return nodeManager->booleanType();
  }
};

class StringStrToIntTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    if (check)
    {
      TypeNode t = n[0].getType(check);
      if (!t.isStringLike())
      {
        std::stringstream ss;
        ss << "expecting a string-like term in argument of " << n.getKind();
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
    return nodeManager->integerType();
  }
};

class StringStrToStrTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    TypeNode t = n[0].getType(check);
    if (check)
    {
      if (!t.isStringLike())
      {
        std::stringstream ss;
        ss << "expecting a string term in argument of " << n.getKind();
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
    return t;
  }
};

class StringRelationTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    if (check)
    {
      TypeNode t = n[0].getType(check);
      if (!t.isStringLike())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting a string-like term in relation");
      }
      TypeNode t2 = n[1].getType(check);
      if (t != t2)
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting two terms of the same string-like type in relation");
      }
    }
    return nodeManager->booleanType();
  }
};

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
        if (!(*it).isConst())
        {
          throw TypeCheckingExceptionPrivate(n, "expecting a constant string term in regexp range");
        }
        if( (*it).getConst<String>().size() != 1 ) {
          throw TypeCheckingExceptionPrivate(n, "expecting a single constant string term in regexp range");
        }
        unsigned ci = (*it).getConst<String>().front();
        ch[i] = ci;
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
