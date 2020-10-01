/*********************                                                        */
/*! \file theory_bool_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add brief comments here ]]
 **
 ** [[ Add file-specific comments here ]]
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY_BOOL_TYPE_RULES_H
#define CVC4__THEORY_BOOL_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace boolean {

class BooleanTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    TypeNode booleanType = nodeManager->booleanType();
    if( check ) {
      TNode::iterator child_it = n.begin();
      TNode::iterator child_it_end = n.end();
      for(; child_it != child_it_end; ++child_it) {
        if(!(*child_it).getType(check).isBoolean()) {
          Debug("pb") << "failed type checking: " << *child_it << std::endl;
          Debug("pb") << "  integer: " << (*child_it).getType(check).isInteger() << std::endl;
          Debug("pb") << "  real: " << (*child_it).getType(check).isReal() << std::endl;
          throw TypeCheckingExceptionPrivate(n, "expecting a Boolean subexpression");
        }
      }
    }
    return booleanType;
  }
};/* class BooleanTypeRule */

class IteTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    TypeNode thenType = n[1].getType(check);
    TypeNode elseType = n[2].getType(check);
    TypeNode iteType = TypeNode::leastCommonTypeNode(thenType, elseType);
    if( check ) {
      TypeNode booleanType = nodeManager->booleanType();
      if (n[0].getType(check) != booleanType) {
        throw TypeCheckingExceptionPrivate(n, "condition of ITE is not Boolean");
      }
      if (iteType.isNull()) {
        std::stringstream ss;
        ss << "Both branches of the ITE must be a subtype of a common type." << std::endl
           << "then branch: " << n[1] << std::endl
           << "its type   : " << thenType << std::endl
           << "else branch: " << n[2] << std::endl
           << "its type   : " << elseType << std::endl;
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
    return iteType;
  }
};/* class IteTypeRule */

}/* CVC4::theory::boolean namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY_BOOL_TYPE_RULES_H */
