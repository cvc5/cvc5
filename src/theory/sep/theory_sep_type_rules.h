/*********************                                                        */
/*! \file theory_sep_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Typing and cardinality rules for the theory of sep
 **
 ** Typing and cardinality rules for the theory of sep.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SEP__THEORY_SEP_TYPE_RULES_H
#define CVC4__THEORY__SEP__THEORY_SEP_TYPE_RULES_H

namespace CVC4 {
namespace theory {
namespace sep {

class SepEmpTypeRule {
public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::SEP_EMP);
    return nodeManager->booleanType();
  }
};

struct SepPtoTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::SEP_PTO);
    if( check ) {
      TypeNode refType = n[0].getType(check);
      TypeNode ptType = n[1].getType(check);
    }
    return nodeManager->booleanType();
  }
};/* struct SepSelectTypeRule */

struct SepStarTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    TypeNode btype = nodeManager->booleanType();
    Assert(n.getKind() == kind::SEP_STAR);
    if( check ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        TypeNode ctype = n[i].getType( check );
        if( ctype!=btype ){
          throw TypeCheckingExceptionPrivate(n, "child of sep star is not Boolean");
        }
      }
    }
    return btype;
  }
};/* struct SepStarTypeRule */

struct SepWandTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    TypeNode btype = nodeManager->booleanType();
    Assert(n.getKind() == kind::SEP_WAND);
    if( check ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        TypeNode ctype = n[i].getType( check );
        if( ctype!=btype ){
          throw TypeCheckingExceptionPrivate(n, "child of sep magic wand is not Boolean");
        }
      }
    }
    return btype;
  }
};/* struct SepWandTypeRule */

struct SepLabelTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    TypeNode btype = nodeManager->booleanType();
    Assert(n.getKind() == kind::SEP_LABEL);
    if( check ){
      TypeNode ctype = n[0].getType( check );
      if( ctype!=btype ){
        throw TypeCheckingExceptionPrivate(n, "child of sep label is not Boolean");
      }
      TypeNode stype = n[1].getType( check );
      if( !stype.isSet() ){
        throw TypeCheckingExceptionPrivate(n, "label of sep label is not a set");
      }
    }
    return btype;
  }
};/* struct SepLabelTypeRule */

struct SepNilTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::SEP_NIL);
    Assert(check);
    TypeNode type = n.getType();
    return type;
  }
};/* struct SepLabelTypeRule */


}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SEP__THEORY_SEP_TYPE_RULES_H */
