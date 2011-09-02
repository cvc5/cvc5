/*********************                                                        */
/*! \file theory_datatypes_type_rules.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of datatypes
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H
#define __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H

#include "util/matcher.h"

namespace CVC4 {

namespace expr {
  namespace attr {
    struct DatatypeConstructorTypeGroundTermTag {};
  }/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */

namespace theory {
namespace datatypes {

typedef expr::Attribute<expr::attr::DatatypeConstructorTypeGroundTermTag, Node> GroundTermAttr;

struct DatatypeConstructorTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::APPLY_CONSTRUCTOR);
    TypeNode consType = n.getOperator().getType(check);
    Type t = consType.getConstructorRangeType().toType();
    Assert( t.isDatatype() );
    DatatypeType dt = DatatypeType(t);
    TNode::iterator child_it = n.begin();
    TNode::iterator child_it_end = n.end();
    TypeNode::iterator tchild_it = consType.begin();
    if( ( dt.isParametric() || check ) && n.getNumChildren() != consType.getNumChildren() - 1 ){
      throw TypeCheckingExceptionPrivate(n, "number of arguments does not match the constructor type");
    }
    if( dt.isParametric() ){
      Debug("typecheck-idt") << "typecheck parameterized datatype " << n << std::endl;
      Matcher m( dt );
      for(; child_it != child_it_end; ++child_it, ++tchild_it) {
        TypeNode childType = (*child_it).getType(check);
        if( !m.doMatching( *tchild_it, childType ) ){
          throw TypeCheckingExceptionPrivate(n, "matching failed for parameterized constructor");
        }
      }
      std::vector< Type > instTypes;
      m.getMatches( instTypes );
      TypeNode range = TypeNode::fromType( dt.instantiate( instTypes ) );
      Debug("typecheck-idt") << "Return " << range << std::endl;
      return range;
    }else{
      if(check) {
        Debug("typecheck-idt") << "typecheck cons: " << n << " " << n.getNumChildren() << std::endl;
        Debug("typecheck-idt") << "cons type: " << consType << " " << consType.getNumChildren() << std::endl;
        for(; child_it != child_it_end; ++child_it, ++tchild_it) {
          TypeNode childType = (*child_it).getType(check);
          Debug("typecheck-idt") << "typecheck cons arg: " << childType << " " << (*tchild_it) << std::endl;
          if(childType != *tchild_it) {
            throw TypeCheckingExceptionPrivate(n, "bad type for constructor argument");
          }
        }
      }
      return consType.getConstructorRangeType();
    }
  }
};/* struct DatatypeConstructorTypeRule */

struct DatatypeSelectorTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::APPLY_SELECTOR);
    TypeNode selType = n.getOperator().getType(check);
    Type t = selType[0].toType();
    Assert( t.isDatatype() );
    DatatypeType dt = DatatypeType(t);
    if( ( dt.isParametric() || check ) && n.getNumChildren() != 1 ){
      throw TypeCheckingExceptionPrivate(n, "number of arguments does not match the selector type");
    }
    if( dt.isParametric() ){
      Debug("typecheck-idt") << "typecheck parameterized sel: " << n << std::endl;
      Matcher m( dt );
      TypeNode childType = n[0].getType(check);
      if(! childType.isInstantiatedDatatype()) {
        throw TypeCheckingExceptionPrivate(n, "Datatype type not fully instantiated");
      }
      if( !m.doMatching( selType[0], childType ) ){
        throw TypeCheckingExceptionPrivate(n, "matching failed for selector argument of parameterized datatype");
      }
      std::vector< Type > types, matches;
      m.getTypes( types );
      m.getMatches( matches );
      Type range = selType[1].toType();
      range = range.substitute( types, matches );
      Debug("typecheck-idt") << "Return " << range << std::endl;
      return TypeNode::fromType( range );
    }else{
      if(check) {
        Debug("typecheck-idt") << "typecheck sel: " << n << std::endl;
        Debug("typecheck-idt") << "sel type: " << selType << std::endl;
        TypeNode childType = n[0].getType(check);
        if(selType[0] != childType) {
          Debug("typecheck-idt") << "ERROR: " << selType[0].getKind() << " " << childType.getKind() << std::endl;
          throw TypeCheckingExceptionPrivate(n, "bad type for selector argument");
        }
      }
      return selType[1];
    }
  }
};/* struct DatatypeSelectorTypeRule */

struct DatatypeTesterTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Assert(n.getKind() == kind::APPLY_TESTER);
    if(check) {
      if(n.getNumChildren() != 1) {
        throw TypeCheckingExceptionPrivate(n, "number of arguments does not match the tester type");
      }
      TypeNode testType = n.getOperator().getType(check);
      TypeNode childType = n[0].getType(check);
      Type t = testType[0].toType();
      Assert( t.isDatatype() );
      DatatypeType dt = DatatypeType(t);
      if( dt.isParametric() ){
        Debug("typecheck-idt") << "typecheck parameterized tester: " << n << std::endl;
        Matcher m( dt );
        if( !m.doMatching( testType[0], childType ) ){
          throw TypeCheckingExceptionPrivate(n, "matching failed for tester argument of parameterized datatype");
        }
      }else{
        Debug("typecheck-idt") << "typecheck test: " << n << std::endl;
        Debug("typecheck-idt") << "test type: " << testType << std::endl;
        if(testType[0] != childType) {
          throw TypeCheckingExceptionPrivate(n, "bad type for tester argument");
        }
      }
    }
    return nodeManager->booleanType();
  }
};/* struct DatatypeTesterTypeRule */

struct DatatypeAscriptionTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
    throw(TypeCheckingExceptionPrivate) {
    Debug("typecheck-idt") << "typechecking ascription: " << n << std::endl;
    Assert(n.getKind() == kind::APPLY_TYPE_ASCRIPTION);
    TypeNode t = TypeNode::fromType(n.getOperator().getConst<AscriptionType>().getType());
    if(check) {
      TypeNode childType = n[0].getType(check);
      //if(!t.getKind() == kind::DATATYPE_TYPE) {
      //  throw TypeCheckingExceptionPrivate(n, "bad type for datatype type ascription");
      //}
      //DatatypeType dt = DatatypeType(childType.toType());
      //if( dt.isParametric() ){
      //  Debug("typecheck-idt") << "typecheck parameterized ascription: " << n << std::endl;
      //  Matcher m( dt );
      //  if( !m.doMatching( childType, t ) ){
      //    throw TypeCheckingExceptionPrivate(n, "matching failed for type ascription argument of parameterized datatype");
      //  }
      //}else{
      //  Debug("typecheck-idt") << "typecheck test: " << n << std::endl;
      //  if(t != childType) {
      //    throw TypeCheckingExceptionPrivate(n, "bad type for type ascription argument");
      //  }
      //}

      Matcher m;
      if( childType.getKind() == kind::CONSTRUCTOR_TYPE ){
        m.addTypesFromDatatype( ConstructorType(childType.toType()).getRangeType() );
      }else if( childType.getKind() == kind::DATATYPE_TYPE ){
        m.addTypesFromDatatype( DatatypeType(childType.toType()) );
      }
      if( !m.doMatching( childType, t ) ){
        throw TypeCheckingExceptionPrivate(n, "matching failed for type ascription argument of parameterized datatype");
      }

    }
    return t;
  }
};/* struct DatatypeAscriptionTypeRule */

struct ConstructorProperties {
  inline static Cardinality computeCardinality(TypeNode type) {
    // Constructors aren't exactly functions, they're like
    // parameterized ground terms.  So the cardinality is more like
    // that of a tuple than that of a function.
    AssertArgument(type.isConstructor(), type);
    Cardinality c = 1;
    for(unsigned i = 0, i_end = type.getNumChildren(); i < i_end - 1; ++i) {
      c *= type[i].getCardinality();
    }
    return c;
  }

  inline static bool isWellFounded(TypeNode type) {
    // Constructors aren't exactly functions, they're like
    // parameterized ground terms.  So the wellfoundedness is more
    // like that of a tuple than that of a function.
    AssertArgument(type.isConstructor(), type);
    for(unsigned i = 0, i_end = type.getNumChildren(); i < i_end - 1; ++i) {
      if(!type[i].isWellFounded()) {
        return false;
      }
    }
    return true;
  }

  inline static Node mkGroundTerm(TypeNode type) {
    AssertArgument(type.isConstructor(), type);

    // is this already in the cache ?
    Node groundTerm = type.getAttribute(GroundTermAttr());
    if(!groundTerm.isNull()) {
      return groundTerm;
    }

    // This is a bit tricky; Constructors have a unique index within
    // their datatype, but Constructor *types* do not; multiple
    // Constructors within the same Datatype could share the same
    // type.  So we scan through the datatype to find one that
    // matches.
    //const Datatype& dt = type[type.getNumChildren() - 1].getConst<Datatype>();
    const Datatype& dt = DatatypeType(type[type.getNumChildren() - 1].toType()).getDatatype();
    for(Datatype::const_iterator i = dt.begin(),
          i_end = dt.end();
        i != i_end;
        ++i) {
      if(TypeNode::fromType((*i).getConstructor().getType()) == type) {
        groundTerm = Node::fromExpr((*i).mkGroundTerm( type.toType() ));
        type.setAttribute(GroundTermAttr(), groundTerm);
        return groundTerm;
      }
    }

    InternalError("couldn't find a matching constructor?!");
  }
};/* struct ConstructorProperties */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H */
