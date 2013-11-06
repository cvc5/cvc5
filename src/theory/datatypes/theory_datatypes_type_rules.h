/*********************                                                        */
/*! \file theory_datatypes_type_rules.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
//#include "expr/attribute.h"

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
    throw(TypeCheckingExceptionPrivate, AssertionException) {
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
          TypeNode argumentType = *tchild_it;
          if(!childType.isComparableTo(argumentType)) {
            std::stringstream ss;
            ss << "bad type for constructor argument:\nexpected: " << argumentType << "\ngot     : " << childType;
            throw TypeCheckingExceptionPrivate(n, ss.str());
          }
        }
      }
      return consType.getConstructorRangeType();
    }
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n)
    throw(AssertionException) {
    Assert(n.getKind() == kind::APPLY_CONSTRUCTOR);
    NodeManagerScope nms(nodeManager);
    for(TNode::const_iterator i = n.begin(); i != n.end(); ++i) {
      if( ! (*i).isConst() ) {
        return false;
      }
    }
    return true;
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
        if(!selType[0].isComparableTo(childType)) {
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
      if(dt.isParametric()) {
        Debug("typecheck-idt") << "typecheck parameterized tester: " << n << std::endl;
        Matcher m( dt );
        if( !m.doMatching( testType[0], childType ) ){
          throw TypeCheckingExceptionPrivate(n, "matching failed for tester argument of parameterized datatype");
        }
      } else {
        Debug("typecheck-idt") << "typecheck test: " << n << std::endl;
        Debug("typecheck-idt") << "test type: " << testType << std::endl;
        if(!testType[0].isComparableTo(childType)) {
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

struct TupleTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    Assert(n.getKind() == kind::TUPLE);
    std::vector<TypeNode> types;
    for(TNode::iterator child_it = n.begin(), child_it_end = n.end();
        child_it != child_it_end;
        ++child_it) {
      types.push_back((*child_it).getType(check));
    }
    return nodeManager->mkTupleType(types);
  }
};/* struct TupleTypeRule */

struct TupleSelectTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    Assert(n.getKind() == kind::TUPLE_SELECT);
    const TupleSelect& ts = n.getOperator().getConst<TupleSelect>();
    TypeNode tupleType = n[0].getType(check);
    if(!tupleType.isTuple()) {
      if(!tupleType.hasAttribute(expr::DatatypeTupleAttr())) {
        throw TypeCheckingExceptionPrivate(n, "Tuple-select expression formed over non-tuple");
      }
      tupleType = tupleType.getAttribute(expr::DatatypeTupleAttr());
    }
    if(ts.getIndex() >= tupleType.getNumChildren()) {
      std::stringstream ss;
      ss << "Tuple-select expression index `" << ts.getIndex()
         << "' is not a valid index; tuple type only has "
         << tupleType.getNumChildren() << " fields";
      throw TypeCheckingExceptionPrivate(n, ss.str().c_str());
    }
    return tupleType[ts.getIndex()];
  }
};/* struct TupleSelectTypeRule */

struct TupleUpdateTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    Assert(n.getKind() == kind::TUPLE_UPDATE);
    const TupleUpdate& tu = n.getOperator().getConst<TupleUpdate>();
    TypeNode tupleType = n[0].getType(check);
    TypeNode newValue = n[1].getType(check);
    if(check) {
      if(!tupleType.isTuple()) {
        if(!tupleType.hasAttribute(expr::DatatypeTupleAttr())) {
          throw TypeCheckingExceptionPrivate(n, "Tuple-update expression formed over non-tuple");
        }
        tupleType = tupleType.getAttribute(expr::DatatypeTupleAttr());
      }
      if(tu.getIndex() >= tupleType.getNumChildren()) {
        std::stringstream ss;
        ss << "Tuple-update expression index `" << tu.getIndex()
           << "' is not a valid index; tuple type only has "
           << tupleType.getNumChildren() << " fields";
        throw TypeCheckingExceptionPrivate(n, ss.str().c_str());
      }
    }
    return tupleType;
  }
};/* struct TupleUpdateTypeRule */

struct TupleProperties {
  inline static Cardinality computeCardinality(TypeNode type) {
    // Don't assert this; allow other theories to use this cardinality
    // computation.
    //
    // Assert(type.getKind() == kind::TUPLE_TYPE);

    Cardinality card(1);
    for(TypeNode::iterator i = type.begin(),
          i_end = type.end();
        i != i_end;
        ++i) {
      card *= (*i).getCardinality();
    }

    return card;
  }

  inline static bool isWellFounded(TypeNode type) {
    // Don't assert this; allow other theories to use this
    // wellfoundedness computation.
    //
    // Assert(type.getKind() == kind::TUPLE_TYPE);

    for(TypeNode::iterator i = type.begin(),
          i_end = type.end();
        i != i_end;
        ++i) {
      if(! (*i).isWellFounded()) {
        return false;
      }
    }

    return true;
  }

  inline static Node mkGroundTerm(TypeNode type) {
    Assert(type.getKind() == kind::TUPLE_TYPE);

    std::vector<Node> children;
    for(TypeNode::iterator i = type.begin(),
          i_end = type.end();
        i != i_end;
        ++i) {
      children.push_back((*i).mkGroundTerm());
    }

    return NodeManager::currentNM()->mkNode(kind::TUPLE, children);
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n) {
    Assert(n.getKind() == kind::TUPLE);
    NodeManagerScope nms(nodeManager);

    for(TNode::iterator i = n.begin(),
          i_end = n.end();
        i != i_end;
        ++i) {
      if(! (*i).isConst()) {
        return false;
      }
    }

    return true;
  }
};/* struct TupleProperties */

struct RecordTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    Assert(n.getKind() == kind::RECORD);
    NodeManagerScope nms(nodeManager);
    const Record& rec = n.getOperator().getConst<Record>();
    if(check) {
      Record::iterator i = rec.begin();
      for(TNode::iterator child_it = n.begin(), child_it_end = n.end();
          child_it != child_it_end;
          ++child_it, ++i) {
        if(i == rec.end()) {
          throw TypeCheckingExceptionPrivate(n, "record description has different length than record literal");
        }
        if(!(*child_it).getType(check).isComparableTo(TypeNode::fromType((*i).second))) {
          throw TypeCheckingExceptionPrivate(n, "record description types differ from record literal types");
        }
      }
      if(i != rec.end()) {
        throw TypeCheckingExceptionPrivate(n, "record description has different length than record literal");
      }
    }
    return nodeManager->mkRecordType(rec);
  }
};/* struct RecordTypeRule */

struct RecordSelectTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    Assert(n.getKind() == kind::RECORD_SELECT);
    NodeManagerScope nms(nodeManager);
    const RecordSelect& rs = n.getOperator().getConst<RecordSelect>();
    TypeNode recordType = n[0].getType(check);
    if(!recordType.isRecord()) {
      if(!recordType.hasAttribute(expr::DatatypeRecordAttr())) {
        throw TypeCheckingExceptionPrivate(n, "Record-select expression formed over non-record");
      }
      recordType = recordType.getAttribute(expr::DatatypeRecordAttr());
    }
    const Record& rec = recordType.getRecord();
    Record::const_iterator field = rec.find(rs.getField());
    if(field == rec.end()) {
      std::stringstream ss;
      ss << "Record-select field `" << rs.getField()
         << "' is not a valid field name for the record type";
      throw TypeCheckingExceptionPrivate(n, ss.str().c_str());
    }
    return TypeNode::fromType((*field).second);
  }
};/* struct RecordSelectTypeRule */

struct RecordUpdateTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check) {
    Assert(n.getKind() == kind::RECORD_UPDATE);
    NodeManagerScope nms(nodeManager);
    const RecordUpdate& ru = n.getOperator().getConst<RecordUpdate>();
    TypeNode recordType = n[0].getType(check);
    TypeNode newValue = n[1].getType(check);
    if(check) {
      if(!recordType.isRecord()) {
        if(!recordType.hasAttribute(expr::DatatypeRecordAttr())) {
          throw TypeCheckingExceptionPrivate(n, "Record-update expression formed over non-record");
        }
        recordType = recordType.getAttribute(expr::DatatypeRecordAttr());
      }
      const Record& rec = recordType.getRecord();
      Record::const_iterator field = rec.find(ru.getField());
      if(field == rec.end()) {
        std::stringstream ss;
        ss << "Record-update field `" << ru.getField()
           << "' is not a valid field name for the record type";
        throw TypeCheckingExceptionPrivate(n, ss.str().c_str());
      }
    }
    return recordType;
  }
};/* struct RecordUpdateTypeRule */

struct RecordProperties {
  inline static Node mkGroundTerm(TypeNode type) {
    Unimplemented();
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n) {
    Assert(n.getKind() == kind::RECORD);
    NodeManagerScope nms(nodeManager);

    for(TNode::iterator i = n.begin(),
          i_end = n.end();
        i != i_end;
        ++i) {
      if(! (*i).isConst()) {
        return false;
      }
    }

    return true;
  }
};/* struct RecordProperties */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H */
