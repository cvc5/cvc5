/*********************                                                        */
/*! \file theory_datatypes_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory of datatypes
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H
#define __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H

#include "expr/matcher.h"
//#include "expr/attribute.h"

namespace CVC4 {

namespace expr {
namespace attr {
struct DatatypeConstructorTypeGroundTermTag {};
} /* CVC4::expr::attr namespace */
} /* CVC4::expr namespace */

namespace theory {
namespace datatypes {

typedef expr::Attribute<expr::attr::DatatypeConstructorTypeGroundTermTag, Node>
    GroundTermAttr;

struct DatatypeConstructorTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    Assert(n.getKind() == kind::APPLY_CONSTRUCTOR);
    TypeNode consType = n.getOperator().getType(check);
    Type t = consType.getConstructorRangeType().toType();
    Assert(t.isDatatype());
    DatatypeType dt = DatatypeType(t);
    TNode::iterator child_it = n.begin();
    TNode::iterator child_it_end = n.end();
    TypeNode::iterator tchild_it = consType.begin();
    if ((dt.isParametric() || check) &&
        n.getNumChildren() != consType.getNumChildren() - 1) {
      throw TypeCheckingExceptionPrivate(
          n, "number of arguments does not match the constructor type");
    }
    if (dt.isParametric()) {
      Debug("typecheck-idt") << "typecheck parameterized datatype " << n
                             << std::endl;
      Matcher m(dt);
      for (; child_it != child_it_end; ++child_it, ++tchild_it) {
        TypeNode childType = (*child_it).getType(check);
        if (!m.doMatching(*tchild_it, childType)) {
          throw TypeCheckingExceptionPrivate(
              n, "matching failed for parameterized constructor");
        }
      }
      std::vector<Type> instTypes;
      m.getMatches(instTypes);
      TypeNode range = TypeNode::fromType(dt.instantiate(instTypes));
      Debug("typecheck-idt") << "Return " << range << std::endl;
      return range;
    } else {
      if (check) {
        Debug("typecheck-idt") << "typecheck cons: " << n << " "
                               << n.getNumChildren() << std::endl;
        Debug("typecheck-idt") << "cons type: " << consType << " "
                               << consType.getNumChildren() << std::endl;
        for (; child_it != child_it_end; ++child_it, ++tchild_it) {
          TypeNode childType = (*child_it).getType(check);
          Debug("typecheck-idt") << "typecheck cons arg: " << childType << " "
                                 << (*tchild_it) << std::endl;
          TypeNode argumentType = *tchild_it;
          if (!childType.isComparableTo(argumentType)) {
            std::stringstream ss;
            ss << "bad type for constructor argument:\nexpected: "
               << argumentType << "\ngot     : " << childType;
            throw TypeCheckingExceptionPrivate(n, ss.str());
          }
        }
      }
      return consType.getConstructorRangeType();
    }
  }

  inline static bool computeIsConst(NodeManager* nodeManager, TNode n) {
    Assert(n.getKind() == kind::APPLY_CONSTRUCTOR);
    NodeManagerScope nms(nodeManager);
    for (TNode::const_iterator i = n.begin(); i != n.end(); ++i) {
      if (!(*i).isConst()) {
        return false;
      }
    }
    return true;
  }
}; /* struct DatatypeConstructorTypeRule */

struct DatatypeSelectorTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    Assert(n.getKind() == kind::APPLY_SELECTOR ||
           n.getKind() == kind::APPLY_SELECTOR_TOTAL);
    TypeNode selType = n.getOperator().getType(check);
    Type t = selType[0].toType();
    Assert(t.isDatatype());
    DatatypeType dt = DatatypeType(t);
    if ((dt.isParametric() || check) && n.getNumChildren() != 1) {
      throw TypeCheckingExceptionPrivate(
          n, "number of arguments does not match the selector type");
    }
    if (dt.isParametric()) {
      Debug("typecheck-idt") << "typecheck parameterized sel: " << n
                             << std::endl;
      Matcher m(dt);
      TypeNode childType = n[0].getType(check);
      if (!childType.isInstantiatedDatatype()) {
        throw TypeCheckingExceptionPrivate(
            n, "Datatype type not fully instantiated");
      }
      if (!m.doMatching(selType[0], childType)) {
        throw TypeCheckingExceptionPrivate(
            n,
            "matching failed for selector argument of parameterized datatype");
      }
      std::vector<Type> types, matches;
      m.getTypes(types);
      m.getMatches(matches);
      Type range = selType[1].toType();
      range = range.substitute(types, matches);
      Debug("typecheck-idt") << "Return " << range << std::endl;
      return TypeNode::fromType(range);
    } else {
      if (check) {
        Debug("typecheck-idt") << "typecheck sel: " << n << std::endl;
        Debug("typecheck-idt") << "sel type: " << selType << std::endl;
        TypeNode childType = n[0].getType(check);
        if (!selType[0].isComparableTo(childType)) {
          Debug("typecheck-idt") << "ERROR: " << selType[0].getKind() << " "
                                 << childType.getKind() << std::endl;
          throw TypeCheckingExceptionPrivate(n,
                                             "bad type for selector argument");
        }
      }
      return selType[1];
    }
  }
}; /* struct DatatypeSelectorTypeRule */

struct DatatypeTesterTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    Assert(n.getKind() == kind::APPLY_TESTER);
    if (check) {
      if (n.getNumChildren() != 1) {
        throw TypeCheckingExceptionPrivate(
            n, "number of arguments does not match the tester type");
      }
      TypeNode testType = n.getOperator().getType(check);
      TypeNode childType = n[0].getType(check);
      Type t = testType[0].toType();
      Assert(t.isDatatype());
      DatatypeType dt = DatatypeType(t);
      if (dt.isParametric()) {
        Debug("typecheck-idt") << "typecheck parameterized tester: " << n
                               << std::endl;
        Matcher m(dt);
        if (!m.doMatching(testType[0], childType)) {
          throw TypeCheckingExceptionPrivate(
              n,
              "matching failed for tester argument of parameterized datatype");
        }
      } else {
        Debug("typecheck-idt") << "typecheck test: " << n << std::endl;
        Debug("typecheck-idt") << "test type: " << testType << std::endl;
        if (!testType[0].isComparableTo(childType)) {
          throw TypeCheckingExceptionPrivate(n, "bad type for tester argument");
        }
      }
    }
    return nodeManager->booleanType();
  }
}; /* struct DatatypeTesterTypeRule */

struct DatatypeAscriptionTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    Debug("typecheck-idt") << "typechecking ascription: " << n << std::endl;
    Assert(n.getKind() == kind::APPLY_TYPE_ASCRIPTION);
    TypeNode t = TypeNode::fromType(
        n.getOperator().getConst<AscriptionType>().getType());
    if (check) {
      TypeNode childType = n[0].getType(check);

      Matcher m;
      if (childType.getKind() == kind::CONSTRUCTOR_TYPE) {
        m.addTypesFromDatatype(
            ConstructorType(childType.toType()).getRangeType());
      } else if (childType.getKind() == kind::DATATYPE_TYPE) {
        m.addTypesFromDatatype(DatatypeType(childType.toType()));
      }
      if (!m.doMatching(childType, t)) {
        throw TypeCheckingExceptionPrivate(n,
                                           "matching failed for type "
                                           "ascription argument of "
                                           "parameterized datatype");
      }
    }
    return t;
  }
}; /* struct DatatypeAscriptionTypeRule */

struct ConstructorProperties {
  inline static Cardinality computeCardinality(TypeNode type) {
    // Constructors aren't exactly functions, they're like
    // parameterized ground terms.  So the cardinality is more like
    // that of a tuple than that of a function.
    AssertArgument(type.isConstructor(), type);
    Cardinality c = 1;
    for (unsigned i = 0, i_end = type.getNumChildren(); i < i_end - 1; ++i) {
      c *= type[i].getCardinality();
    }
    return c;
  }
}; /* struct ConstructorProperties */

struct TupleUpdateTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    Assert(n.getKind() == kind::TUPLE_UPDATE);
    const TupleUpdate& tu = n.getOperator().getConst<TupleUpdate>();
    TypeNode tupleType = n[0].getType(check);
    TypeNode newValue = n[1].getType(check);
    if (check) {
      if (!tupleType.isTuple()) {
        throw TypeCheckingExceptionPrivate(
            n, "Tuple-update expression formed over non-tuple");
      }
      if (tu.getIndex() >= tupleType.getTupleLength()) {
        std::stringstream ss;
        ss << "Tuple-update expression index `" << tu.getIndex()
           << "' is not a valid index; tuple type only has "
           << tupleType.getTupleLength() << " fields";
        throw TypeCheckingExceptionPrivate(n, ss.str().c_str());
      }
    }
    return tupleType;
  }
}; /* struct TupleUpdateTypeRule */

struct RecordUpdateTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    Assert(n.getKind() == kind::RECORD_UPDATE);
    NodeManagerScope nms(nodeManager);
    const RecordUpdate& ru = n.getOperator().getConst<RecordUpdate>();
    TypeNode recordType = n[0].getType(check);
    TypeNode newValue = n[1].getType(check);
    if (check) {
      if (!recordType.isRecord()) {
        throw TypeCheckingExceptionPrivate(
            n, "Record-update expression formed over non-record");
      }
      const Record& rec = recordType.getRecord();
      if (!rec.contains(ru.getField())) {
        std::stringstream ss;
        ss << "Record-update field `" << ru.getField()
           << "' is not a valid field name for the record type";
        throw TypeCheckingExceptionPrivate(n, ss.str().c_str());
      }
    }
    return recordType;
  }
}; /* struct RecordUpdateTypeRule */

class DtSizeTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    if (check) {
      TypeNode t = n[0].getType(check);
      if (!t.isDatatype()) {
        throw TypeCheckingExceptionPrivate(
            n, "expecting datatype size term to have datatype argument.");
      }
    }
    return nodeManager->integerType();
  }
}; /* class DtSizeTypeRule */

class DtHeightBoundTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    if (check) {
      TypeNode t = n[0].getType(check);
      if (!t.isDatatype()) {
        throw TypeCheckingExceptionPrivate(
            n,
            "expecting datatype height bound term to have datatype argument.");
      }
      if (n[1].getKind() != kind::CONST_RATIONAL) {
        throw TypeCheckingExceptionPrivate(
            n, "datatype height bound must be a constant");
      }
      if (n[1].getConst<Rational>().getNumerator().sgn() == -1) {
        throw TypeCheckingExceptionPrivate(
            n, "datatype height bound must be non-negative");
      }
    }
    return nodeManager->booleanType();
  }
}; /* class DtHeightBoundTypeRule */

} /* CVC4::theory::datatypes namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H */
