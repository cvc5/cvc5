/*********************                                                        */
/*! \file theory_datatypes_type_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory of datatypes
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H
#define CVC4__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H

#include "expr/dtype.h"
#include "expr/type_matcher.h"
#include "theory/datatypes/theory_datatypes_utils.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

struct DatatypeConstructorTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    Assert(n.getKind() == kind::APPLY_CONSTRUCTOR);
    TypeNode consType = n.getOperator().getType(check);
    TypeNode t = consType.getConstructorRangeType();
    Assert(t.isDatatype());
    TNode::iterator child_it = n.begin();
    TNode::iterator child_it_end = n.end();
    TypeNode::iterator tchild_it = consType.begin();
    if ((t.isParametricDatatype() || check)
        && n.getNumChildren() != consType.getNumChildren() - 1)
    {
      throw TypeCheckingExceptionPrivate(
          n, "number of arguments does not match the constructor type");
    }
    if (t.isParametricDatatype())
    {
      Debug("typecheck-idt") << "typecheck parameterized datatype " << n
                             << std::endl;
      TypeMatcher m(t);
      for (; child_it != child_it_end; ++child_it, ++tchild_it) {
        TypeNode childType = (*child_it).getType(check);
        if (!m.doMatching(*tchild_it, childType)) {
          throw TypeCheckingExceptionPrivate(
              n, "matching failed for parameterized constructor");
        }
      }
      std::vector<TypeNode> instTypes;
      m.getMatches(instTypes);
      TypeNode range = t.instantiateParametricDatatype(instTypes);
      Debug("typecheck-idt") << "Return " << range << std::endl;
      return range;
    }
    else
    {
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
          if (!childType.isSubtypeOf(argumentType)) { 
            std::stringstream ss;
            ss << "bad type for constructor argument:\n"
               << "child type:  " << childType << "\n"
               << "not subtype: " << argumentType << "\n"
               << "in term : " << n;
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
    Assert(n.getKind() == kind::APPLY_SELECTOR
           || n.getKind() == kind::APPLY_SELECTOR_TOTAL);
    TypeNode selType = n.getOperator().getType(check);
    TypeNode t = selType[0];
    Assert(t.isDatatype());
    if ((t.isParametricDatatype() || check) && n.getNumChildren() != 1)
    {
      throw TypeCheckingExceptionPrivate(
          n, "number of arguments does not match the selector type");
    }
    if (t.isParametricDatatype())
    {
      Debug("typecheck-idt") << "typecheck parameterized sel: " << n
                             << std::endl;
      TypeMatcher m(t);
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
      std::vector<TypeNode> types, matches;
      m.getTypes(types);
      m.getMatches(matches);
      TypeNode range = selType[1];
      range = range.substitute(
          types.begin(), types.end(), matches.begin(), matches.end());
      Debug("typecheck-idt") << "Return " << range << std::endl;
      return range;
    }
    else
    {
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
      TypeNode t = testType[0];
      Assert(t.isDatatype());
      if (t.isParametricDatatype())
      {
        Debug("typecheck-idt") << "typecheck parameterized tester: " << n
                               << std::endl;
        TypeMatcher m(t);
        if (!m.doMatching(testType[0], childType)) {
          throw TypeCheckingExceptionPrivate(
              n,
              "matching failed for tester argument of parameterized datatype");
        }
      }
      else
      {
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

      TypeMatcher m;
      if (childType.getKind() == kind::CONSTRUCTOR_TYPE) {
        m.addTypesFromDatatype(childType.getConstructorRangeType());
      } else if (childType.getKind() == kind::DATATYPE_TYPE) {
        m.addTypesFromDatatype(childType);
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

class TupleUpdateOpTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::TUPLE_UPDATE_OP);
    return nodeManager->builtinOperatorType();
  }
}; /* class TupleUpdateOpTypeRule */

struct RecordUpdateTypeRule {
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    Assert(n.getKind() == kind::RECORD_UPDATE);
    NodeManagerScope nms(nodeManager);
    const RecordUpdate& ru = n.getOperator().getConst<RecordUpdate>();
    TypeNode recordType = n[0].getType(check);
    TypeNode newValue = n[1].getType(check);
    if (check) {
      if (!recordType.toType().isRecord())
      {
        throw TypeCheckingExceptionPrivate(
            n, "Record-update expression formed over non-record");
      }
      const DType& dt = recordType.getDType();
      const DTypeConstructor& recCons = dt[0];
      if (recCons.getSelectorIndexForName(ru.getField()) == -1)
      {
        std::stringstream ss;
        ss << "Record-update field `" << ru.getField()
           << "' is not a valid field name for the record type";
        throw TypeCheckingExceptionPrivate(n, ss.str().c_str());
      }
    }
    return recordType;
  }
}; /* struct RecordUpdateTypeRule */

class RecordUpdateOpTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::RECORD_UPDATE_OP);
    return nodeManager->builtinOperatorType();
  }
}; /* class RecordUpdateOpTypeRule */

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

class DtBoundTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    if (check) {
      TypeNode t = n[0].getType(check);
      if (!t.isDatatype()) {
        throw TypeCheckingExceptionPrivate(
            n,
            "expecting datatype bound term to have datatype argument.");
      }
      if (n[1].getKind() != kind::CONST_RATIONAL) {
        throw TypeCheckingExceptionPrivate(
            n, "datatype bound must be a constant");
      }
      if (n[1].getConst<Rational>().getNumerator().sgn() == -1) {
        throw TypeCheckingExceptionPrivate(
            n, "datatype bound must be non-negative");
      }
    }
    return nodeManager->booleanType();
  }
}; /* class DtBoundTypeRule */

class DtSygusBoundTypeRule {
 public:
  inline static TypeNode computeType(NodeManager* nodeManager, TNode n,
                                     bool check) {
    if (check) {
      if (!n[0].getType().isDatatype()) {
        throw TypeCheckingExceptionPrivate(
            n, "datatype sygus bound takes a datatype");
      }
      if (n[1].getKind() != kind::CONST_RATIONAL) {
        throw TypeCheckingExceptionPrivate(
            n, "datatype sygus bound must be a constant");
      }
      if (n[1].getConst<Rational>().getNumerator().sgn() == -1) {
        throw TypeCheckingExceptionPrivate(
            n, "datatype sygus bound must be non-negative");
      }
    }
    return nodeManager->booleanType();
  }
}; /* class DtSygusBoundTypeRule */

class DtSyguEvalTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    TypeNode headType = n[0].getType(check);
    if (!headType.isDatatype())
    {
      throw TypeCheckingExceptionPrivate(
          n, "datatype sygus eval takes a datatype head");
    }
    const DType& dt = headType.getDType();
    if (!dt.isSygus())
    {
      throw TypeCheckingExceptionPrivate(
          n, "datatype sygus eval must have a datatype head that is sygus");
    }
    if (check)
    {
      Node svl = dt.getSygusVarList();
      if (svl.getNumChildren() + 1 != n.getNumChildren())
      {
        throw TypeCheckingExceptionPrivate(n,
                                           "wrong number of arguments to a "
                                           "datatype sygus evaluation "
                                           "function");
      }
      for (unsigned i = 0, nvars = svl.getNumChildren(); i < nvars; i++)
      {
        TypeNode vtype = svl[i].getType(check);
        TypeNode atype = n[i + 1].getType(check);
        if (!vtype.isComparableTo(atype))
        {
          throw TypeCheckingExceptionPrivate(
              n,
              "argument type mismatch in a datatype sygus evaluation function");
        }
      }
    }
    return dt.getSygusType();
  }
}; /* class DtSyguEvalTypeRule */

class MatchTypeRule
{
 public:
  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check)
  {
    Assert(n.getKind() == kind::MATCH);

    TypeNode retType;

    TypeNode headType = n[0].getType(check);
    if (!headType.isDatatype())
    {
      throw TypeCheckingExceptionPrivate(n, "expecting datatype head in match");
    }
    const DType& hdt = headType.getDType();

    std::unordered_set<unsigned> patIndices;
    bool patHasVariable = false;
    // the type of a match case list is the least common type of its cases
    for (unsigned i = 1, nchildren = n.getNumChildren(); i < nchildren; i++)
    {
      Node nc = n[i];
      if (check)
      {
        Kind nck = nc.getKind();
        std::unordered_set<Node, NodeHashFunction> bvs;
        if (nck == kind::MATCH_BIND_CASE)
        {
          for (const Node& v : nc[0])
          {
            Assert(v.getKind() == kind::BOUND_VARIABLE);
            bvs.insert(v);
          }
        }
        else if (nck != kind::MATCH_CASE)
        {
          throw TypeCheckingExceptionPrivate(
              n, "expected a match case in match expression");
        }
        // get the pattern type
        unsigned pindex = nck == kind::MATCH_CASE ? 0 : 1;
        TypeNode patType = nc[pindex].getType();
        // should be caught in the above call
        if (!patType.isDatatype())
        {
          throw TypeCheckingExceptionPrivate(
              n, "expecting datatype pattern in match");
        }
        Kind ncpk = nc[pindex].getKind();
        if (ncpk == kind::APPLY_CONSTRUCTOR)
        {
          for (const Node& arg : nc[pindex])
          {
            if (bvs.find(arg) == bvs.end())
            {
              throw TypeCheckingExceptionPrivate(
                  n,
                  "expecting distinct bound variable as argument to "
                  "constructor in pattern of match");
            }
            bvs.erase(arg);
          }
          unsigned ci = utils::indexOf(nc[pindex].getOperator());
          patIndices.insert(ci);
        }
        else if (ncpk == kind::BOUND_VARIABLE)
        {
          patHasVariable = true;
        }
        else
        {
          throw TypeCheckingExceptionPrivate(
              n, "unexpected kind of term in pattern in match");
        }
        const DType& pdt = patType.getDType();
        // compare datatypes instead of the types to catch parametric case,
        // where the pattern has parametric type.
        if (hdt.getTypeNode() != pdt.getTypeNode())
        {
          std::stringstream ss;
          ss << "pattern of a match case does not match the head type in match";
          throw TypeCheckingExceptionPrivate(n, ss.str());
        }
      }
      TypeNode currType = nc.getType(check);
      if (i == 1)
      {
        retType = currType;
      }
      else
      {
        retType = TypeNode::leastCommonTypeNode(retType, currType);
        if (retType.isNull())
        {
          throw TypeCheckingExceptionPrivate(
              n, "incomparable types in match case list");
        }
      }
    }
    if (check)
    {
      if (!patHasVariable && patIndices.size() < hdt.getNumConstructors())
      {
        throw TypeCheckingExceptionPrivate(
            n, "cases for match term are not exhaustive");
      }
    }
    return retType;
  }
}; /* class MatchTypeRule */

class MatchCaseTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::MATCH_CASE);
    if (check)
    {
      TypeNode patType = n[0].getType(check);
      if (!patType.isDatatype())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting datatype pattern in match case");
      }
    }
    return n[1].getType(check);
  }
}; /* class MatchCaseTypeRule */

class MatchBindCaseTypeRule
{
 public:
  inline static TypeNode computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
  {
    Assert(n.getKind() == kind::MATCH_BIND_CASE);
    if (check)
    {
      if (n[0].getKind() != kind::BOUND_VAR_LIST)
      {
        throw TypeCheckingExceptionPrivate(
            n, "expected a bound variable list in match bind case");
      }
      TypeNode patType = n[1].getType(check);
      if (!patType.isDatatype())
      {
        throw TypeCheckingExceptionPrivate(
            n, "expecting datatype pattern in match bind case");
      }
    }
    return n[2].getType(check);
  }
}; /* class MatchBindCaseTypeRule */

} /* CVC4::theory::datatypes namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__DATATYPES__THEORY_DATATYPES_TYPE_RULES_H */
