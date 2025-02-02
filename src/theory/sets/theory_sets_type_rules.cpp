/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets theory type rules.
 */

#include "theory/sets/theory_sets_type_rules.h"

#include <sstream>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "theory/bags/bags_utils.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/sets/normal_form.h"
#include "util/cardinality.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

using namespace cvc5::internal::theory::datatypes;

bool isMaybeRelation(const TypeNode& tn)
{
  // if not a set type
  if (!tn.isMaybeKind(Kind::SET_TYPE))
  {
    return false;
  }
  // if a concrete set type whose element type is not a tuple type
  if (tn.isSet() && !tn[0].isMaybeKind(Kind::TUPLE_TYPE))
  {
    return false;
  }
  return true;
}

bool checkFunctionTypeFor(const Node& n,
                          const TypeNode& functionType,
                          const TypeNode& setType,
                          std::ostream* errOut)
{
  // get the element type of the second argument, if it exists
  TypeNode elementType;
  if (setType.isSet())
  {
    elementType = setType.getSetElementType();
  }
  if (!functionType.isMaybeKind(Kind::FUNCTION_TYPE))
  {
    if (errOut)
    {
      (*errOut) << "Operator " << n.getKind()
                << " expects a function as a first argument. "
                << "Found a term of type '" << functionType << "'.";
    }
    return false;
  }
  // note that if functionType is abstract, we don't check whether it
  // matches the argument.
  if (functionType.isFunction())
  {
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    if (!(argTypes.size() == 1
          && (elementType.isNull() || argTypes[0].isComparableTo(elementType))))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function whose type is comparable to the "
                     "type of elements in the set";
        if (!elementType.isNull())
        {
          (*errOut) << " (" << elementType << ")";
        }
        (*errOut) << ". Found a function of type '" << functionType << "'.";
      }
      return false;
    }
  }
  return true;
}

TypeNode SetsBinaryOperatorTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SetsBinaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check,
                                                 std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_UNION || n.getKind() == Kind::SET_INTER
         || n.getKind() == Kind::SET_MINUS);
  TypeNode setType = n[0].getTypeOrNull();
  TypeNode secondSetType = n[1].getTypeOrNull();
  TypeNode retType = setType.leastUpperBound(secondSetType);
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE)
        || !secondSetType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "operator expects a set, argument is not";
      }
      return TypeNode::null();
    }
  }
  if (retType.isNull())
  {
    if (errOut)
    {
      (*errOut) << "Operator " << n.getKind()
                << " expects two sets of comparable type. Found types '"
                << setType << "' and '" << secondSetType << "'.";
    }
    return TypeNode::null();
  }
  // we are ?Set if both children are fully abstract
  if (retType.isFullyAbstract())
  {
    return nodeManager->mkAbstractType(Kind::SET_TYPE);
  }
  return retType;
}

bool SetsBinaryOperatorTypeRule::computeIsConst(NodeManager* nodeManager,
                                                TNode n)
{
  // only SET_UNION has a const rule in kinds.
  // SET_INTER and SET_MINUS are not used in the canonical representation
  // of sets and therefore they do not have const rules in kinds
  Assert(n.getKind() == Kind::SET_UNION);
  return NormalForm::checkNormalConstant(n);
}

TypeNode SubsetTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode SubsetTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_SUBSET);
  TypeNode setType = n[0].getTypeOrNull();
  if (check)
  {
    TypeNode secondSetType = n[1].getTypeOrNull();
    if (!setType.isMaybeKind(Kind::SET_TYPE)
        || !secondSetType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "set subset operating on non-set";
      }
      return TypeNode::null();
    }
    if (!secondSetType.isComparableTo(setType))
    {
      if (errOut)
      {
        (*errOut) << "set subset operating on sets of incomparable types";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode MemberTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode MemberTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_MEMBER);
  TypeNode setType = n[1].getTypeOrNull();
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "checking for membership in a non-set";
      }
      return TypeNode::null();
    }
    TypeNode elementType = n[0].getTypeOrNull();
    if (!elementType.isComparableTo(setType.getSetElementType()))
    {
      if (errOut)
      {
        (*errOut) << "member operating on sets of different types:\n"
                  << "child type:  " << elementType << "\n"
                  << "not type: " << setType.getSetElementType() << "\n"
                  << "in term : " << n;
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode SingletonTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SingletonTypeRule::computeType(NodeManager* nodeManager,
                                        TNode n,
                                        bool check,
                                        std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_SINGLETON);
  TypeNode type1 = n[0].getTypeOrNull();
  return nodeManager->mkSetType(type1);
}

bool SingletonTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == Kind::SET_SINGLETON);
  return n[0].isConst();
}

TypeNode EmptySetTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode EmptySetTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check,
                                       std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_EMPTY);
  EmptySet emptySet = n.getConst<EmptySet>();
  return emptySet.getType();
}

TypeNode CardTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->integerType();
}
TypeNode CardTypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check,
                                   std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_CARD);
  TypeNode setType = n[0].getTypeOrNull();
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "cardinality operates on a set, non-set object found";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->integerType();
}

TypeNode ComplementTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ComplementTypeRule::computeType(NodeManager* nodeManager,
                                         TNode n,
                                         bool check,
                                         std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_COMPLEMENT);
  TypeNode setType = n[0].getTypeOrNull();
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "SET_COMPLEMENT operates on a set, non-set object found";
      }
      return TypeNode::null();
    }
  }
  // we are ?Set if argument is ?
  if (setType.isFullyAbstract())
  {
    return nodeManager->mkAbstractType(Kind::SET_TYPE);
  }
  return setType;
}

TypeNode UniverseSetTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode UniverseSetTypeRule::computeType(NodeManager* nodeManager,
                                          TNode n,
                                          bool check,
                                          std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_UNIVERSE);
  // for nullary operators, we only computeType for check=true, since they are
  // given TypeAttr() on creation
  Assert(check);
  TypeNode setType = n.getTypeOrNull();
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "Non-set type found for universe set";
      }
      return TypeNode::null();
    }
  }
  return setType;
}

TypeNode ComprehensionTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ComprehensionTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_COMPREHENSION);
  if (check)
  {
    if (n[0].getKind() != Kind::BOUND_VAR_LIST)
    {
      if (errOut)
      {
        (*errOut)
            << "first argument of set comprehension is not bound var list";
      }
      return TypeNode::null();
    }
    TypeNode bt = n[1].getTypeOrNull();
    if (!bt.isBoolean() && !bt.isFullyAbstract())
    {
      if (errOut)
      {
        (*errOut) << "body of set comprehension is not Boolean";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->mkSetType(n[2].getTypeOrNull());
}

TypeNode ChooseTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ChooseTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_CHOOSE);
  TypeNode setType = n[0].getTypeOrNull();
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "SET_CHOOSE operator expects a set, a non-set is found";
      }
      return TypeNode::null();
    }
  }
  if (setType.isAbstract())
  {
    // don't know the element type, return the fully abstract type
    return nodeManager->mkAbstractType(Kind::ABSTRACT_TYPE);
  }
  return setType.getSetElementType();
}

TypeNode IsSetTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode IsSetTypeRule::computeType(NodeManager* nodeManager,
                                    TNode n,
                                    bool check,
                                    std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_IS_EMPTY
         || n.getKind() == Kind::SET_IS_SINGLETON);
  TypeNode setType = n[0].getTypeOrNull();
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << n.getKind()
                  << " operator expects a set, a non-set is found";
      }
      return TypeNode::null();
    }
  }
  return nodeManager->booleanType();
}

TypeNode InsertTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode InsertTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_INSERT);
  size_t numChildren = n.getNumChildren();
  Assert(numChildren >= 2);
  TypeNode setType = n[numChildren - 1].getTypeOrNull();
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "inserting into a non-set";
      }
      return TypeNode::null();
    }
  }
  // returned element type, which is the join of all elements and the element
  // type of the set (if it exists).
  TypeNode retElementType;
  if (setType.isSet())
  {
    retElementType = setType.getSetElementType();
  }
  for (size_t i = 0; i < numChildren - 1; ++i)
  {
    TypeNode elementType = n[i].getTypeOrNull();
    retElementType = retElementType.isNull()
                         ? elementType
                         : retElementType.leastUpperBound(elementType);
    if (retElementType.isNull())
    {
      if (errOut)
      {
        (*errOut) << "type of element should be same as element type of set "
                     "being inserted into";
      }
      return TypeNode::null();
    }
  }
  Assert(!retElementType.isNull());
  return nodeManager->mkSetType(retElementType);
}

TypeNode SetMapTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SetMapTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_MAP);
  TypeNode functionType = n[0].getTypeOrNull();
  TypeNode setType = n[1].getTypeOrNull();
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "set.map operator expects a set in the second argument, "
                     "a non-set is found";
      }
      return TypeNode::null();
    }
    if (!checkFunctionTypeFor(n, functionType, setType, errOut))
    {
      return TypeNode::null();
    }
  }
  TypeNode rangeType;
  if (functionType.isFunction())
  {
    rangeType = functionType.getRangeType();
  }
  else
  {
    // if an abstract function, the element type is fully abstract
    rangeType = nodeManager->mkAbstractType(Kind::ABSTRACT_TYPE);
  }
  return nodeManager->mkSetType(rangeType);
}

TypeNode SetFilterTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SetFilterTypeRule::computeType(NodeManager* nodeManager,
                                        TNode n,
                                        bool check,
                                        std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_FILTER);
  TypeNode functionType = n[0].getTypeOrNull();
  TypeNode setType = n[1].getTypeOrNull();
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "set.filter operator expects a set in the second "
                     "argument, a non-set is found";
      }
      return TypeNode::null();
    }
    if (!checkFunctionTypeFor(n, functionType, setType, errOut))
    {
      return TypeNode::null();
    }
    if (functionType.isFunction())
    {
      TypeNode rangeType = functionType.getRangeType();
      if (!rangeType.isBoolean() && !rangeType.isFullyAbstract())
      {
        if (errOut)
        {
          (*errOut) << "Operator set.filter expects a function returning Bool.";
        }
        return TypeNode::null();
      }
    }
  }
  return setType;
}

TypeNode SetAllSomeTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}

TypeNode SetAllSomeTypeRule::computeType(NodeManager* nodeManager,
                                         TNode n,
                                         bool check,
                                         std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_ALL || n.getKind() == Kind::SET_SOME);
  std::string op = n.getKind() == Kind::SET_ALL ? "set.all" : "set.some";
  TypeNode functionType = n[0].getTypeOrNull();
  TypeNode setType = n[1].getTypeOrNull();
  if (check)
  {
    if (!setType.isMaybeKind(Kind::SET_TYPE))
    {
      if (errOut)
      {
        (*errOut) << op
                  << " operator expects a set in the second "
                     "argument, a non-set is found";
      }
      return TypeNode::null();
    }
    if (!checkFunctionTypeFor(n, functionType, setType, errOut))
    {
      return TypeNode::null();
    }
    if (functionType.isFunction())
    {
      TypeNode rangeType = functionType.getRangeType();
      if (!rangeType.isBoolean() && !rangeType.isFullyAbstract())
      {
        if (errOut)
        {
          (*errOut) << "Operator " << op
                    << " expects a function returning Bool.";
        }
        return TypeNode::null();
      }
    }
  }
  return nodeManager->booleanType();
}

TypeNode SetFoldTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SetFoldTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  Assert(n.getKind() == Kind::SET_FOLD);
  TypeNode functionType = n[0].getTypeOrNull();
  TypeNode setType = n[2].getTypeOrNull();
  if (check)
  {
    if (!setType.isSet())
    {
      if (errOut)
      {
        (*errOut) << "set.fold operator expects a set in the third argument, "
                     "a non-set is found";
      }
      return TypeNode::null();
    }

    TypeNode elementType = setType.getSetElementType();

    if (!functionType.isFunction())
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType
                  << " T2 T2) as a first argument. "
                  << "Found a term of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    TypeNode rangeType = functionType.getRangeType();
    if (!(argTypes.size() == 2 && argTypes[0] == elementType
          && argTypes[1] == rangeType))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function of type  (-> " << elementType
                  << " T2 T2). "
                  << "Found a function of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
    TypeNode initialValueType = n[1].getTypeOrNull();
    if (rangeType != initialValueType)
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects an initial value of type " << rangeType
                  << ". Found a term of type '" << initialValueType << "'.";
      }
      return TypeNode::null();
    }
  }
  if (functionType.isAbstract())
  {
    // if an abstract function, the element type is fully abstract
    return nodeManager->mkAbstractType(Kind::ABSTRACT_TYPE);
  }
  return functionType.getRangeType();
}

TypeNode RelBinaryOperatorTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelBinaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                                TNode n,
                                                bool check,
                                                std::ostream* errOut)
{
  Assert(n.getKind() == Kind::RELATION_PRODUCT
         || n.getKind() == Kind::RELATION_JOIN);

  TypeNode firstRelType = n[0].getTypeOrNull();
  TypeNode secondRelType = n[1].getTypeOrNull();
  TypeNode resultType = firstRelType;
  if (check)
  {
    if (!isMaybeRelation(firstRelType) || !isMaybeRelation(secondRelType))

    {
      if (errOut)
      {
        (*errOut)
            << "Relational operator operates on non-relations (sets of tuples)";
      }
      return TypeNode::null();
    }
  }

  if (firstRelType.isRelation() && secondRelType.isRelation())
  {
    std::vector<TypeNode> newTupleTypes;
    std::vector<TypeNode> firstTupleTypes = firstRelType[0].getTupleTypes();
    std::vector<TypeNode> secondTupleTypes = secondRelType[0].getTupleTypes();
    // RELATION_JOIN is not allowed to apply on two unary sets
    if (n.getKind() == Kind::RELATION_JOIN)
    {
      if ((firstTupleTypes.size() == 1) && (secondTupleTypes.size() == 1))
      {
        if (errOut)
        {
          (*errOut) << "Join operates on two unary relations";
        }
        return TypeNode::null();
      }
      else if (firstTupleTypes.back() != secondTupleTypes.front())
      {
        if (errOut)
        {
          (*errOut) << "Join operates on two non-joinable relations";
        }
        return TypeNode::null();
      }
      newTupleTypes.insert(newTupleTypes.end(),
                           firstTupleTypes.begin(),
                           firstTupleTypes.end() - 1);
      newTupleTypes.insert(newTupleTypes.end(),
                           secondTupleTypes.begin() + 1,
                           secondTupleTypes.end());
    }
    else if (n.getKind() == Kind::RELATION_PRODUCT)
    {
      newTupleTypes.insert(
          newTupleTypes.end(), firstTupleTypes.begin(), firstTupleTypes.end());
      newTupleTypes.insert(newTupleTypes.end(),
                           secondTupleTypes.begin(),
                           secondTupleTypes.end());
    }
    resultType =
        nodeManager->mkSetType(nodeManager->mkTupleType(newTupleTypes));
  }
  else
  {
    // otherwise, an abstract relation type
    resultType =
        nodeManager->mkSetType(nodeManager->mkAbstractType(Kind::TUPLE_TYPE));
  }
  return resultType;
}

TypeNode RelationTableJoinTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelationTableJoinTypeRule::computeType(NodeManager* nm,
                                                TNode n,
                                                bool check,
                                                std::ostream* errOut)
{
  Assert(n.getKind() == Kind::RELATION_TABLE_JOIN && n.hasOperator()
         && n.getOperator().getKind() == Kind::RELATION_TABLE_JOIN_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();
  Node A = n[0];
  Node B = n[1];
  TypeNode aType = A.getType();
  TypeNode bType = B.getType();

  if (check)
  {
    if (!(aType.isSet() && bType.isSet()))
    {
      std::stringstream ss;
      ss << "RELATION_TABLE_JOIN operator expects two relations. Found '"
         << n[0] << "', '" << n[1] << "' of types '" << aType << "', '" << bType
         << "' respectively. ";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    TypeNode aTupleType = aType.getSetElementType();
    TypeNode bTupleType = bType.getSetElementType();
    if (!(aTupleType.isTuple() && bTupleType.isTuple()))
    {
      std::stringstream ss;
      ss << "RELATION_TABLE_JOIN operator expects two relations. Found '"
         << n[0] << "', '" << n[1] << "' of types '" << aType << "', '" << bType
         << "' respectively. ";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    if (indices.size() % 2 != 0)
    {
      std::stringstream ss;
      ss << "RELATION_TABLE_JOIN operator expects even number of indices. "
            "Found "
         << indices.size() << " in term " << n;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    auto [aIndices, bIndices] = bags::BagsUtils::splitTableJoinIndices(n);
    if (!TupleUtils::checkTypeIndices(aTupleType, aIndices))
    {
      if (errOut)
      {
        (*errOut) << "Index in operator of " << n
                  << " is out of range for the type of its first argument";
      }
      return TypeNode::null();
    }
    if (!TupleUtils::checkTypeIndices(bTupleType, bIndices))
    {
      if (errOut)
      {
        (*errOut) << "Index in operator of " << n
                  << " is out of range for the type of its second argument";
      }
      return TypeNode::null();
    }

    // check the types of columns
    std::vector<TypeNode> aTypes = aTupleType.getTupleTypes();
    std::vector<TypeNode> bTypes = bTupleType.getTupleTypes();
    for (uint32_t i = 0; i < aIndices.size(); i++)
    {
      if (aTypes[aIndices[i]] != bTypes[bIndices[i]])
      {
        std::stringstream ss;
        ss << "RELATION_TABLE_JOIN operator expects column " << aIndices[i]
           << " in relation " << n[0] << " to match column " << bIndices[i]
           << " in relation " << n[1] << ". But their types are "
           << aTypes[aIndices[i]] << " and " << bTypes[bIndices[i]]
           << "' respectively. ";
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
  }
  TypeNode aTupleType = aType.getSetElementType();
  TypeNode bTupleType = bType.getSetElementType();
  TypeNode retTupleType = TupleUtils::concatTupleTypes(aTupleType, bTupleType);
  return nm->mkSetType(retTupleType);
}

TypeNode RelTransposeTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelTransposeTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getKind() == Kind::RELATION_TRANSPOSE);
  TypeNode setType = n[0].getTypeOrNull();
  if (check && !isMaybeRelation(setType))
  {
    if (errOut)
    {
      (*errOut) << "relation transpose operates on non-relation";
    }
    return TypeNode::null();
  }
  // transpose for ? is abstract relation.
  if (setType.isAbstract())
  {
    return nodeManager->mkSetType(
        nodeManager->mkAbstractType(Kind::TUPLE_TYPE));
  }
  // otherwise, reverse the types
  std::vector<TypeNode> tupleTypes = setType[0].getTupleTypes();
  std::reverse(tupleTypes.begin(), tupleTypes.end());
  return nodeManager->mkSetType(nodeManager->mkTupleType(tupleTypes));
}

TypeNode RelTransClosureTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelTransClosureTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  Assert(n.getKind() == Kind::RELATION_TCLOSURE);
  TypeNode setType = n[0].getTypeOrNull();
  if (check)
  {
    if (!isMaybeRelation(setType))
    {
      if (errOut)
      {
        (*errOut) << "transitive closure operates on non-relation";
      }
      return TypeNode::null();
    }
    if (setType.isRelation())
    {
      std::vector<TypeNode> tupleTypes = setType[0].getTupleTypes();
      if (tupleTypes.size() != 2)
      {
        if (errOut)
        {
          (*errOut) << "transitive closure operates on non-binary relation";
        }
        return TypeNode::null();
      }
      if (!tupleTypes[0].isComparableTo(tupleTypes[1]))
      {
        if (errOut)
        {
          (*errOut)
              << "transitive closure operates on incompatible binary relation";
        }
        return TypeNode::null();
      }
    }
  }
  // return abstract relation if argument is ?
  if (setType.isFullyAbstract())
  {
    return nodeManager->mkSetType(
        nodeManager->mkAbstractType(Kind::TUPLE_TYPE));
  }
  return setType;
}

TypeNode JoinImageTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode JoinImageTypeRule::computeType(NodeManager* nodeManager,
                                        TNode n,
                                        bool check,
                                        std::ostream* errOut)
{
  Assert(n.getKind() == Kind::RELATION_JOIN_IMAGE);

  TypeNode firstRelType = n[0].getTypeOrNull();

  if (!isMaybeRelation(firstRelType))
  {
    if (errOut)
    {
      (*errOut) << "JoinImage operator operates on non-relations";
    }
    return TypeNode::null();
  }
  if (!firstRelType.isRelation())
  {
    // abstract relation if the argument is not concreate
    return nodeManager->mkSetType(
        nodeManager->mkAbstractType(Kind::TUPLE_TYPE));
  }
  std::vector<TypeNode> tupleTypes = firstRelType[0].getTupleTypes();
  if (check)
  {
    if (tupleTypes.size() != 2)
    {
      if (errOut)
      {
        (*errOut) << "JoinImage operates on a non-binary relation";
      }
      return TypeNode::null();
    }
    if (!tupleTypes[0].isComparableTo(tupleTypes[1]))
    {
      // TODO: Investigate supporting JoinImage for general binary
      // relations https://github.com/cvc5/cvc5-projects/issues/346
      if (errOut)
      {
        (*errOut) << "JoinImage operates on a pair of different types";
      }
      return TypeNode::null();
    }
    TypeNode valType = n[1].getTypeOrNull();
    if (!valType.isInteger() && !valType.isFullyAbstract())
    {
      if (errOut)
      {
        (*errOut) << "JoinImage cardinality constraint must be integer";
      }
      return TypeNode::null();
    }
  }
  std::vector<TypeNode> newTupleTypes;
  newTupleTypes.push_back(tupleTypes[0]);
  return nodeManager->mkSetType(nodeManager->mkTupleType(newTupleTypes));
}

TypeNode RelIdenTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelIdenTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  Assert(n.getKind() == Kind::RELATION_IDEN);
  TypeNode setType = n[0].getTypeOrNull();
  if (check)
  {
    if (!isMaybeRelation(setType))
    {
      if (errOut)
      {
        (*errOut) << "Identity operates on non-relation";
      }
      return TypeNode::null();
    }
    if (setType.isRelation())
    {
      if (setType[0].getTupleTypes().size() != 1)
      {
        if (errOut)
        {
          (*errOut) << "Identity operates on non-unary relations";
        }
        return TypeNode::null();
      }
    }
  }
  // abstract relation if argument is not a concrete relation type
  if (!setType.isRelation())
  {
    return nodeManager->mkSetType(
        nodeManager->mkAbstractType(Kind::TUPLE_TYPE));
  }
  std::vector<TypeNode> tupleTypes = setType[0].getTupleTypes();
  tupleTypes.push_back(tupleTypes[0]);
  return nodeManager->mkSetType(nodeManager->mkTupleType(tupleTypes));
}

TypeNode RelationGroupTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelationGroupTypeRule::computeType(NodeManager* nm,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  Assert(n.getKind() == Kind::RELATION_GROUP && n.hasOperator()
         && n.getOperator().getKind() == Kind::RELATION_GROUP_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();

  TypeNode setType = n[0].getTypeOrNull();

  if (check)
  {
    if (!isMaybeRelation(setType))
    {
      if (errOut)
      {
        (*errOut) << "RELATION_GROUP operator expects a relation. Found '"
                  << n[0] << "' of type '" << setType << "'.";
      }
      return TypeNode::null();
    }
    if (setType.isRelation())
    {
      TypeNode tupleType = setType[0];
      if (!datatypes::TupleUtils::checkTypeIndices(tupleType, indices))
      {
        if (errOut)
        {
          (*errOut) << "Index in operator of " << n
                    << " is out of range for the type of its arguments";
        }
        return TypeNode::null();
      }
    }
  }
  // we know the argument should be a relation, thus we ensure it has at least
  // that information before constructing the return type
  if (!setType.isRelation())
  {
    setType = nm->mkSetType(nm->mkAbstractType(Kind::TUPLE_TYPE));
  }
  return nm->mkSetType(setType);
}

TypeNode RelationAggregateTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelationAggregateTypeRule::computeType(NodeManager* nm,
                                                TNode n,
                                                bool check,
                                                std::ostream* errOut)
{
  Assert(n.getKind() == Kind::RELATION_AGGREGATE && n.hasOperator()
         && n.getOperator().getKind() == Kind::RELATION_AGGREGATE_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();

  TypeNode functionType = n[0].getTypeOrNull();

  if (check)
  {
    TypeNode setType = n[2].getTypeOrNull();
    if (!isMaybeRelation(setType))
    {
      if (errOut)
      {
        (*errOut) << "RELATION_AGGREGATE operator expects a relation. Found '"
                  << n[2] << "' of type '" << setType << "'.";
      }
      return TypeNode::null();
    }
    TypeNode tupleType;
    if (setType.isRelation())
    {
      tupleType = setType.getSetElementType();
      if (!TupleUtils::checkTypeIndices(tupleType, indices))
      {
        if (errOut)
        {
          (*errOut) << "Index in operator of " << n
                    << " is out of range for the type of its arguments";
        }
        return TypeNode::null();
      }
    }
    if (!functionType.isMaybeKind(Kind::FUNCTION_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "Operator " << n.getKind()
                  << " expects a function as a first argument. "
                  << "Found a term of type '" << functionType << "'.";
      }
      return TypeNode::null();
    }
    if (functionType.isFunction())
    {
      std::vector<TypeNode> argTypes = functionType.getArgTypes();
      TypeNode rangeType = functionType.getRangeType();
      if (!(argTypes.size() == 2
            && (tupleType.isNull() || argTypes[0].isComparableTo(tupleType))
            && argTypes[1].isComparableTo(rangeType)))
      {
        if (errOut)
        {
          (*errOut) << "Operator " << n.getKind()
                    << " expects a function of type (-> ";
          if (!tupleType.isNull())
          {
            (*errOut) << tupleType;
          }
          else
          {
            (*errOut) << "?";
          }
          (*errOut) << " T T). ";
          (*errOut) << "Found a function of type '" << functionType << "'.";
        }
        return TypeNode::null();
      }
      TypeNode initialValueType = n[1].getTypeOrNull();
      if (!rangeType.isComparableTo(initialValueType))
      {
        if (errOut)
        {
          (*errOut) << "Operator " << n.getKind()
                    << " expects an initial value of type " << rangeType
                    << ". Found a term of type '" << initialValueType << "'.";
        }
        return TypeNode::null();
      }
    }
  }
  if (functionType.isAbstract())
  {
    // if an abstract function, return ?Set
    return nm->mkSetType(nm->mkAbstractType(Kind::ABSTRACT_TYPE));
  }
  return nm->mkSetType(functionType.getRangeType());
}

TypeNode RelationProjectTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelationProjectTypeRule::computeType(NodeManager* nm,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  Assert(n.getKind() == Kind::RELATION_PROJECT && n.hasOperator()
         && n.getOperator().getKind() == Kind::RELATION_PROJECT_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();
  TypeNode setType = n[0].getTypeOrNull();
  if (check)
  {
    if (!isMaybeRelation(setType))
    {
      if (errOut)
      {
        (*errOut) << "RELATION_PROJECT operator expects a relation. Found '"
                  << n[0] << "' of type '" << setType << "'.";
      }
      return TypeNode::null();
    }
    if (setType.isRelation())
    {
      TypeNode tupleType = setType.getSetElementType();
      // make sure all indices are less than the length of the tuple type
      const DType& dType = tupleType.getDType();
      const DTypeConstructor& constructor = dType[0];
      size_t numArgs = constructor.getNumArgs();
      for (uint32_t index : indices)
      {
        if (index >= numArgs)
        {
          if (errOut)
          {
            (*errOut) << "Index " << index << " in term " << n
                      << " is >= " << numArgs
                      << " which is the number of columns in " << n[0] << ".";
          }
          return TypeNode::null();
        }
      }
    }
  }
  // abstract relation type if applied to abstract argument
  if (setType.isAbstract())
  {
    return nm->mkSetType(nm->mkAbstractType(Kind::TUPLE_TYPE));
  }
  TypeNode tupleType = setType.getSetElementType();
  TypeNode retTupleType =
      TupleUtils::getTupleProjectionType(indices, tupleType);
  return nm->mkSetType(retTupleType);
}

TypeNode SetEmptyOfTypeTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode SetEmptyOfTypeTypeRule::computeType(NodeManager* nm,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  return nm->mkAbstractType(Kind::SET_TYPE);
}

Cardinality SetsProperties::computeCardinality(TypeNode type)
{
  Assert(type.getKind() == Kind::SET_TYPE);
  Cardinality elementCard = 2;
  elementCard ^= type[0].getCardinality();
  return elementCard;
}

bool SetsProperties::isWellFounded(TypeNode type)
{
  return type[0].isWellFounded();
}

Node SetsProperties::mkGroundTerm(TypeNode type)
{
  Assert(type.isSet());
  return NodeManager::currentNM()->mkConst(EmptySet(type));
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
