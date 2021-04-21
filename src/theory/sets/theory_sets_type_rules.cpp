/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Kshitij Bansal, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets theory type rules.
 */

#include "theory/sets/theory_sets_type_rules.h"

#include <climits>
#include <sstream>

#include "theory/sets/normal_form.h"

namespace cvc5 {
namespace theory {
namespace sets {

TypeNode SetsBinaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check)
{
  Assert(n.getKind() == kind::UNION || n.getKind() == kind::INTERSECTION
         || n.getKind() == kind::SETMINUS);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n, "operator expects a set, first argument is not");
    }
    TypeNode secondSetType = n[1].getType(check);
    if (secondSetType != setType)
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind()
         << " expects two sets of the same type. Found types '" << setType
         << "' and '" << secondSetType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return setType;
}

bool SetsBinaryOperatorTypeRule::computeIsConst(NodeManager* nodeManager,
                                                TNode n)
{
  // only UNION has a const rule in kinds.
  // INTERSECTION and SETMINUS are not used in the canonical representation of
  // sets and therefore they do not have const rules in kinds
  Assert(n.getKind() == kind::UNION);
  return NormalForm::checkNormalConstant(n);
}

TypeNode SubsetTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  Assert(n.getKind() == kind::SUBSET);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(n, "set subset operating on non-set");
    }
    TypeNode secondSetType = n[1].getType(check);
    if (secondSetType != setType)
    {
      if (!setType.isComparableTo(secondSetType))
      {
        throw TypeCheckingExceptionPrivate(
            n, "set subset operating on sets of different types");
      }
    }
  }
  return nodeManager->booleanType();
}

TypeNode MemberTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  Assert(n.getKind() == kind::MEMBER);
  TypeNode setType = n[1].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n, "checking for membership in a non-set");
    }
    TypeNode elementType = n[0].getType(check);
    // e.g. (member 1 (singleton 1.0)) is true whereas
    // (member 1.0 (singleton 1)) throws a typing error
    if (!elementType.isSubtypeOf(setType.getSetElementType()))
    {
      std::stringstream ss;
      ss << "member operating on sets of different types:\n"
         << "child type:  " << elementType << "\n"
         << "not subtype: " << setType.getSetElementType() << "\n"
         << "in term : " << n;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return nodeManager->booleanType();
}

TypeNode SingletonTypeRule::computeType(NodeManager* nodeManager,
                                        TNode n,
                                        bool check)
{
  Assert(n.getKind() == kind::SINGLETON && n.hasOperator()
         && n.getOperator().getKind() == kind::SINGLETON_OP);

  SingletonOp op = n.getOperator().getConst<SingletonOp>();
  TypeNode type1 = op.getType();
  if (check)
  {
    TypeNode type2 = n[0].getType(check);
    TypeNode leastCommonType = TypeNode::leastCommonTypeNode(type1, type2);
    // the type of the element should be a subtype of the type of the operator
    // e.g. (singleton (singleton_op Real) 1) where 1 is an Int
    if (leastCommonType.isNull() || leastCommonType != type1)
    {
      std::stringstream ss;
      ss << "The type '" << type2 << "' of the element is not a subtype of '"
         << type1 << "' in term : " << n;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return nodeManager->mkSetType(type1);
}

bool SingletonTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == kind::SINGLETON);
  return n[0].isConst();
}

TypeNode EmptySetTypeRule::computeType(NodeManager* nodeManager,
                                       TNode n,
                                       bool check)
{
  Assert(n.getKind() == kind::EMPTYSET);
  EmptySet emptySet = n.getConst<EmptySet>();
  return emptySet.getType();
}

TypeNode CardTypeRule::computeType(NodeManager* nodeManager,
                                   TNode n,
                                   bool check)
{
  Assert(n.getKind() == kind::CARD);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n, "cardinality operates on a set, non-set object found");
    }
  }
  return nodeManager->integerType();
}

TypeNode ComplementTypeRule::computeType(NodeManager* nodeManager,
                                         TNode n,
                                         bool check)
{
  Assert(n.getKind() == kind::COMPLEMENT);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n, "COMPLEMENT operates on a set, non-set object found");
    }
  }
  return setType;
}

TypeNode UniverseSetTypeRule::computeType(NodeManager* nodeManager,
                                          TNode n,
                                          bool check)
{
  Assert(n.getKind() == kind::UNIVERSE_SET);
  // for nullary operators, we only computeType for check=true, since they are
  // given TypeAttr() on creation
  Assert(check);
  TypeNode setType = n.getType();
  if (!setType.isSet())
  {
    throw TypeCheckingExceptionPrivate(n,
                                       "Non-set type found for universe set");
  }
  return setType;
}

TypeNode ComprehensionTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check)
{
  Assert(n.getKind() == kind::COMPREHENSION);
  if (check)
  {
    if (n[0].getType(check) != nodeManager->boundVarListType())
    {
      throw TypeCheckingExceptionPrivate(
          n, "first argument of set comprehension is not bound var list");
    }
    if (n[1].getType(check) != nodeManager->booleanType())
    {
      throw TypeCheckingExceptionPrivate(
          n, "body of set comprehension is not boolean");
    }
  }
  return nodeManager->mkSetType(n[2].getType(check));
}

TypeNode ChooseTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  Assert(n.getKind() == kind::CHOOSE);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n, "CHOOSE operator expects a set, a non-set is found");
    }
  }
  return setType.getSetElementType();
}

TypeNode IsSingletonTypeRule::computeType(NodeManager* nodeManager,
                                          TNode n,
                                          bool check)
{
  Assert(n.getKind() == kind::IS_SINGLETON);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n, "IS_SINGLETON operator expects a set, a non-set is found");
    }
  }
  return nodeManager->booleanType();
}

TypeNode InsertTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check)
{
  Assert(n.getKind() == kind::INSERT);
  size_t numChildren = n.getNumChildren();
  Assert(numChildren >= 2);
  TypeNode setType = n[numChildren - 1].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(n, "inserting into a non-set");
    }
    for (size_t i = 0; i < numChildren - 1; ++i)
    {
      TypeNode elementType = n[i].getType(check);
      if (elementType != setType.getSetElementType())
      {
        throw TypeCheckingExceptionPrivate(
            n,
            "type of element should be same as element type of set being "
            "inserted into");
      }
    }
  }
  return setType;
}

TypeNode RelBinaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                                TNode n,
                                                bool check)
{
  Assert(n.getKind() == kind::PRODUCT || n.getKind() == kind::JOIN);

  TypeNode firstRelType = n[0].getType(check);
  TypeNode secondRelType = n[1].getType(check);
  TypeNode resultType = firstRelType;

  if (!firstRelType.isSet() || !secondRelType.isSet())
  {
    throw TypeCheckingExceptionPrivate(
        n, " Relational operator operates on non-sets");
  }
  if (!firstRelType[0].isTuple() || !secondRelType[0].isTuple())
  {
    throw TypeCheckingExceptionPrivate(
        n, " Relational operator operates on non-relations (sets of tuples)");
  }

  std::vector<TypeNode> newTupleTypes;
  std::vector<TypeNode> firstTupleTypes = firstRelType[0].getTupleTypes();
  std::vector<TypeNode> secondTupleTypes = secondRelType[0].getTupleTypes();

  // JOIN is not allowed to apply on two unary sets
  if (n.getKind() == kind::JOIN)
  {
    if ((firstTupleTypes.size() == 1) && (secondTupleTypes.size() == 1))
    {
      throw TypeCheckingExceptionPrivate(
          n, " Join operates on two unary relations");
    }
    else if (firstTupleTypes.back() != secondTupleTypes.front())
    {
      throw TypeCheckingExceptionPrivate(
          n, " Join operates on two non-joinable relations");
    }
    newTupleTypes.insert(newTupleTypes.end(),
                         firstTupleTypes.begin(),
                         firstTupleTypes.end() - 1);
    newTupleTypes.insert(newTupleTypes.end(),
                         secondTupleTypes.begin() + 1,
                         secondTupleTypes.end());
  }
  else if (n.getKind() == kind::PRODUCT)
  {
    newTupleTypes.insert(
        newTupleTypes.end(), firstTupleTypes.begin(), firstTupleTypes.end());
    newTupleTypes.insert(
        newTupleTypes.end(), secondTupleTypes.begin(), secondTupleTypes.end());
  }
  resultType = nodeManager->mkSetType(nodeManager->mkTupleType(newTupleTypes));

  return resultType;
}

TypeNode RelTransposeTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check)
{
  Assert(n.getKind() == kind::TRANSPOSE);
  TypeNode setType = n[0].getType(check);
  if (check && (!setType.isSet() || !setType.getSetElementType().isTuple()))
  {
    throw TypeCheckingExceptionPrivate(
        n, "relation transpose operates on non-relation");
  }
  std::vector<TypeNode> tupleTypes = setType[0].getTupleTypes();
  std::reverse(tupleTypes.begin(), tupleTypes.end());
  return nodeManager->mkSetType(nodeManager->mkTupleType(tupleTypes));
}

TypeNode RelTransClosureTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check)
{
  Assert(n.getKind() == kind::TCLOSURE);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet() || !setType.getSetElementType().isTuple())
    {
      throw TypeCheckingExceptionPrivate(
          n, " transitive closure operates on non-relation");
    }
    std::vector<TypeNode> tupleTypes = setType[0].getTupleTypes();
    if (tupleTypes.size() != 2)
    {
      throw TypeCheckingExceptionPrivate(
          n, " transitive closure operates on non-binary relations");
    }
    if (tupleTypes[0] != tupleTypes[1])
    {
      throw TypeCheckingExceptionPrivate(
          n,
          " transitive closure operates on non-homogeneous binary relations");
    }
  }
  return setType;
}

TypeNode JoinImageTypeRule::computeType(NodeManager* nodeManager,
                                        TNode n,
                                        bool check)
{
  Assert(n.getKind() == kind::JOIN_IMAGE);

  TypeNode firstRelType = n[0].getType(check);

  if (!firstRelType.isSet())
  {
    throw TypeCheckingExceptionPrivate(
        n, " JoinImage operator operates on non-relations");
  }
  if (!firstRelType[0].isTuple())
  {
    throw TypeCheckingExceptionPrivate(
        n, " JoinImage operator operates on non-relations (sets of tuples)");
  }

  std::vector<TypeNode> tupleTypes = firstRelType[0].getTupleTypes();
  if (tupleTypes.size() != 2)
  {
    throw TypeCheckingExceptionPrivate(
        n, " JoinImage operates on a non-binary relation");
  }
  TypeNode valType = n[1].getType(check);
  if (valType != nodeManager->integerType())
  {
    throw TypeCheckingExceptionPrivate(
        n, " JoinImage cardinality constraint must be integer");
  }
  std::vector<TypeNode> newTupleTypes;
  newTupleTypes.push_back(tupleTypes[0]);
  return nodeManager->mkSetType(nodeManager->mkTupleType(newTupleTypes));
}

TypeNode RelIdenTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check)
{
  Assert(n.getKind() == kind::IDEN);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet() && !setType.getSetElementType().isTuple())
    {
      throw TypeCheckingExceptionPrivate(n,
                                         " Identity operates on non-relation");
    }
    if (setType[0].getTupleTypes().size() != 1)
    {
      throw TypeCheckingExceptionPrivate(
          n, " Identity operates on non-unary relations");
    }
  }
  std::vector<TypeNode> tupleTypes = setType[0].getTupleTypes();
  tupleTypes.push_back(tupleTypes[0]);
  return nodeManager->mkSetType(nodeManager->mkTupleType(tupleTypes));
}

Cardinality SetsProperties::computeCardinality(TypeNode type)
{
  Assert(type.getKind() == kind::SET_TYPE);
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
}  // namespace cvc5
