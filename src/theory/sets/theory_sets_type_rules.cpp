/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/sets/normal_form.h"
#include "util/cardinality.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/tuple_utils.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

using namespace cvc5::internal::theory::datatypes;

TypeNode SetsBinaryOperatorTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SetsBinaryOperatorTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check,
                                                 std::ostream* errOut)
{
  Assert(n.getKind() == kind::SET_UNION || n.getKind() == kind::SET_INTER
         || n.getKind() == kind::SET_MINUS);
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
  // only SET_UNION has a const rule in kinds.
  // SET_INTER and SET_MINUS are not used in the canonical representation
  // of sets and therefore they do not have const rules in kinds
  Assert(n.getKind() == kind::SET_UNION);
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
  Assert(n.getKind() == kind::SET_SUBSET);
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
      throw TypeCheckingExceptionPrivate(
          n, "set subset operating on sets of different types");
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
  Assert(n.getKind() == kind::SET_MEMBER);
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
    if (elementType != setType.getSetElementType())
    {
      std::stringstream ss;
      ss << "member operating on sets of different types:\n"
         << "child type:  " << elementType << "\n"
         << "not type: " << setType.getSetElementType() << "\n"
         << "in term : " << n;
      throw TypeCheckingExceptionPrivate(n, ss.str());
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
  Assert(n.getKind() == kind::SET_SINGLETON);
  TypeNode type1 = n[0].getType(check);
  return nodeManager->mkSetType(type1);
}

bool SingletonTypeRule::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getKind() == kind::SET_SINGLETON);
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
  Assert(n.getKind() == kind::SET_EMPTY);
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
  Assert(n.getKind() == kind::SET_CARD);
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

TypeNode ComplementTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ComplementTypeRule::computeType(NodeManager* nodeManager,
                                         TNode n,
                                         bool check,
                                         std::ostream* errOut)
{
  Assert(n.getKind() == kind::SET_COMPLEMENT);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n, "SET_COMPLEMENT operates on a set, non-set object found");
    }
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
  Assert(n.getKind() == kind::SET_UNIVERSE);
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

TypeNode ComprehensionTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ComprehensionTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  Assert(n.getKind() == kind::SET_COMPREHENSION);
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

TypeNode ChooseTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode ChooseTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == kind::SET_CHOOSE);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n, "SET_CHOOSE operator expects a set, a non-set is found");
    }
  }
  return setType.getSetElementType();
}

TypeNode IsSingletonTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode IsSingletonTypeRule::computeType(NodeManager* nodeManager,
                                          TNode n,
                                          bool check,
                                          std::ostream* errOut)
{
  Assert(n.getKind() == kind::SET_IS_SINGLETON);
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n, "SET_IS_SINGLETON operator expects a set, a non-set is found");
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
  Assert(n.getKind() == kind::SET_INSERT);
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

TypeNode SetMapTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode SetMapTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  Assert(n.getKind() == kind::SET_MAP);
  TypeNode functionType = n[0].getType(check);
  TypeNode setType = n[1].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "set.map operator expects a set in the second argument, "
          "a non-set is found");
    }

    TypeNode elementType = setType.getSetElementType();

    if (!(functionType.isFunction()))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " *) as a first argument. "
         << "Found a term of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    if (!(argTypes.size() == 1 && argTypes[0] == elementType))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " *). "
         << "Found a function of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  TypeNode rangeType = n[0].getType().getRangeType();
  TypeNode retType = nodeManager->mkSetType(rangeType);
  return retType;
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
  Assert(n.getKind() == kind::SET_FILTER);
  TypeNode functionType = n[0].getType(check);
  TypeNode setType = n[1].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "set.filter operator expects a set in the second argument, "
          "a non-set is found");
    }

    TypeNode elementType = setType.getSetElementType();

    if (!(functionType.isFunction()))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " Bool) as a first argument. "
         << "Found a term of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    NodeManager* nm = NodeManager::currentNM();
    if (!(argTypes.size() == 1 && argTypes[0] == elementType
          && functionType.getRangeType() == nm->booleanType()))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " Bool). "
         << "Found a function of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  return setType;
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
  Assert(n.getKind() == kind::SET_FOLD);
  TypeNode functionType = n[0].getType(check);
  TypeNode initialValueType = n[1].getType(check);
  TypeNode setType = n[2].getType(check);
  if (check)
  {
    if (!setType.isSet())
    {
      throw TypeCheckingExceptionPrivate(
          n,
          "set.fold operator expects a set in the third argument, "
          "a non-set is found");
    }

    TypeNode elementType = setType.getSetElementType();

    if (!(functionType.isFunction()))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " T2 T2) as a first argument. "
         << "Found a term of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    TypeNode rangeType = functionType.getRangeType();
    if (!(argTypes.size() == 2 && argTypes[0] == elementType
          && argTypes[1] == rangeType))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " T2 T2). "
         << "Found a function of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    if (rangeType != initialValueType)
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects an initial value of type "
         << rangeType << ". Found a term of type '" << initialValueType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  TypeNode retType = n[0].getType().getRangeType();
  return retType;
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
  Assert(n.getKind() == kind::RELATION_PRODUCT
         || n.getKind() == kind::RELATION_JOIN);

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

  // RELATION_JOIN is not allowed to apply on two unary sets
  if (n.getKind() == kind::RELATION_JOIN)
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
  else if (n.getKind() == kind::RELATION_PRODUCT)
  {
    newTupleTypes.insert(
        newTupleTypes.end(), firstTupleTypes.begin(), firstTupleTypes.end());
    newTupleTypes.insert(
        newTupleTypes.end(), secondTupleTypes.begin(), secondTupleTypes.end());
  }
  resultType = nodeManager->mkSetType(nodeManager->mkTupleType(newTupleTypes));

  return resultType;
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
  Assert(n.getKind() == kind::RELATION_TRANSPOSE);
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

TypeNode RelTransClosureTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelTransClosureTypeRule::computeType(NodeManager* nodeManager,
                                              TNode n,
                                              bool check,
                                              std::ostream* errOut)
{
  Assert(n.getKind() == kind::RELATION_TCLOSURE);
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

TypeNode JoinImageTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode JoinImageTypeRule::computeType(NodeManager* nodeManager,
                                        TNode n,
                                        bool check,
                                        std::ostream* errOut)
{
  Assert(n.getKind() == kind::RELATION_JOIN_IMAGE);

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
  if (tupleTypes[0] != tupleTypes[1])
  {
    // TODO: Investigate supporting JoinImage for general binary
    // relationshttps://github.com/cvc5/cvc5-projects/issues/346
    throw TypeCheckingExceptionPrivate(
        n, " JoinImage operates on a pair of different types");
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

TypeNode RelIdenTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelIdenTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  Assert(n.getKind() == kind::RELATION_IDEN);
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

TypeNode RelationGroupTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode RelationGroupTypeRule::computeType(NodeManager* nm,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
{
  Assert(n.getKind() == kind::RELATION_GROUP && n.hasOperator()
         && n.getOperator().getKind() == kind::RELATION_GROUP_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();

  TypeNode setType = n[0].getType(check);

  if (check)
  {
    if (!setType.isSet())
    {
      std::stringstream ss;
      ss << "RELATION_GROUP operator expects a relation. Found '" << n[0]
         << "' of type '" << setType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    TypeNode tupleType = setType.getSetElementType();
    if (!tupleType.isTuple())
    {
      std::stringstream ss;
      ss << "RELATION_GROUP operator expects a relation. Found '" << n[0]
         << "' of type '" << setType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    datatypes::TupleUtils::checkTypeIndices(n, tupleType, indices);
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
  Assert(n.getKind() == kind::RELATION_AGGREGATE && n.hasOperator()
         && n.getOperator().getKind() == kind::RELATION_AGGREGATE_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();

  TypeNode functionType = n[0].getType(check);
  TypeNode initialValueType = n[1].getType(check);
  TypeNode setType = n[2].getType(check);

  if (check)
  {
    if (!setType.isSet())
    {
      std::stringstream ss;
      ss << "RELATION_AGGREGATE operator expects a set. Found '" << n[2]
         << "' of type '" << setType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    TypeNode tupleType = setType.getSetElementType();
    if (!tupleType.isTuple())
    {
      std::stringstream ss;
      ss << "RELATION_AGGREGATE operator expects a relation. Found '" << n[2]
         << "' of type '" << setType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    TupleUtils::checkTypeIndices(n, tupleType, indices);

    TypeNode elementType = setType.getSetElementType();

    if (!(functionType.isFunction()))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " T T) as a first argument. "
         << "Found a term of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    std::vector<TypeNode> argTypes = functionType.getArgTypes();
    TypeNode rangeType = functionType.getRangeType();
    if (!(argTypes.size() == 2 && argTypes[0] == elementType
          && argTypes[1] == rangeType))
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects a function of type  (-> "
         << elementType << " T T). "
         << "Found a function of type '" << functionType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    if (rangeType != initialValueType)
    {
      std::stringstream ss;
      ss << "Operator " << n.getKind() << " expects an initial value of type "
         << rangeType << ". Found a term of type '" << initialValueType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
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
  Assert(n.getKind() == kind::RELATION_PROJECT && n.hasOperator()
         && n.getOperator().getKind() == kind::RELATION_PROJECT_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();
  TypeNode setType = n[0].getType(check);
  if (check)
  {
    if (n.getNumChildren() != 1)
    {
      std::stringstream ss;
      ss << "operands in term " << n << " are " << n.getNumChildren()
         << ", but RELATION_PROJECT expects 1 operand.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    if (!setType.isSet())
    {
      std::stringstream ss;
      ss << "RELATION_PROJECT operator expects a set. Found '" << n[0]
         << "' of type '" << setType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    TypeNode tupleType = setType.getSetElementType();
    if (!tupleType.isTuple())
    {
      std::stringstream ss;
      ss << "RELATION_PROJECT operator expects a relation. Found '" << n[0]
         << "' of type '" << setType << "'.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }

    // make sure all indices are less than the length of the tuple type
    DType dType = tupleType.getDType();
    DTypeConstructor constructor = dType[0];
    size_t numArgs = constructor.getNumArgs();
    for (uint32_t index : indices)
    {
      std::stringstream ss;
      if (index >= numArgs)
      {
        ss << "Index " << index << " in term " << n << " is >= " << numArgs
           << " which is the number of columns in " << n[0] << ".";
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
  }
  TypeNode tupleType = setType.getSetElementType();
  TypeNode retTupleType =
      TupleUtils::getTupleProjectionType(indices, tupleType);
  return nm->mkSetType(retTupleType);
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
}  // namespace cvc5::internal
