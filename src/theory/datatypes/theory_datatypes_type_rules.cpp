/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Typing and cardinality rules for the theory of datatypes.
 */

#include "theory/datatypes/theory_datatypes_type_rules.h"

#include <sstream>

#include "expr/ascription_type.h"
#include "expr/codatatype_bound_variable.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/type_matcher.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/datatypes/tuple_utils.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace datatypes {

TypeNode DatatypeConstructorTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode DatatypeConstructorTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check,
                                                  std::ostream* errOut)
{
  Assert(n.getKind() == kind::APPLY_CONSTRUCTOR);
  TypeNode consType = n.getOperator().getType(check);
  if (!consType.isDatatypeConstructor())
  {
    throw TypeCheckingExceptionPrivate(n, "expected constructor to apply");
  }
  TypeNode t = consType.getDatatypeConstructorRangeType();
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
    Trace("typecheck-idt") << "typecheck parameterized datatype " << n
                           << std::endl;
    TypeMatcher m(t);
    for (; child_it != child_it_end; ++child_it, ++tchild_it)
    {
      TypeNode childType = (*child_it).getType(check);
      if (!m.doMatching(*tchild_it, childType))
      {
        throw TypeCheckingExceptionPrivate(
            n, "matching failed for parameterized constructor");
      }
    }
    std::vector<TypeNode> instTypes;
    m.getMatches(instTypes);
    TypeNode range = t.instantiate(instTypes);
    Trace("typecheck-idt") << "Return (constructor) " << range << " for " << n
                           << std::endl;
    return range;
  }
  else
  {
    if (check)
    {
      Trace("typecheck-idt")
          << "typecheck cons: " << n << " " << n.getNumChildren() << std::endl;
      Trace("typecheck-idt") << "cons type: " << consType << " "
                             << consType.getNumChildren() << std::endl;
      for (; child_it != child_it_end; ++child_it, ++tchild_it)
      {
        TypeNode childType = (*child_it).getType(check);
        Trace("typecheck-idt") << "typecheck cons arg: " << childType << " "
                               << (*tchild_it) << std::endl;
        TypeNode argumentType = *tchild_it;
        if (childType != argumentType)
        {
          std::stringstream ss;
          ss << "bad type for constructor argument:\n"
             << "child type:  " << childType << "\n"
             << "not type: " << argumentType << "\n"
             << "in term : " << n;
          throw TypeCheckingExceptionPrivate(n, ss.str());
        }
      }
    }
    return consType.getDatatypeConstructorRangeType();
  }
}

bool DatatypeConstructorTypeRule::computeIsConst(NodeManager* nodeManager,
                                                 TNode n)
{
  Assert(n.getKind() == kind::APPLY_CONSTRUCTOR);
  for (TNode::const_iterator i = n.begin(); i != n.end(); ++i)
  {
    if (!(*i).isConst())
    {
      return false;
    }
  }
  return true;
}

TypeNode DatatypeSelectorTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode DatatypeSelectorTypeRule::computeType(NodeManager* nodeManager,
                                               TNode n,
                                               bool check,
                                               std::ostream* errOut)
{
  Assert(n.getKind() == kind::APPLY_SELECTOR);
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
    Trace("typecheck-idt") << "typecheck parameterized sel: " << n << std::endl;
    TypeMatcher m(t);
    TypeNode childType = n[0].getType(check);
    if (!childType.isInstantiatedDatatype())
    {
      throw TypeCheckingExceptionPrivate(
          n, "Datatype type not fully instantiated");
    }
    if (!m.doMatching(selType[0], childType))
    {
      throw TypeCheckingExceptionPrivate(
          n, "matching failed for selector argument of parameterized datatype");
    }
    std::vector<TypeNode> types, matches;
    m.getTypes(types);
    m.getMatches(matches);
    TypeNode range = selType[1];
    range = range.substitute(
        types.begin(), types.end(), matches.begin(), matches.end());
    Trace("typecheck-idt") << "Return (selector) " << range << " for " << n
                           << " from " << selType[1] << std::endl;
    return range;
  }
  else
  {
    if (check)
    {
      Trace("typecheck-idt") << "typecheck sel: " << n << std::endl;
      Trace("typecheck-idt") << "sel type: " << selType << std::endl;
      TypeNode childType = n[0].getType(check);
      if (selType[0] != childType)
      {
        Trace("typecheck-idt") << "ERROR: " << selType[0].getKind() << " "
                               << childType.getKind() << std::endl;
        throw TypeCheckingExceptionPrivate(n, "bad type for selector argument");
      }
    }
    return selType[1];
  }
}

TypeNode DatatypeTesterTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode DatatypeTesterTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  Assert(n.getKind() == kind::APPLY_TESTER);
  if (check)
  {
    if (n.getNumChildren() != 1)
    {
      throw TypeCheckingExceptionPrivate(
          n, "number of arguments does not match the tester type");
    }
    TypeNode testType = n.getOperator().getType(check);
    TypeNode childType = n[0].getType(check);
    TypeNode t = testType[0];
    Assert(t.isDatatype());
    if (t.isParametricDatatype())
    {
      Trace("typecheck-idt")
          << "typecheck parameterized tester: " << n << std::endl;
      TypeMatcher m(t);
      if (!m.doMatching(testType[0], childType))
      {
        throw TypeCheckingExceptionPrivate(
            n, "matching failed for tester argument of parameterized datatype");
      }
    }
    else
    {
      Trace("typecheck-idt") << "typecheck test: " << n << std::endl;
      Trace("typecheck-idt") << "test type: " << testType << std::endl;
      if (testType[0] != childType)
      {
        throw TypeCheckingExceptionPrivate(n, "bad type for tester argument");
      }
    }
  }
  return nodeManager->booleanType();
}

TypeNode DatatypeUpdateTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode DatatypeUpdateTypeRule::computeType(NodeManager* nodeManager,
                                             TNode n,
                                             bool check,
                                             std::ostream* errOut)
{
  Assert(n.getKind() == kind::APPLY_UPDATER);
  TypeNode updType = n.getOperator().getType(check);
  Assert(updType.getNumChildren() == 2);
  if (check)
  {
    TypeNode t = updType[0];
    for (size_t i = 0; i < 2; i++)
    {
      TypeNode childType = n[i].getType(check);
      TypeNode targ = updType[i];
      Trace("typecheck-idt") << "typecheck update: " << n << "[" << i
                             << "]: " << targ << " " << childType << std::endl;
      if (t.isParametricDatatype())
      {
        TypeMatcher m(t);
        if (!m.doMatching(targ, childType))
        {
          throw TypeCheckingExceptionPrivate(
              n,
              "matching failed for update argument of parameterized datatype");
        }
      }
      else if (targ != childType)
      {
        throw TypeCheckingExceptionPrivate(n, "bad type for update argument");
      }
    }
  }
  // type is the first argument
  return n[0].getType();
}

TypeNode DatatypeAscriptionTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return n.getOperator().getConst<AscriptionType>().getType();
}
TypeNode DatatypeAscriptionTypeRule::computeType(NodeManager* nodeManager,
                                                 TNode n,
                                                 bool check,
                                                 std::ostream* errOut)
{
  Trace("typecheck-idt") << "typechecking ascription: " << n << std::endl;
  Assert(n.getKind() == kind::APPLY_TYPE_ASCRIPTION);
  TypeNode t = n.getOperator().getConst<AscriptionType>().getType();
  if (check)
  {
    TypeNode childType = n[0].getType(check);

    TypeMatcher m;
    if (childType.getKind() == kind::CONSTRUCTOR_TYPE)
    {
      m.addTypesFromDatatype(childType.getDatatypeConstructorRangeType());
    }
    else if (childType.isDatatype())
    {
      m.addTypesFromDatatype(childType);
    }
    if (!m.doMatching(childType, t))
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "matching failed for type "
                                         "ascription argument of "
                                         "parameterized datatype");
    }
  }
  return t;
}

Cardinality ConstructorProperties::computeCardinality(TypeNode type)
{
  // Constructors aren't exactly functions, they're like
  // parameterized ground terms.  So the cardinality is more like
  // that of a tuple than that of a function.
  AssertArgument(type.isDatatypeConstructor(), type);
  Cardinality c = 1;
  for (unsigned i = 0, i_end = type.getNumChildren(); i < i_end - 1; ++i)
  {
    c *= type[i].getCardinality();
  }
  return c;
}

TypeNode DtSizeTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->integerType();
}
TypeNode DtSizeTypeRule::computeType(NodeManager* nodeManager,
                                     TNode n,
                                     bool check,
                                     std::ostream* errOut)
{
  if (check)
  {
    TypeNode t = n[0].getType(check);
    if (!t.isDatatype())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting datatype size term to have datatype argument.");
    }
  }
  return nodeManager->integerType();
}

TypeNode DtBoundTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return nm->booleanType();
}
TypeNode DtBoundTypeRule::computeType(NodeManager* nodeManager,
                                      TNode n,
                                      bool check,
                                      std::ostream* errOut)
{
  if (check)
  {
    TypeNode t = n[0].getType(check);
    if (!t.isDatatype())
    {
      throw TypeCheckingExceptionPrivate(
          n, "expecting datatype bound term to have datatype argument.");
    }
    if (!n[1].isConst() || !n[1].getType().isInteger())
    {
      throw TypeCheckingExceptionPrivate(
          n, "datatype bound must be a constant integer");
    }
    if (n[1].getConst<Rational>().getNumerator().sgn() == -1)
    {
      throw TypeCheckingExceptionPrivate(n,
                                         "datatype bound must be non-negative");
    }
  }
  return nodeManager->booleanType();
}

TypeNode DtSygusEvalTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode DtSygusEvalTypeRule::computeType(NodeManager* nodeManager,
                                          TNode n,
                                          bool check,
                                          std::ostream* errOut)
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
      if (vtype != atype)
      {
        throw TypeCheckingExceptionPrivate(
            n,
            "argument type mismatch in a datatype sygus evaluation function");
      }
    }
  }
  return dt.getSygusType();
}

TypeNode MatchTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode MatchTypeRule::computeType(NodeManager* nodeManager,
                                    TNode n,
                                    bool check,
                                    std::ostream* errOut)
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
    Kind nck = nc.getKind();
    std::unordered_set<Node> bvs;
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
    uint32_t pindex = nck == kind::MATCH_CASE ? 0 : 1;
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
      size_t ci = utils::indexOf(nc[pindex].getOperator());
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
    TypeNode currType = nc.getType(check);
    if (i == 1)
    {
      retType = currType;
    }
    else if (retType != currType)
    {
      std::stringstream ss;
      ss << "incomparable types in match case list" << std::endl;
      ss << nc[1] << ": " << currType << std::endl;
      ss << "expected: " << retType << std::endl;
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
  }
  // it is mandatory to check this here to ensure the match is exhaustive
  if (!patHasVariable && patIndices.size() < hdt.getNumConstructors())
  {
    throw TypeCheckingExceptionPrivate(
        n, "cases for match term are not exhaustive");
  }
  return retType;
}

TypeNode MatchCaseTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode MatchCaseTypeRule::computeType(NodeManager* nodeManager,
                                        TNode n,
                                        bool check,
                                        std::ostream* errOut)
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

TypeNode MatchBindCaseTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode MatchBindCaseTypeRule::computeType(NodeManager* nodeManager,
                                            TNode n,
                                            bool check,
                                            std::ostream* errOut)
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

TypeNode TupleProjectTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}
TypeNode TupleProjectTypeRule::computeType(NodeManager* nm,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getKind() == kind::TUPLE_PROJECT && n.hasOperator()
         && n.getOperator().getKind() == kind::TUPLE_PROJECT_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();
  if (check)
  {
    if (n.getNumChildren() != 1)
    {
      std::stringstream ss;
      ss << "operands in term " << n << " are " << n.getNumChildren()
         << ", but TUPLE_PROJECT expects 1 operand.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    TypeNode tupleType = n[0].getType(check);
    if (!tupleType.isTuple())
    {
      std::stringstream ss;
      ss << "TUPLE_PROJECT expects a tuple for " << n[0] << ". Found"
         << tupleType;
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
        ss << "Project index " << index << " in term " << n
           << " is >= " << numArgs << " which is the length of tuple " << n[0]
           << std::endl;
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
  }
  TypeNode tupleType = n[0].getType(check);
  return TupleUtils::getTupleProjectionType(indices, tupleType);
}

TypeNode CodatatypeBoundVariableTypeRule::preComputeType(NodeManager* nm,
                                                         TNode n)
{
  return TypeNode::null();
}
TypeNode CodatatypeBoundVariableTypeRule::computeType(NodeManager* nodeManager,
                                                      TNode n,
                                                      bool check,
                                                      std::ostream* errOut)
{
  return n.getConst<CodatatypeBoundVariable>().getType();
}

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
