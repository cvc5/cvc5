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
  TypeNode consType = n.getOperator().getTypeOrNull();
  if (consType.isDatatypeConstructor())
  {
    TypeNode t = consType.getDatatypeConstructorRangeType();
    // if not parametric, the return type can be obtained from constructor op
    if (!t.isParametricDatatype())
    {
      return t;
    }
  }
  return TypeNode::null();
}
TypeNode DatatypeConstructorTypeRule::computeType(NodeManager* nodeManager,
                                                  TNode n,
                                                  bool check,
                                                  std::ostream* errOut)
{
  Assert(n.getKind() == Kind::APPLY_CONSTRUCTOR);
  TypeNode consType = n.getOperator().getTypeOrNull();
  // note that datatype constructors cannot be abstracted
  if (!consType.isDatatypeConstructor())
  {
    if (errOut)
    {
      (*errOut) << "expected constructor to apply";
    }
    return TypeNode::null();
  }
  TypeNode t = consType.getDatatypeConstructorRangeType();
  Assert(t.isDatatype());
  TNode::iterator child_it = n.begin();
  TNode::iterator child_it_end = n.end();
  TypeNode::iterator tchild_it = consType.begin();
  if ((t.isParametricDatatype() || check)
      && n.getNumChildren() != consType.getNumChildren() - 1)
  {
    if (errOut)
    {
      (*errOut) << "number of arguments does not match the constructor type";
    }
    return TypeNode::null();
  }
  if (t.isParametricDatatype())
  {
    Trace("typecheck-idt") << "typecheck parameterized datatype " << n
                           << std::endl;
    TypeMatcher m(t);
    for (; child_it != child_it_end; ++child_it, ++tchild_it)
    {
      TypeNode childType = (*child_it).getTypeOrNull();
      if (!m.doMatching(*tchild_it, childType))
      {
        if (errOut)
        {
          (*errOut) << "matching failed for parameterized constructor";
        }
        return TypeNode::null();
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
        TypeNode childType = (*child_it).getTypeOrNull();
        Trace("typecheck-idt") << "typecheck cons arg: " << childType << " "
                               << (*tchild_it) << std::endl;
        TypeNode argumentType = *tchild_it;
        if (!childType.isComparableTo(argumentType))
        {
          if (errOut)
          {
            (*errOut) << "bad type for constructor argument:\n"
                      << "child type:  " << childType << "\n"
                      << "not type: " << argumentType << "\n"
                      << "in term : " << n;
          }
          return TypeNode::null();
        }
      }
    }
    return t;
  }
}

bool DatatypeConstructorTypeRule::computeIsConst(NodeManager* nodeManager,
                                                 TNode n)
{
  Assert(n.getKind() == Kind::APPLY_CONSTRUCTOR);
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
  Assert(n.getKind() == Kind::APPLY_SELECTOR);
  TypeNode selType = n.getOperator().getTypeOrNull();
  TypeNode t = selType[0];
  Assert(t.isDatatype());
  if ((t.isParametricDatatype() || check) && n.getNumChildren() != 1)
  {
    if (errOut)
    {
      (*errOut) << "number of arguments does not match the selector type";
    }
    return TypeNode::null();
  }
  if (t.isParametricDatatype())
  {
    Trace("typecheck-idt") << "typecheck parameterized sel: " << n << std::endl;
    TypeMatcher m(t);
    TypeNode childType = n[0].getTypeOrNull();
    if (!childType.isInstantiatedDatatype())
    {
      if (errOut)
      {
        (*errOut) << "Datatype type not fully instantiated";
      }
      return TypeNode::null();
    }
    // note that parametric datatype matching does not account for gradual
    // types.
    if (!m.doMatching(selType[0], childType))
    {
      if (errOut)
      {
        (*errOut) << "matching failed for selector argument of parameterized "
                     "datatype";
      }
      return TypeNode::null();
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
      TypeNode childType = n[0].getTypeOrNull();
      if (!selType[0].isComparableTo(childType))
      {
        Trace("typecheck-idt") << "ERROR: " << selType[0].getKind() << " "
                               << childType.getKind() << std::endl;
        if (errOut)
        {
          (*errOut) << "bad type for selector argument";
        }
        return TypeNode::null();
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
  Assert(n.getKind() == Kind::APPLY_TESTER);
  if (check)
  {
    if (n.getNumChildren() != 1)
    {
      if (errOut)
      {
        (*errOut) << "number of arguments does not match the tester type";
      }
      return TypeNode::null();
    }
    TypeNode testType = n.getOperator().getTypeOrNull();
    TypeNode childType = n[0].getTypeOrNull();
    TypeNode t = testType[0];
    Assert(t.isDatatype());
    if (t.isParametricDatatype())
    {
      Trace("typecheck-idt")
          << "typecheck parameterized tester: " << n << std::endl;
      TypeMatcher m(t);
      if (!m.doMatching(testType[0], childType))
      {
        if (errOut)
        {
          (*errOut) << "matching failed for tester argument of parameterized "
                       "datatype";
        }
        return TypeNode::null();
      }
    }
    else
    {
      Trace("typecheck-idt") << "typecheck test: " << n << std::endl;
      Trace("typecheck-idt") << "test type: " << testType << std::endl;
      if (testType[0] != childType)
      {
        if (errOut)
        {
          (*errOut) << "bad type for tester argument";
        }
        return TypeNode::null();
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
  Assert(n.getKind() == Kind::APPLY_UPDATER);
  TypeNode updType = n.getOperator().getTypeOrNull();
  Assert(updType.getNumChildren() == 2);
  if (check)
  {
    TypeNode t = updType[0];
    for (size_t i = 0; i < 2; i++)
    {
      TypeNode childType = n[i].getTypeOrNull();
      TypeNode targ = updType[i];
      Trace("typecheck-idt") << "typecheck update: " << n << "[" << i
                             << "]: " << targ << " " << childType << std::endl;
      if (t.isParametricDatatype())
      {
        TypeMatcher m(t);
        if (!m.doMatching(targ, childType))
        {
          if (errOut)
          {
            (*errOut) << "matching failed for update argument of parameterized "
                         "datatype";
          }
          return TypeNode::null();
        }
      }
      else if (targ != childType)
      {
        if (errOut)
        {
          (*errOut) << "bad type for update argument";
        }
        return TypeNode::null();
      }
    }
  }
  // type is the first argument
  return n[0].getTypeOrNull();
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
  Assert(n.getKind() == Kind::APPLY_TYPE_ASCRIPTION);
  TypeNode t = n.getOperator().getConst<AscriptionType>().getType();
  if (check)
  {
    TypeNode childType = n[0].getTypeOrNull();

    TypeMatcher m;
    if (childType.getKind() == Kind::CONSTRUCTOR_TYPE)
    {
      m.addTypesFromDatatype(childType.getDatatypeConstructorRangeType());
    }
    else if (childType.isDatatype())
    {
      m.addTypesFromDatatype(childType);
    }
    if (!m.doMatching(childType, t))
    {
      if (errOut)
      {
        (*errOut) << "matching failed for type ascription argument of "
                     "parameterized datatype";
      }
      return TypeNode::null();
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
    TypeNode t = n[0].getTypeOrNull();
    if (!t.isDatatype())
    {
      if (errOut)
      {
        (*errOut) << "expecting datatype size term to have datatype argument.";
      }
      return TypeNode::null();
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
    TypeNode t = n[0].getTypeOrNull();
    if (!t.isDatatype())
    {
      if (errOut)
      {
        (*errOut) << "expecting datatype bound term to have datatype argument.";
      }
      return TypeNode::null();
    }
    if (!n[1].isConst() || !n[1].getTypeOrNull().isInteger())
    {
      if (errOut)
      {
        (*errOut) << "datatype bound must be a constant integer";
      }
      return TypeNode::null();
    }
    if (n[1].getConst<Rational>().getNumerator().sgn() == -1)
    {
      if (errOut)
      {
        (*errOut) << "datatype bound must be non-negative";
      }
      return TypeNode::null();
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
  TypeNode headType = n[0].getTypeOrNull();
  if (!headType.isDatatype())
  {
    if (errOut)
    {
      (*errOut) << "datatype sygus eval takes a datatype head";
    }
    return TypeNode::null();
  }
  const DType& dt = headType.getDType();
  if (!dt.isSygus())
  {
    if (errOut)
    {
      (*errOut)
          << "datatype sygus eval must have a datatype head that is sygus";
    }
    return TypeNode::null();
  }
  if (check)
  {
    Node svl = dt.getSygusVarList();
    if (svl.getNumChildren() + 1 != n.getNumChildren())
    {
      if (errOut)
      {
        (*errOut) << "wrong number of arguments to a datatype sygus evaluation "
                     "function";
      }
      return TypeNode::null();
    }
    for (unsigned i = 0, nvars = svl.getNumChildren(); i < nvars; i++)
    {
      TypeNode vtype = svl[i].getTypeOrNull();
      TypeNode atype = n[i + 1].getTypeOrNull();
      if (vtype != atype)
      {
        if (errOut)
        {
          (*errOut) << "argument type mismatch in a datatype sygus evaluation "
                       "function";
        }
        return TypeNode::null();
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
  Assert(n.getKind() == Kind::MATCH);

  TypeNode retType;

  TypeNode headType = n[0].getTypeOrNull();
  if (!headType.isDatatype())
  {
    if (errOut)
    {
      (*errOut) << "expecting datatype head in match";
    }
    return TypeNode::null();
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
    if (nck == Kind::MATCH_BIND_CASE)
    {
      for (const Node& v : nc[0])
      {
        Assert(v.getKind() == Kind::BOUND_VARIABLE);
        bvs.insert(v);
      }
    }
    else if (nck != Kind::MATCH_CASE)
    {
      if (errOut)
      {
        (*errOut) << "expected a match case in match expression";
      }
      return TypeNode::null();
    }
    // get the pattern type
    uint32_t pindex = nck == Kind::MATCH_CASE ? 0 : 1;
    TypeNode patType = nc[pindex].getTypeOrNull();
    // should be caught in the above call
    if (!patType.isDatatype())
    {
      if (errOut)
      {
        (*errOut) << "expecting datatype pattern in match";
      }
      return TypeNode::null();
    }
    Kind ncpk = nc[pindex].getKind();
    if (ncpk == Kind::APPLY_CONSTRUCTOR)
    {
      for (const Node& arg : nc[pindex])
      {
        if (bvs.find(arg) == bvs.end())
        {
          if (errOut)
          {
            (*errOut) << "expecting distinct bound variable as argument to "
                         "constructor in pattern of match";
          }
          return TypeNode::null();
        }
        bvs.erase(arg);
      }
      size_t ci = utils::indexOf(nc[pindex].getOperator());
      patIndices.insert(ci);
    }
    else if (ncpk == Kind::BOUND_VARIABLE)
    {
      patHasVariable = true;
    }
    else
    {
      if (errOut)
      {
        (*errOut) << "unexpected kind of term in pattern in match";
      }
      return TypeNode::null();
    }
    const DType& pdt = patType.getDType();
    // compare datatypes instead of the types to catch parametric case,
    // where the pattern has parametric type.
    if (hdt.getTypeNode() != pdt.getTypeNode())
    {
      if (errOut)
      {
        (*errOut)
            << "pattern of a match case does not match the head type in match";
      }
      return TypeNode::null();
    }
    TypeNode currType = nc.getTypeOrNull();
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
    if (errOut)
    {
      (*errOut) << "cases for match term are not exhaustive";
    }
    return TypeNode::null();
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
  Assert(n.getKind() == Kind::MATCH_CASE);
  if (check)
  {
    TypeNode patType = n[0].getTypeOrNull();
    if (!patType.isDatatype())
    {
      if (errOut)
      {
        (*errOut) << "expecting datatype pattern in match case";
      }
      return TypeNode::null();
    }
  }
  return n[1].getTypeOrNull();
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
  Assert(n.getKind() == Kind::MATCH_BIND_CASE);
  if (check)
  {
    if (n[0].getKind() != Kind::BOUND_VAR_LIST)
    {
      if (errOut)
      {
        (*errOut) << "expected a bound variable list in match bind case";
      }
      return TypeNode::null();
    }
    TypeNode patType = n[1].getTypeOrNull();
    if (!patType.isDatatype())
    {
      if (errOut)
      {
        (*errOut) << "expecting datatype pattern in match bind case";
      }
      return TypeNode::null();
    }
  }
  return n[2].getTypeOrNull();
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
  Assert(n.getKind() == Kind::TUPLE_PROJECT && n.hasOperator()
         && n.getOperator().getKind() == Kind::TUPLE_PROJECT_OP);
  ProjectOp op = n.getOperator().getConst<ProjectOp>();
  const std::vector<uint32_t>& indices = op.getIndices();
  if (check)
  {
    if (n.getNumChildren() != 1)
    {
      if (errOut)
      {
        (*errOut) << "operands in term " << n << " are " << n.getNumChildren()
                  << ", but TUPLE_PROJECT expects 1 operand.";
      }
      return TypeNode::null();
    }
    TypeNode tupleType = n[0].getTypeOrNull();
    if (!tupleType.isMaybeKind(Kind::TUPLE_TYPE))
    {
      if (errOut)
      {
        (*errOut) << "TUPLE_PROJECT expects a tuple for " << n[0] << ". Found"
                  << tupleType;
      }
      return TypeNode::null();
    }

    // check indicies if we are a concrete tuple
    if (tupleType.isTuple())
    {
      // make sure all indices are less than the length of the tuple type
      const DType& dType = tupleType.getDType();
      DTypeConstructor constructor = dType[0];
      size_t numArgs = constructor.getNumArgs();
      for (uint32_t index : indices)
      {
        if (index >= numArgs)
        {
          if (errOut)
          {
            (*errOut) << "Project index " << index << " in term " << n
                      << " is >= " << numArgs
                      << " which is the length of tuple " << n[0] << std::endl;
          }
          return TypeNode::null();
        }
      }
    }
  }
  TypeNode tupleType = n[0].getTypeOrNull();
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

TypeNode NullableLiftTypeRule::preComputeType(NodeManager* nm, TNode n)
{
  return TypeNode::null();
}

TypeNode NullableLiftTypeRule::computeType(NodeManager* nodeManager,
                                           TNode n,
                                           bool check,
                                           std::ostream* errOut)
{
  Assert(n.getKind() == Kind::NULLABLE_LIFT);
  if (check)
  {
    std::vector<TypeNode> argTypes;
    TypeNode functionType = n[0].getType(check);
    if (!functionType.isFunction())
    {
      std::stringstream ss;
      ss << "Argument 0 '" << n[0] << "' in term " << n << " has type '"
         << functionType << "' which is not a function type.";
      throw TypeCheckingExceptionPrivate(n, ss.str());
    }
    std::vector<TypeNode> funArgTypes = functionType.getArgTypes();
    for (size_t i = 1; i < n.getNumChildren(); i++)
    {
      TypeNode argType = n[i].getType(check);
      if (!argType.isNullable())
      {
        std::stringstream ss;
        ss << "Argument " << i << " '" << n[i] << "' in term " << n
           << " has type '" << argType << "' which is not a nullable type.";
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
      TypeNode elementType = argType[0];
      if (funArgTypes[i - 1] != elementType)
      {
        std::stringstream ss;
        ss << "Argument " << (i - 1) << " in function '" << n[0] << " has type "
           << funArgTypes[i - 1] << ". Expected '" << n[i] << "' to have type "
           << nodeManager->mkNullableType(funArgTypes[i - 1]) << " instead of "
           << argType;
        throw TypeCheckingExceptionPrivate(n, ss.str());
      }
    }
  }
  return nodeManager->mkNullableType(n[0].getType().getRangeType());
}

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
