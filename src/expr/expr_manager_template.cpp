/*********************                                                        */
/*! \file expr_manager_template.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Public-facing expression manager interface, implementation
 **
 ** Public-facing expression manager interface, implementation.
 **/

#include "expr/expr_manager.h"

#include <map>

#include "expr/node_manager.h"
#include "expr/variable_type_map.h"
#include "expr/node_manager_attributes.h"
#include "options/options.h"
#include "util/statistics_registry.h"

${includes}

#ifdef CVC4_STATISTICS_ON
  #define INC_STAT(kind) \
  { \
    if (d_exprStatistics[kind] == NULL) { \
      stringstream statName; \
      statName << "expr::ExprManager::" << kind; \
      d_exprStatistics[kind] = new IntStat(statName.str(), 0); \
      d_nodeManager->getStatisticsRegistry()->registerStat(d_exprStatistics[kind]); \
    } \
    ++ *(d_exprStatistics[kind]); \
  }
#define INC_STAT_VAR(type, bound_var)                                      \
  {                                                                        \
    TypeNode* isv_typeNode = Type::getTypeNode(type);                      \
    TypeConstant isv_type = isv_typeNode->getKind() == kind::TYPE_CONSTANT \
                                ? isv_typeNode->getConst<TypeConstant>()   \
                                : LAST_TYPE;                               \
    if (d_exprStatisticsVars[isv_type] == NULL)                            \
    {                                                                      \
      stringstream statName;                                               \
      if (isv_type == LAST_TYPE)                                           \
      {                                                                    \
        statName << "expr::ExprManager::"                                  \
                 << ((bound_var) ? "BOUND_VARIABLE" : "VARIABLE")          \
                 << ":Parameterized isv_type";                             \
      }                                                                    \
      else                                                                 \
      {                                                                    \
        statName << "expr::ExprManager::"                                  \
                 << ((bound_var) ? "BOUND_VARIABLE" : "VARIABLE") << ":"   \
                 << isv_type;                                              \
      }                                                                    \
      d_exprStatisticsVars[isv_type] = new IntStat(statName.str(), 0);     \
      d_nodeManager->getStatisticsRegistry()->registerStat(                \
          d_exprStatisticsVars[isv_type]);                                 \
    }                                                                      \
    ++*(d_exprStatisticsVars[isv_type]);                                   \
  }
#else
  #define INC_STAT(kind)
  #define INC_STAT_VAR(type, bound_var)
#endif

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {

ExprManager::ExprManager() :
  d_nodeManager(new NodeManager(this)) {
#ifdef CVC4_STATISTICS_ON
  for (unsigned i = 0; i < kind::LAST_KIND; ++ i) {
    d_exprStatistics[i] = NULL;
  }
  for (unsigned i = 0; i <= LAST_TYPE; ++ i) {
    d_exprStatisticsVars[i] = NULL;
  }
#endif
}

ExprManager::~ExprManager()
{
  NodeManagerScope nms(d_nodeManager);

  try {

#ifdef CVC4_STATISTICS_ON
    for (unsigned i = 0; i < kind::LAST_KIND; ++ i) {
      if (d_exprStatistics[i] != NULL) {
        d_nodeManager->getStatisticsRegistry()->unregisterStat(d_exprStatistics[i]);
        delete d_exprStatistics[i];
        d_exprStatistics[i] = NULL;
      }
    }
    for (unsigned i = 0; i <= LAST_TYPE; ++ i) {
      if (d_exprStatisticsVars[i] != NULL) {
        d_nodeManager->getStatisticsRegistry()->unregisterStat(d_exprStatisticsVars[i]);
        delete d_exprStatisticsVars[i];
        d_exprStatisticsVars[i] = NULL;
      }
    }
#endif

    delete d_nodeManager;
    d_nodeManager = NULL;
  } catch(Exception& e) {
    Warning() << "CVC4 threw an exception during cleanup." << std::endl
              << e << std::endl;
  }
}

BooleanType ExprManager::booleanType() const {
  NodeManagerScope nms(d_nodeManager);
  return BooleanType(Type(d_nodeManager, new TypeNode(d_nodeManager->booleanType())));
}

StringType ExprManager::stringType() const {
  NodeManagerScope nms(d_nodeManager);
  return StringType(Type(d_nodeManager, new TypeNode(d_nodeManager->stringType())));
}

RegExpType ExprManager::regExpType() const {
  NodeManagerScope nms(d_nodeManager);
  return RegExpType(Type(d_nodeManager, new TypeNode(d_nodeManager->regExpType())));
}

RealType ExprManager::realType() const {
  NodeManagerScope nms(d_nodeManager);
  return RealType(Type(d_nodeManager, new TypeNode(d_nodeManager->realType())));
}

IntegerType ExprManager::integerType() const {
  NodeManagerScope nms(d_nodeManager);
  return IntegerType(Type(d_nodeManager, new TypeNode(d_nodeManager->integerType())));
}

RoundingModeType ExprManager::roundingModeType() const {
  NodeManagerScope nms(d_nodeManager);
  return RoundingModeType(Type(d_nodeManager, new TypeNode(d_nodeManager->roundingModeType())));
}


Expr ExprManager::mkExpr(Kind kind, Expr child1) {
  const kind::MetaKind mk = kind::metaKindOf(kind);
  const unsigned n = 1 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  PrettyCheckArgument(
      mk == kind::metakind::PARAMETERIZED ||
      mk == kind::metakind::OPERATOR, kind,
      "Only operator-style expressions are made with mkExpr(); "
      "to make variables and constants, see mkVar(), mkBoundVar(), "
      "and mkConst().");
  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind, child1.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2) {
  const kind::MetaKind mk = kind::metaKindOf(kind);
  const unsigned n = 2 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  PrettyCheckArgument(
      mk == kind::metakind::PARAMETERIZED ||
      mk == kind::metakind::OPERATOR, kind,
      "Only operator-style expressions are made with mkExpr(); "
      "to make variables and constants, see mkVar(), mkBoundVar(), "
      "and mkConst().");
  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2, Expr child3) {
  const kind::MetaKind mk = kind::metaKindOf(kind);
  const unsigned n = 3 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  PrettyCheckArgument(
      mk == kind::metakind::PARAMETERIZED ||
      mk == kind::metakind::OPERATOR, kind,
      "Only operator-style expressions are made with mkExpr(); "
      "to make variables and constants, see mkVar(), mkBoundVar(), "
      "and mkConst().");
  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2, Expr child3,
                         Expr child4) {
  const kind::MetaKind mk = kind::metaKindOf(kind);
  const unsigned n = 4 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  PrettyCheckArgument(
      mk == kind::metakind::PARAMETERIZED ||
      mk == kind::metakind::OPERATOR, kind,
      "Only operator-style expressions are made with mkExpr(); "
      "to make variables and constants, see mkVar(), mkBoundVar(), "
      "and mkConst().");
  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode(),
                                               child4.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2, Expr child3,
                         Expr child4, Expr child5) {
  const kind::MetaKind mk = kind::metaKindOf(kind);
  const unsigned n = 5 - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  PrettyCheckArgument(
      mk == kind::metakind::PARAMETERIZED ||
      mk == kind::metakind::OPERATOR, kind,
      "Only operator-style expressions are made with mkExpr(); "
      "to make variables and constants, see mkVar(), mkBoundVar(), "
      "and mkConst().");
  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind,
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode(),
                                               child4.getNode(),
                                               child5.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, const std::vector<Expr>& children)
{
  const size_t nchildren = children.size();
  const kind::MetaKind mk = kind::metaKindOf(kind);
  PrettyCheckArgument(
      mk == kind::metakind::PARAMETERIZED || mk == kind::metakind::OPERATOR,
      kind,
      "Only operator-style expressions are made with mkExpr(); "
      "to make variables and constants, see mkVar(), mkBoundVar(), "
      "and mkConst().");
  PrettyCheckArgument(
      mk != kind::metakind::PARAMETERIZED || nchildren > 0,
      kind,
      "Terms with kind %s must have an operator expression as first argument",
      kind::kindToString(kind).c_str());
  const size_t n = nchildren - (mk == kind::metakind::PARAMETERIZED ? 1 : 0);
  PrettyCheckArgument(n >= minArity(kind) && n <= maxArity(kind),
                      kind,
                      "Exprs with kind %s must have at least %u children and "
                      "at most %u children (the one under construction has %u)",
                      kind::kindToString(kind).c_str(),
                      minArity(kind),
                      maxArity(kind),
                      n);

  NodeManagerScope nms(d_nodeManager);

  vector<Node> nodes;
  vector<Expr>::const_iterator it = children.begin();
  vector<Expr>::const_iterator it_end = children.end();
  while(it != it_end) {
    nodes.push_back(it->getNode());
    ++it;
  }
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind, nodes));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Kind kind, Expr child1,
                         const std::vector<Expr>& otherChildren) {
  const kind::MetaKind mk = kind::metaKindOf(kind);
  const unsigned n =
      otherChildren.size() - (mk == kind::metakind::PARAMETERIZED ? 1 : 0) + 1;
  PrettyCheckArgument(
      mk == kind::metakind::PARAMETERIZED ||
      mk == kind::metakind::OPERATOR, kind,
      "Only operator-style expressions are made with mkExpr(); "
      "to make variables and constants, see mkVar(), mkBoundVar(), "
      "and mkConst().");
  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);

  NodeManagerScope nms(d_nodeManager);

  vector<Node> nodes;
  nodes.push_back(child1.getNode());

  vector<Expr>::const_iterator it = otherChildren.begin();
  vector<Expr>::const_iterator it_end = otherChildren.end();
  while(it != it_end) {
    nodes.push_back(it->getNode());
    ++it;
  }
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(kind, nodes));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr) {
  const Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  PrettyCheckArgument(
      opExpr.getKind() == kind::BUILTIN ||
      kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED, opExpr,
      "This Expr constructor is for parameterized kinds only");
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, Expr child1) {
  const unsigned n = 1;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  PrettyCheckArgument(
      (opExpr.getKind() == kind::BUILTIN ||
       kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED), opExpr,
      "This Expr constructor is for parameterized kinds only");
  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode(), child1.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, Expr child1, Expr child2) {
  const unsigned n = 2;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  PrettyCheckArgument(
      (opExpr.getKind() == kind::BUILTIN ||
       kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED), opExpr,
      "This Expr constructor is for parameterized kinds only");
  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode(),
                                               child1.getNode(),
                                               child2.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3) {
  const unsigned n = 3;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  PrettyCheckArgument(
      (opExpr.getKind() == kind::BUILTIN ||
       kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED), opExpr,
                "This Expr constructor is for parameterized kinds only");
  PrettyCheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode(),
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3,
                         Expr child4) {
  const unsigned n = 4;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  PrettyCheckArgument(
      (opExpr.getKind() == kind::BUILTIN ||
       kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED), opExpr,
      "This Expr constructor is for parameterized kinds only");

  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);

  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode(),
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode(),
                                               child4.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3,
                         Expr child4, Expr child5) {
  const unsigned n = 5;
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  PrettyCheckArgument(
      (opExpr.getKind() == kind::BUILTIN ||
       kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED), opExpr,
      "This Expr constructor is for parameterized kinds only");
  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    INC_STAT(kind);
    return Expr(this, d_nodeManager->mkNodePtr(opExpr.getNode(),
                                               child1.getNode(),
                                               child2.getNode(),
                                               child3.getNode(),
                                               child4.getNode(),
                                               child5.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

Expr ExprManager::mkExpr(Expr opExpr, const std::vector<Expr>& children) {
  const unsigned n = children.size();
  Kind kind = NodeManager::operatorToKind(opExpr.getNode());
  PrettyCheckArgument(
      (opExpr.getKind() == kind::BUILTIN ||
       kind::metaKindOf(kind) == kind::metakind::PARAMETERIZED), opExpr,
      "This Expr constructor is for parameterized kinds only");
  PrettyCheckArgument(
      n >= minArity(kind) && n <= maxArity(kind), kind,
      "Exprs with kind %s must have at least %u children and "
      "at most %u children (the one under construction has %u)",
      kind::kindToString(kind).c_str(),
      minArity(kind), maxArity(kind), n);

  NodeManagerScope nms(d_nodeManager);

  vector<Node> nodes;
  vector<Expr>::const_iterator it = children.begin();
  vector<Expr>::const_iterator it_end = children.end();
  while(it != it_end) {
    nodes.push_back(it->getNode());
    ++it;
  }
  try {
    INC_STAT(kind);
    return Expr(this,d_nodeManager->mkNodePtr(opExpr.getNode(), nodes));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
}

bool ExprManager::hasOperator(Kind k) {
  return NodeManager::hasOperator(k);
}

Expr ExprManager::operatorOf(Kind k) {
  NodeManagerScope nms(d_nodeManager);

  return d_nodeManager->operatorOf(k).toExpr();
}

Kind ExprManager::operatorToKind(Expr e) {
  NodeManagerScope nms(d_nodeManager);

  return d_nodeManager->operatorToKind( e.getNode() );
}

/** Make a function type from domain to range. */
FunctionType ExprManager::mkFunctionType(Type domain, Type range) {
  NodeManagerScope nms(d_nodeManager);
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(*domain.d_typeNode, *range.d_typeNode))));
}

/** Make a function type with input types from argTypes. */
FunctionType ExprManager::mkFunctionType(const std::vector<Type>& argTypes, Type range) {
  NodeManagerScope nms(d_nodeManager);
  Assert(argTypes.size() >= 1);
  std::vector<TypeNode> argTypeNodes;
  for (unsigned i = 0, i_end = argTypes.size(); i < i_end; ++ i) {
    argTypeNodes.push_back(*argTypes[i].d_typeNode);
  }
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(argTypeNodes, *range.d_typeNode))));
}

FunctionType ExprManager::mkFunctionType(const std::vector<Type>& sorts) {
  NodeManagerScope nms(d_nodeManager);
  Assert(sorts.size() >= 2);
  std::vector<TypeNode> sortNodes;
  for (unsigned i = 0, i_end = sorts.size(); i < i_end; ++ i) {
     sortNodes.push_back(*sorts[i].d_typeNode);
  }
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(sortNodes))));
}

FunctionType ExprManager::mkPredicateType(const std::vector<Type>& sorts) {
  NodeManagerScope nms(d_nodeManager);
  Assert(sorts.size() >= 1);
  std::vector<TypeNode> sortNodes;
  for (unsigned i = 0, i_end = sorts.size(); i < i_end; ++ i) {
     sortNodes.push_back(*sorts[i].d_typeNode);
  }
  return FunctionType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkPredicateType(sortNodes))));
}

SExprType ExprManager::mkSExprType(const std::vector<Type>& types) {
  NodeManagerScope nms(d_nodeManager);
  std::vector<TypeNode> typeNodes;
  for (unsigned i = 0, i_end = types.size(); i < i_end; ++ i) {
     typeNodes.push_back(*types[i].d_typeNode);
  }
  return SExprType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkSExprType(typeNodes))));
}

FloatingPointType ExprManager::mkFloatingPointType(unsigned exp, unsigned sig) const {
  NodeManagerScope nms(d_nodeManager);
  return FloatingPointType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkFloatingPointType(exp,sig))));
}

BitVectorType ExprManager::mkBitVectorType(unsigned size) const {
  NodeManagerScope nms(d_nodeManager);
  return BitVectorType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkBitVectorType(size))));
}

ArrayType ExprManager::mkArrayType(Type indexType, Type constituentType) const {
  NodeManagerScope nms(d_nodeManager);
  return ArrayType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkArrayType(*indexType.d_typeNode, *constituentType.d_typeNode))));
}

SetType ExprManager::mkSetType(Type elementType) const {
  NodeManagerScope nms(d_nodeManager);
  return SetType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkSetType(*elementType.d_typeNode))));
}

SequenceType ExprManager::mkSequenceType(Type elementType) const
{
  NodeManagerScope nms(d_nodeManager);
  return SequenceType(Type(
      d_nodeManager,
      new TypeNode(d_nodeManager->mkSequenceType(*elementType.d_typeNode))));
}

SortType ExprManager::mkSort(const std::string& name, uint32_t flags) const {
  NodeManagerScope nms(d_nodeManager);
  return SortType(Type(d_nodeManager, new TypeNode(d_nodeManager->mkSort(name, flags))));
}

SortConstructorType ExprManager::mkSortConstructor(const std::string& name,
                                                   size_t arity,
                                                   uint32_t flags) const
{
  NodeManagerScope nms(d_nodeManager);
  return SortConstructorType(
      Type(d_nodeManager,
           new TypeNode(d_nodeManager->mkSortConstructor(name, arity, flags))));
}

/**
 * Get the type for the given Expr and optionally do type checking.
 *
 * Initial type computation will be near-constant time if
 * type checking is not requested. Results are memoized, so that
 * subsequent calls to getType() without type checking will be
 * constant time.
 *
 * Initial type checking is linear in the size of the expression.
 * Again, the results are memoized, so that subsequent calls to
 * getType(), with or without type checking, will be constant
 * time.
 *
 * NOTE: A TypeCheckingException can be thrown even when type
 * checking is not requested. getType() will always return a
 * valid and correct type and, thus, an exception will be thrown
 * when no valid or correct type can be computed (e.g., if the
 * arguments to a bit-vector operation aren't bit-vectors). When
 * type checking is not requested, getType() will do the minimum
 * amount of checking required to return a valid result.
 *
 * @param e the Expr for which we want a type
 * @param check whether we should check the type as we compute it
 * (default: false)
 */
Type ExprManager::getType(Expr expr, bool check)
{
  NodeManagerScope nms(d_nodeManager);
  Type t;
  try {
    t = Type(d_nodeManager,
             new TypeNode(d_nodeManager->getType(expr.getNode(), check)));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(this, &e);
  }
  return t;
}

Expr ExprManager::mkVar(const std::string& name, Type type, uint32_t flags) {
  NodeManagerScope nms(d_nodeManager);
  Node* n = d_nodeManager->mkVarPtr(name, *type.d_typeNode, flags);
  Debug("nm") << "set " << name << " on " << *n << std::endl;
  INC_STAT_VAR(type, false);
  return Expr(this, n);
}

Expr ExprManager::mkVar(Type type, uint32_t flags) {
  NodeManagerScope nms(d_nodeManager);
  INC_STAT_VAR(type, false);
  return Expr(this, d_nodeManager->mkVarPtr(*type.d_typeNode, flags));
}

Expr ExprManager::mkBoundVar(const std::string& name, Type type) {
  NodeManagerScope nms(d_nodeManager);
  Node* n = d_nodeManager->mkBoundVarPtr(name, *type.d_typeNode);
  Debug("nm") << "set " << name << " on " << *n << std::endl;
  INC_STAT_VAR(type, true);
  return Expr(this, n);
}

Expr ExprManager::mkBoundVar(Type type) {
  NodeManagerScope nms(d_nodeManager);
  INC_STAT_VAR(type, true);
  return Expr(this, d_nodeManager->mkBoundVarPtr(*type.d_typeNode));
}

Expr ExprManager::mkNullaryOperator(Type type, Kind k){
  NodeManagerScope nms(d_nodeManager);
  Node n = d_nodeManager->mkNullaryOperator(*type.d_typeNode, k); 
  return n.toExpr();
}

Expr ExprManager::mkAssociative(Kind kind,
                                const std::vector<Expr>& children) {
  PrettyCheckArgument(
      kind::isAssociative(kind), kind,
      "Illegal kind in mkAssociative: %s",
      kind::kindToString(kind).c_str());

  const unsigned int max = maxArity(kind);
  unsigned int numChildren = children.size();

  /* If the number of children is within bounds, then there's nothing to do. */
  if( numChildren <= max ) {
    return mkExpr(kind,children);
  }
  NodeManagerScope nms(d_nodeManager);
  const unsigned int min = minArity(kind);

  std::vector<Expr>::const_iterator it = children.begin() ;
  std::vector<Expr>::const_iterator end = children.end() ;

  /* The new top-level children and the children of each sub node */
  std::vector<Expr> newChildren;
  std::vector<Node> subChildren;

  while( it != end && numChildren > max ) {
    /* Grab the next max children and make a node for them. */
    for( std::vector<Expr>::const_iterator next = it + max;
         it != next;
         ++it, --numChildren ) {
      subChildren.push_back(it->getNode());
    }
    Node subNode = d_nodeManager->mkNode(kind,subChildren);
    newChildren.push_back(subNode.toExpr());

    subChildren.clear();
  }

  // add the leftover children
  if(numChildren > 0) {
    for (; it != end; ++it)
    {
      newChildren.push_back(*it);
    }
  }

  /* It would be really weird if this happened (it would require
   * min > 2, for one thing), but let's make sure. */
  AlwaysAssert(newChildren.size() >= min)
      << "Too few new children in mkAssociative";

  // recurse
  return mkAssociative(kind, newChildren);
}

Expr ExprManager::mkLeftAssociative(Kind kind,
                                    const std::vector<Expr>& children)
{
  NodeManagerScope nms(d_nodeManager);
  Node n = children[0];
  for (unsigned i = 1, size = children.size(); i < size; i++)
  {
    n = d_nodeManager->mkNode(kind, n, children[i].getNode());
  }
  return n.toExpr();
}

Expr ExprManager::mkRightAssociative(Kind kind,
                                     const std::vector<Expr>& children)
{
  NodeManagerScope nms(d_nodeManager);
  Node n = children[children.size() - 1];
  for (unsigned i = children.size() - 1; i > 0;)
  {
    n = d_nodeManager->mkNode(kind, children[--i].getNode(), n);
  }
  return n.toExpr();
}

Expr ExprManager::mkChain(Kind kind, const std::vector<Expr>& children)
{
  if (children.size() == 2)
  {
    // if this is the case exactly 1 pair will be generated so the
    // AND is not required
    return mkExpr(kind, children[0], children[1]);
  }
  std::vector<Expr> cchildren;
  for (size_t i = 0, nargsmo = children.size() - 1; i < nargsmo; i++)
  {
    cchildren.push_back(mkExpr(kind, children[i], children[i + 1]));
  }
  return mkExpr(kind::AND, cchildren);
}

unsigned ExprManager::minArity(Kind kind) {
  return metakind::getLowerBoundForKind(kind);
}

unsigned ExprManager::maxArity(Kind kind) {
  return metakind::getUpperBoundForKind(kind);
}

bool ExprManager::isNAryKind(Kind fun)
{
  return ExprManager::maxArity(fun) == expr::NodeValue::MAX_CHILDREN;
}

NodeManager* ExprManager::getNodeManager() const {
  return d_nodeManager;
}
Statistics ExprManager::getStatistics() const
{
  return Statistics(*d_nodeManager->getStatisticsRegistry());
}

SExpr ExprManager::getStatistic(const std::string& name) const
{
  return d_nodeManager->getStatisticsRegistry()->getStatistic(name);
}

void ExprManager::safeFlushStatistics(int fd) const {
  d_nodeManager->getStatisticsRegistry()->safeFlushInformation(fd);
}

namespace expr {

Node exportInternal(TNode n, ExprManager* from, ExprManager* to, ExprManagerMapCollection& vmap);

TypeNode exportTypeInternal(TypeNode n, NodeManager* from, NodeManager* to, ExprManagerMapCollection& vmap) {
  Debug("export") << "type: " << n << " " << n.getId() << std::endl;
  if(theory::kindToTheoryId(n.getKind()) == theory::THEORY_DATATYPES) {
    throw ExportUnsupportedException
      ("export of types belonging to theory of DATATYPES kinds unsupported");
  }
  if(n.getMetaKind() == kind::metakind::PARAMETERIZED &&
     n.getKind() != kind::SORT_TYPE) {
    throw ExportUnsupportedException
      ("export of PARAMETERIZED-kinded types (other than SORT_KIND) not supported");
  }
  if(n.getKind() == kind::TYPE_CONSTANT) {
    return to->mkTypeConst(n.getConst<TypeConstant>());
  } else if(n.getKind() == kind::BITVECTOR_TYPE) {
    return to->mkBitVectorType(n.getConst<BitVectorSize>());
  }
  else if (n.getKind() == kind::FLOATINGPOINT_TYPE)
  {
    return to->mkFloatingPointType(n.getConst<FloatingPointSize>());
  }
  else if (n.getNumChildren() == 0)
  {
    std::stringstream msg;
    msg << "export of type " << n << " not supported";
    throw ExportUnsupportedException(msg.str().c_str());
  }
  Type from_t = from->toType(n);
  Type& to_t = vmap.d_typeMap[from_t];
  if(! to_t.isNull()) {
    Debug("export") << "+ mapped `" << from_t << "' to `" << to_t << "'" << std::endl;
    return *Type::getTypeNode(to_t);
  }
  NodeBuilder<> children(to, n.getKind());
  if(n.getKind() == kind::SORT_TYPE) {
    Debug("export") << "type: operator: " << n.getOperator() << std::endl;
    // make a new sort tag in target node manager
    Node sortTag = NodeBuilder<0>(to, kind::SORT_TAG);
    children << sortTag;
  }
  for(TypeNode::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
    Debug("export") << "type: child: " << *i << std::endl;
    children << exportTypeInternal(*i, from, to, vmap);
  }
  TypeNode out = children.constructTypeNode();// FIXME thread safety
  to_t = to->toType(out);
  return out;
}/* exportTypeInternal() */

}/* CVC4::expr namespace */

Type ExprManager::exportType(const Type& t, ExprManager* em, ExprManagerMapCollection& vmap) {
  Assert(t.d_nodeManager != em->d_nodeManager)
      << "Can't export a Type to the same ExprManager";
  NodeManagerScope ems(t.d_nodeManager);
  return Type(em->d_nodeManager,
              new TypeNode(expr::exportTypeInternal(*t.d_typeNode, t.d_nodeManager, em->d_nodeManager, vmap)));
}

${mkConst_implementations}

}/* CVC4 namespace */
