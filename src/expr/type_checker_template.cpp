/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * TypeChecker implementation.
 */

#include <sstream>

#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"
#include "expr/type_checker.h"
#include "expr/type_checker_util.h"

// clang-format off
${typechecker_includes}
// clang-format on

namespace cvc5::internal {
namespace expr {

TypeNode TypeChecker::preComputeType(NodeManager* nodeManager, TNode n)
{
  TypeNode typeNode;

  // Infer the type
  switch (n.getKind())
  {
    case kind::VARIABLE:
    case kind::SKOLEM:
    case kind::BOUND_VARIABLE:
    case kind::INST_CONSTANT:
    case kind::RAW_SYMBOL:
      // variable kinds have their type marked as an attribute upon construction
      typeNode = nodeManager->getAttribute(n, TypeAttr());
      break;
    case kind::BUILTIN:
      typeNode = nodeManager->builtinOperatorType();
      break;

      // clang-format off
${pretyperules}
      // clang-format on

    default:
      // not handled
      break;
  }
  return typeNode;
}

TypeNode TypeChecker::computeType(NodeManager* nodeManager,
                                  TNode n,
                                  bool check,
                                  std::ostream* errOut)
{
  TypeNode typeNode;

  // Infer the type
  switch (n.getKind())
  {

      // clang-format off
${typerules}
      // clang-format on

    default:
      Trace("getType") << "FAILURE" << std::endl;
      Unhandled() << " " << n.getKind();
  }

  return typeNode;

} /* TypeChecker::computeType */

bool TypeChecker::computeIsConst(NodeManager* nodeManager, TNode n)
{
  Assert(n.getMetaKind() == kind::metakind::OPERATOR
         || n.getMetaKind() == kind::metakind::PARAMETERIZED
         || n.getMetaKind() == kind::metakind::NULLARY_OPERATOR);

  switch (n.getKind())
  {
    // clang-format off
${construles}
      // clang-format on

    default:;
  }

  return false;

}/* TypeChecker::computeIsConst */

}  // namespace expr
}  // namespace cvc5::internal
