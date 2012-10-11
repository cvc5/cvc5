/*********************                                                        */
/*! \file type_checker_template.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief TypeChecker implementation
 **
 ** TypeChecker implementation.
 **/

#line 20 "${template}"

#include "expr/type_checker.h"
#include "expr/node_manager.h"

${typechecker_includes}

#line 27 "${template}"

namespace CVC4 {
namespace expr {

TypeNode TypeChecker::computeType(NodeManager* nodeManager, TNode n, bool check)
  throw (TypeCheckingExceptionPrivate, AssertionException) {
  TypeNode typeNode;

  // Infer the type
  switch(n.getKind()) {
  case kind::VARIABLE:
  case kind::SKOLEM:
    typeNode = nodeManager->getAttribute(n, NodeManager::TypeAttr());
    break;
  case kind::BUILTIN:
    typeNode = nodeManager->builtinOperatorType();
    break;

${typerules}

#line 48 "${template}"

  default:
    Debug("getType") << "FAILURE" << std::endl;
    Unhandled(n.getKind());
  }

  nodeManager->setAttribute(n, NodeManager::TypeAttr(), typeNode);
  nodeManager->setAttribute(n, NodeManager::TypeCheckedAttr(),
                            check || nodeManager->getAttribute(n, NodeManager::TypeCheckedAttr()));

  return typeNode;

}/* TypeChecker::computeType */

bool TypeChecker::computeIsConst(NodeManager* nodeManager, TNode n)
  throw (AssertionException) {

  Assert(n.getMetaKind() == kind::metakind::OPERATOR || n.getMetaKind() == kind::metakind::PARAMETERIZED);

  switch(n.getKind()) {
${construles}

#line 71 "${template}"

  default:;
  }

  return false;

}/* TypeChecker::computeIsConst */

}/* CVC4::expr namespace */
}/* CVC4 namespace */
