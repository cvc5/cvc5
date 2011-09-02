/*********************                                                        */
/*! \file type_checker_template.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
  case kind::SORT_TYPE:
    typeNode = nodeManager->kindType();
    break;

${typerules}

#line 51 "${template}"

  default:
    Debug("getType") << "FAILURE" << std::endl;
    Unhandled(n.getKind());
  }

  nodeManager->setAttribute(n, NodeManager::TypeAttr(), typeNode);
  nodeManager->setAttribute(n, NodeManager::TypeCheckedAttr(),
                            check || nodeManager->getAttribute(n, NodeManager::TypeCheckedAttr()));

  return typeNode;

}/* TypeChecker::computeType */

}/* CVC4::expr namespace */
}/* CVC4 namespace */
