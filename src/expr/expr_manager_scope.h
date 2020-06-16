/*********************                                                        */
/*! \file expr_manager_scope.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR_MANAGER_SCOPE_H
#define CVC4__EXPR_MANAGER_SCOPE_H

#include "expr/expr.h"
#include "expr/node_manager.h"
#include "expr/expr_manager.h"

namespace CVC4 {

/**
 * Creates a <code>NodeManagerScope</code> with the underlying
 * <code>NodeManager</code> of a given <code>Expr</code> or
 * <code>ExprManager</code>.  The <code>NodeManagerScope</code> is
 * destroyed when the <code>ExprManagerScope</code> is destroyed. See
 * <code>NodeManagerScope</code> for more information.
 */
// NOTE: Here, it seems ExprManagerScope is redundant, since we have
// NodeManagerScope already.  However, without this class, we'd need
// Expr to be a friend of ExprManager, because in the implementation
// of Expr functions, it needs to set the current NodeManager
// correctly (and to do that it needs access to
// ExprManager::getNodeManager()).  So, we make ExprManagerScope a
// friend of ExprManager's, since its implementation is simple to
// read and understand (and verify that it doesn't do any mischief).
//
// ExprManager::getNodeManager() can't just be made public, since
// ExprManager is exposed to clients of the library and NodeManager is
// not.  Similarly, ExprManagerScope shouldn't go in expr_manager.h,
// since that's a public header.
class ExprManagerScope {
  NodeManagerScope d_nms;
public:
  inline ExprManagerScope(const Expr& e) :
    d_nms(e.getExprManager() == NULL
          ? NodeManager::currentNM()
          : e.getExprManager()->getNodeManager()) {
  }
  inline ExprManagerScope(const Type& t) :
    d_nms(t.getExprManager() == NULL
          ? NodeManager::currentNM()
          : t.getExprManager()->getNodeManager()) {
  }
  inline ExprManagerScope(const ExprManager& exprManager) :
    d_nms(exprManager.getNodeManager()) {
  }
};/* class ExprManagerScope */

}/* CVC4 namespace */

#endif /* CVC4__EXPR_MANAGER_SCOPE_H */
