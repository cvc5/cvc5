/*********************                                                        */
/** expr_manager.h
 ** Original author: dejan
 ** Major contributors: cconway, mdeters
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Public-facing expression manager interface.
 **/

#ifndef __CVC4__EXPR_MANAGER_H
#define __CVC4__EXPR_MANAGER_H

#include "cvc4_config.h"
#include "expr/kind.h"
#include "expr/node_manager.h"
#include <vector>

namespace CVC4 {

class Expr;
class Type;
class BooleanType; 
class FunctionType; 
class KindType;
class SmtEngine;

class CVC4_PUBLIC ExprManager {

public:

  /**
   * Creates an expression manager.
   */
  ExprManager();

  /**
   * Destroys the expression manager. No will be deallocated at this point, so
   * any expression references that used to be managed by this expression
   * manager and are left-over are bad.
   */
  ~ExprManager();

  /** Get the type for booleans. */
  const BooleanType* booleanType();
  /** Get the type for sorts. */
  const KindType* kindType();

  /**
   * Make a unary expression of a given kind (TRUE, FALSE,...).
   * @param kind the kind of expression
   * @return the expression
   */
  Expr mkExpr(Kind kind);

  /**
   * Make a unary expression of a given kind (NOT, BVNOT, ...).
   * @param kind the kind of expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, const Expr& child1);

  /**
   * Make a binary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2);

  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2,
              const Expr& child3);
  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2,
              const Expr& child3, const Expr& child4);
  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2,
              const Expr& child3, const Expr& child4, const Expr& child5);

  /**
   * Make an n-ary expression of given kind given a vector of it's children
   * @param kind the kind of expression to build
   * @param children the subexpressions
   * @return the n-ary expression
   */
  Expr mkExpr(Kind kind, const std::vector<Expr>& children);

  /** Make a function type from domain to range. */
  const FunctionType* 
    mkFunctionType(const Type* domain, 
                   const Type* range);

  /** Make a function type with input types from argTypes. */
  const FunctionType* 
    mkFunctionType(const std::vector<const Type*>& argTypes, 
                   const Type* range);

  /** Make a new sort with the given name. */
  const Type* mkSort(const std::string& name);

  // variables are special, because duplicates are permitted
  Expr mkVar(const Type* type, const std::string& name);
  Expr mkVar(const Type* type);

private:
  /** The internal node manager */
  NodeManager* d_nodeManager;
  
  /**
   * Returns the internal node manager. This should only be used by internal
   * users, i.e. the friend classes.
   */
  NodeManager* getNodeManager() const;

  /** SmtEngine will use all the internals, so it will grab the node manager */
  friend class SmtEngine;

  /** ExprManagerScope reaches in to get the NodeManager */
  friend class ExprManagerScope;
};

}/* CVC4 namespace */

#include "expr/expr.h"

namespace CVC4 {

/**
 * A wrapper (essentially) for NodeManagerScope.  Without this, we'd
 * need Expr to be a friend of ExprManager.
 */
class ExprManagerScope {
  NodeManagerScope d_nms;
public:
  inline ExprManagerScope(const Expr& e) :
    d_nms(e.getExprManager() == NULL ?
          NodeManager::currentNM() : e.getExprManager()->getNodeManager()) {
  }
};

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_MANAGER_H */

