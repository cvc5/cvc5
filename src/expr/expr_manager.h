/*
 * expr_manager.h
 *
 *  Created on: Dec 10, 2009
 *      Author: dejan
 */

#ifndef __CVC4__EXPR_MANAGER_H
#define __CVC4__EXPR_MANAGER_H

#include "cvc4_config.h"
#include "expr/kind.h"
#include <vector>

namespace CVC4 {

class Expr;
class NodeManager;
class SmtEngine;

class CVC4_PUBLIC ExprManager {

public:

  /**
   * Creates an expressio manager.
   */
  ExprManager();

  /**
   * Destroys the expression manager. No will be deallocated at this point, so
   * any expression references that used to be managed by this expression
   * manager and are left-over are bad.
   */
  ~ExprManager();

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
   * Make a ternary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
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

  // variables are special, because duplicates are permitted
  Expr mkVar();

private:

  /** The internal node manager */
  NodeManager* d_nm;

  /**
   * Returns the internal node manager. This should only be used by internal
   * users, i.e. the friend classes.
   */
  NodeManager* getNodeManager() const;

  /** SmtEngine will use all the internals, so it will grab the node manager */
  friend class SmtEngine;
};

}

#endif /* __CVC4__EXPR_MANAGER_H */
