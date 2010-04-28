/*********************                                                        */
/** expr_manager_template.h
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): taking, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Public-facing expression manager interface.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__EXPR_MANAGER_H
#define __CVC4__EXPR_MANAGER_H

#include <vector>

#include "expr/kind.h"
#include "expr/type.h"

${includes}

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 33 "${template}"

namespace CVC4 {

class Expr;
class SmtEngine;
class NodeManager;

namespace context {
  class Context;
}/* CVC4::context namespace */

class CVC4_PUBLIC ExprManager {
private:
  /** The context */
  context::Context* d_ctxt;

  /** The internal node manager */
  NodeManager* d_nodeManager;

  /**
   * Returns the internal node manager.  This should only be used by
   * internal users, i.e. the friend classes.
   */
  NodeManager* getNodeManager() const;

  /**
   * Returns the internal Context.  Used by internal users, i.e. the
   * friend classes.
   */
  context::Context* getContext() const;

  /**
   * SmtEngine will use all the internals, so it will grab the
   * NodeManager.
   */
  friend class SmtEngine;

  /** ExprManagerScope reaches in to get the NodeManager */
  friend class ExprManagerScope;

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

  /** Get the type for booleans */
  BooleanType booleanType() const;

  /** Get the type for sorts. */
  KindType kindType() const;

  /** Get the type for reals. */
  RealType realType() const;

  /** Get the type for integers */
  IntegerType integerType() const;

  /**
   * Make a unary expression of a given kind (TRUE, FALSE,...).
   * @param kind the kind of expression
   * @return the expression
   */
  Expr mkExpr(Kind kind);

  /**
   * Make a unary expression of a given kind (NOT, BVNOT, ...).
   * @param child1 kind the kind of expression
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

  /**
   * Make a 3-ary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @param child3 the third child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2,
              const Expr& child3);

  /**
   * Make a 4-ary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @param child3 the third child of the new expression
   * @param child4 the fourth child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2,
              const Expr& child3, const Expr& child4);

  /**
   * Make a 5-ary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @param child3 the third child of the new expression
   * @param child4 the fourth child of the new expression
   * @param child5 the fifth child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2,
              const Expr& child3, const Expr& child4, const Expr& child5);

  /**
   * Make an n-ary expression of given kind given a vector of it's children
   * @param kind the kind of expression to build
   * @param children the subexpressions
   * @return the n-ary expression
   */
  Expr mkExpr(Kind kind, const std::vector<Expr>& children);

  /** Create a constant of type T */
  template <class T>
  Expr mkConst(const T&);

  /** Make a function type from domain to range. */
  FunctionType mkFunctionType(const Type& domain, const Type& range);

  /**
   * Make a function type with input types from argTypes.
   * <code>argTypes</code> must have at least one element.
   */
  FunctionType mkFunctionType(const std::vector<Type>& argTypes, const Type& range);

  /**
   * Make a function type with input types from
   * <code>sorts[0..sorts.size()-2]</code> and result type
   * <code>sorts[sorts.size()-1]</code>. <code>sorts</code> must have
   * at least 2 elements.
   */
  FunctionType mkFunctionType(const std::vector<Type>& sorts);

  /**
   * Make a predicate type with input types from
   * <code>sorts</code>. The result with be a function type with range
   * <code>BOOLEAN</code>. <code>sorts</code> must have at least one
   * element.
   */
  FunctionType mkPredicateType(const std::vector<Type>& sorts);

  /** Make a new sort with the given name. */
  SortType mkSort(const std::string& name);

  /** Get the type of an expression */
  Type getType(const Expr& e);

  // variables are special, because duplicates are permitted
  Expr mkVar(const std::string& name, const Type& type);
  Expr mkVar(const Type& type);

  /** Returns the minimum arity of the given kind. */
  static unsigned minArity(Kind kind);

  /** Returns the maximum arity of the given kind. */
  static unsigned maxArity(Kind kind);
};

${mkConst_instantiations}

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_MANAGER_H */
