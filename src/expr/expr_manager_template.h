/*********************                                                        */
/*! \file expr_manager_template.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Public-facing expression manager interface
 **
 ** Public-facing expression manager interface.
 **/

#include "cvc4_public.h"

#ifndef CVC4__EXPR_MANAGER_H
#define CVC4__EXPR_MANAGER_H

#include <vector>

#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "util/statistics.h"

${includes}

namespace CVC4 {

namespace api {
class Solver;
}

class Expr;
class SmtEngine;
class NodeManager;
class Options;
class IntStat;
struct ExprManagerMapCollection;
class ResourceManager;

class CVC4_PUBLIC ExprManager {
 private:
  friend api::Solver;
  /** The internal node manager */
  NodeManager* d_nodeManager;

  /** Counts of expressions and variables created of a given kind */
  IntStat* d_exprStatisticsVars[LAST_TYPE + 1];
  IntStat* d_exprStatistics[kind::LAST_KIND];

  /**
   * Returns the internal node manager.  This should only be used by
   * internal users, i.e. the friend classes.
   */
  NodeManager* getNodeManager() const;

  /**
   * SmtEngine will use all the internals, so it will grab the
   * NodeManager.
   */
  friend class SmtEngine;

  /** ExprManagerScope reaches in to get the NodeManager */
  friend class ExprManagerScope;

  /** NodeManager reaches in to get the NodeManager */
  friend class NodeManager;

  // undefined, private copy constructor and assignment op (disallow copy)
  ExprManager(const ExprManager&) = delete;
  ExprManager& operator=(const ExprManager&) = delete;
  /** Creates an expression manager. */
  ExprManager();
 public:
  /**
   * Destroys the expression manager. No will be deallocated at this point, so
   * any expression references that used to be managed by this expression
   * manager and are left-over are bad.
   */
  ~ExprManager();

  /** Get the type for booleans */
  BooleanType booleanType() const;

  /** Get the type for strings. */
  StringType stringType() const;

  /** Get the type for regular expressions. */
  RegExpType regExpType() const;

  /** Get the type for reals. */
  RealType realType() const;

  /** Get the type for integers */
  IntegerType integerType() const;

  /** Get the type for rounding modes */
  RoundingModeType roundingModeType() const;

  /**
   * Make a unary expression of a given kind (NOT, BVNOT, ...).
   * @param kind the kind of expression
   * @param child1 kind the kind of expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, Expr child1);

  /**
   * Make a binary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, Expr child1, Expr child2);

  /**
   * Make a 3-ary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @param child3 the third child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, Expr child1, Expr child2, Expr child3);

  /**
   * Make a 4-ary expression of a given kind (AND, PLUS, ...).
   * @param kind the kind of expression
   * @param child1 the first child of the new expression
   * @param child2 the second child of the new expression
   * @param child3 the third child of the new expression
   * @param child4 the fourth child of the new expression
   * @return the expression
   */
  Expr mkExpr(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4);

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
  Expr mkExpr(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4,
              Expr child5);

  /**
   * Make an n-ary expression of given kind given a vector of its
   * children
   *
   * @param kind the kind of expression to build
   * @param children the subexpressions
   * @return the n-ary expression
   */
  Expr mkExpr(Kind kind, const std::vector<Expr>& children);

  /**
   * Make an n-ary expression of given kind given a first arg and
   * a vector of its remaining children (this can be useful where the
   * kind is parameterized operator, so the first arg is really an
   * arg to the kind to construct an operator)
   *
   * @param kind the kind of expression to build
   * @param child1 the first subexpression
   * @param otherChildren the remaining subexpressions
   * @return the n-ary expression
   */
  Expr mkExpr(Kind kind, Expr child1, const std::vector<Expr>& otherChildren);

  /**
   * Make a nullary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @return the nullary expression
   */
  Expr mkExpr(Expr opExpr);

  /**
   * Make a unary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @param child1 the subexpression
   * @return the unary expression
   */
  Expr mkExpr(Expr opExpr, Expr child1);

  /**
   * Make a binary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @param child1 the first subexpression
   * @param child2 the second subexpression
   * @return the binary expression
   */
  Expr mkExpr(Expr opExpr, Expr child1, Expr child2);

  /**
   * Make a ternary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @param child1 the first subexpression
   * @param child2 the second subexpression
   * @param child3 the third subexpression
   * @return the ternary expression
   */
  Expr mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3);

  /**
   * Make a quaternary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @param child1 the first subexpression
   * @param child2 the second subexpression
   * @param child3 the third subexpression
   * @param child4 the fourth subexpression
   * @return the quaternary expression
   */
  Expr mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3, Expr child4);

  /**
   * Make a quinary parameterized expression with the given operator.
   *
   * @param opExpr the operator expression
   * @param child1 the first subexpression
   * @param child2 the second subexpression
   * @param child3 the third subexpression
   * @param child4 the fourth subexpression
   * @param child5 the fifth subexpression
   * @return the quinary expression
   */
  Expr mkExpr(Expr opExpr, Expr child1, Expr child2, Expr child3, Expr child4,
              Expr child5);

  /**
   * Make an n-ary expression of given operator to apply and a vector
   * of its children
   *
   * @param opExpr the operator expression
   * @param children the subexpressions
   * @return the n-ary expression
   */
  Expr mkExpr(Expr opExpr, const std::vector<Expr>& children);

  /** Create a constant of type T */
  template <class T>
  Expr mkConst(const T&);

  /**
   * Create an Expr by applying an associative operator to the children.
   * If <code>children.size()</code> is greater than the max arity for
   * <code>kind</code>, then the expression will be broken up into
   * suitably-sized chunks, taking advantage of the associativity of
   * <code>kind</code>. For example, if kind <code>FOO</code> has max arity
   * 2, then calling <code>mkAssociative(FOO,a,b,c)</code> will return
   * <code>(FOO (FOO a b) c)</code> or <code>(FOO a (FOO b c))</code>.
   * The order of the arguments will be preserved in a left-to-right
   * traversal of the resulting tree.
   */
  Expr mkAssociative(Kind kind, const std::vector<Expr>& children);

  /**
   * Create an Expr by applying an binary left-associative operator to the
   * children. For example, mkLeftAssociative( f, { a, b, c } ) returns
   * f( f( a, b ), c ).
   */
  Expr mkLeftAssociative(Kind kind, const std::vector<Expr>& children);
  /**
   * Create an Expr by applying an binary right-associative operator to the
   * children. For example, mkRightAssociative( f, { a, b, c } ) returns
   * f( a, f( b, c ) ).
   */
  Expr mkRightAssociative(Kind kind, const std::vector<Expr>& children);

  /** make chain
   *
   * Given a kind k and arguments t_1, ..., t_n, this returns the
   * conjunction of:
   *  (k t_1 t_2) .... (k t_{n-1} t_n)
   * It is expected that k is a kind denoting a predicate, and args is a list
   * of terms of size >= 2 such that the terms above are well-typed.
   */
  Expr mkChain(Kind kind, const std::vector<Expr>& children);

  /**
   * Determine whether Exprs of a particular Kind have operators.
   * @returns true if Exprs of Kind k have operators.
   */
  static bool hasOperator(Kind k);

  /**
   * Get the (singleton) operator of an OPERATOR-kinded kind.  The
   * returned Expr e will have kind BUILTIN, and calling
   * e.getConst<CVC4::Kind>() will yield k.
   */
  Expr operatorOf(Kind k);
  
  /** Get a Kind from an operator expression */
  Kind operatorToKind(Expr e);
  
  /** Make a function type from domain to range. */
  FunctionType mkFunctionType(Type domain, Type range);

  /**
   * Make a function type with input types from argTypes.
   * <code>argTypes</code> must have at least one element.
   */
  FunctionType mkFunctionType(const std::vector<Type>& argTypes, Type range);

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

  /**
   * Make a symbolic expressiontype with types from
   * <code>types[0..types.size()-1]</code>.  <code>types</code> may
   * have any number of elements.
   */
  SExprType mkSExprType(const std::vector<Type>& types);

  /** Make a type representing a floating-point type with the given parameters. */
  FloatingPointType mkFloatingPointType(unsigned exp, unsigned sig) const;

  /** Make a type representing a bit-vector of the given size. */
  BitVectorType mkBitVectorType(unsigned size) const;

  /** Make the type of arrays with the given parameterization. */
  ArrayType mkArrayType(Type indexType, Type constituentType) const;

  /** Make the type of set with the given parameterization. */
  SetType mkSetType(Type elementType) const;

  /** Make the type of sequence with the given parameterization. */
  SequenceType mkSequenceType(Type elementType) const;

  /** Bits for use in mkSort() flags. */
  enum {
    SORT_FLAG_NONE = 0,
    SORT_FLAG_PLACEHOLDER = 1
  };/* enum */

  /** Make a new sort with the given name. */
  SortType mkSort(const std::string& name, uint32_t flags = SORT_FLAG_NONE) const;

  /** Make a sort constructor from a name and arity. */
  SortConstructorType mkSortConstructor(const std::string& name,
                                        size_t arity,
                                        uint32_t flags = SORT_FLAG_NONE) const;

  /**
   * Get the type of an expression.
   *
   * Throws a TypeCheckingException on failures or if a Type cannot be
   * computed.
   */
  Type getType(Expr e, bool check = false);

  /** Bits for use in mkVar() flags. */
  enum {
    VAR_FLAG_NONE = 0,
    VAR_FLAG_GLOBAL = 1,
    VAR_FLAG_DEFINED = 2
  };/* enum */

  /**
   * Create a new, fresh variable.  This variable is guaranteed to be
   * distinct from every variable thus far in the ExprManager, even
   * if it shares a name with another; this is to support any kind of
   * scoping policy on top of ExprManager.  The SymbolTable class
   * can be used to store and lookup symbols by name, if desired.
   *
   * @param name a name to associate to the fresh new variable
   * @param type the type for the new variable
   * @param flags - VAR_FLAG_NONE - no flags;
   * VAR_FLAG_GLOBAL - whether this variable is to be
   * considered "global" or not.  Note that this information isn't
   * used by the ExprManager, but is passed on to the ExprManager's
   * event subscribers like the model-building service; if isGlobal
   * is true, this newly-created variable will still available in
   * models generated after an intervening pop.
   * VAR_FLAG_DEFINED - if this is to be a "defined" symbol, e.g., for
   * use with SmtEngine::defineFunction().  This keeps a declaration
   * from being emitted in API dumps (since a subsequent definition is
   * expected to be dumped instead).
   */
  Expr mkVar(const std::string& name, Type type, uint32_t flags = VAR_FLAG_NONE);

  /**
   * Create a (nameless) new, fresh variable.  This variable is guaranteed
   * to be distinct from every variable thus far in the ExprManager.
   *
   * @param type the type for the new variable
   * @param flags - VAR_FLAG_GLOBAL - whether this variable is to be considered "global"
   * or not.  Note that this information isn't used by the ExprManager,
   * but is passed on to the ExprManager's event subscribers like the
   * model-building service; if isGlobal is true, this newly-created
   * variable will still available in models generated after an
   * intervening pop.
   */
  Expr mkVar(Type type, uint32_t flags = VAR_FLAG_NONE);

  /**
   * Create a new, fresh variable for use in a binder expression
   * (the BOUND_VAR_LIST of a FORALL, EXISTS, LAMBDA, or WITNESS).  It is
   * an error for this bound variable to exist outside of a binder,
   * and it should also only be used in a single binder expression.
   * That is, two distinct FORALL expressions should use entirely
   * disjoint sets of bound variables (however, a single FORALL
   * expression can be used in multiple places in a formula without
   * a problem).  This newly-created bound variable is guaranteed to
   * be distinct from every variable thus far in the ExprManager, even
   * if it shares a name with another; this is to support any kind of
   * scoping policy on top of ExprManager.  The SymbolTable class
   * can be used to store and lookup symbols by name, if desired.
   *
   * @param name a name to associate to the fresh new bound variable
   * @param type the type for the new bound variable
   */
  Expr mkBoundVar(const std::string& name, Type type);

  /**
   * Create a (nameless) new, fresh variable for use in a binder
   * expression (the BOUND_VAR_LIST of a FORALL, EXISTS, LAMBDA, or WITNESS).
   * It is an error for this bound variable to exist outside of a
   * binder, and it should also only be used in a single binder
   * expression.  That is, two distinct FORALL expressions should use
   * entirely disjoint sets of bound variables (however, a single FORALL
   * expression can be used in multiple places in a formula without
   * a problem).  This newly-created bound variable is guaranteed to
   * be distinct from every variable thus far in the ExprManager.
   *
   * @param type the type for the new bound variable
   */
  Expr mkBoundVar(Type type);

  /**
   * Create unique variable of type 
   */
  Expr mkNullaryOperator( Type type, Kind k);

  /** Get a reference to the statistics registry for this ExprManager */
  Statistics getStatistics() const;

  /** Get a reference to the statistics registry for this ExprManager */
  SExpr getStatistic(const std::string& name) const;

  /**
   * Flushes statistics for this ExprManager to a file descriptor. Safe to use
   * in a signal handler.
   */
  void safeFlushStatistics(int fd) const;

  /** Export an expr to a different ExprManager */
  //static Expr exportExpr(const Expr& e, ExprManager* em);
  /** Export a type to a different ExprManager */
  static Type exportType(const Type& t, ExprManager* em, ExprManagerMapCollection& vmap);

  /** Returns the minimum arity of the given kind. */
  static unsigned minArity(Kind kind);

  /** Returns the maximum arity of the given kind. */
  static unsigned maxArity(Kind kind);

  /** Whether a kind is n-ary. The test is based on n-ary kinds having their
   * maximal arity as the maximal possible number of children of a node.
   **/
  static bool isNAryKind(Kind fun);
};/* class ExprManager */

${mkConst_instantiations}

}/* CVC4 namespace */

#endif /* CVC4__EXPR_MANAGER_H */
