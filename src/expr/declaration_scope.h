/*********************                                                        */
/*! \file declaration_scope.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Convenience class for scoping variable and type declarations.
 **
 ** Convenience class for scoping variable and type declarations.
 **/

#ifndef DECLARATION_SCOPE_H
#define DECLARATION_SCOPE_H

#include <ext/hash_map>

#include "expr/expr.h"
#include "util/hash.h"

namespace CVC4 {

class Type;

namespace context {

class Context;

template <class Key, class Data, class HashFcn>
class CDMap;

} //namespace context

class CVC4_PUBLIC ScopeException : public Exception {
};

/**
 * A convenience class for handling scoped declarations. Implements the usual
 * nested scoping rules for declarations, with separate bindings for expressions
 * and types.
 */
class CVC4_PUBLIC DeclarationScope {
  /** The context manager for the scope maps. */
  context::Context *d_context;

  /** A map for expressions. */
  context::CDMap<std::string,Expr,StringHashFunction> *d_exprMap;

  /** A map for types. */
  context::CDMap<std::string,Type,StringHashFunction> *d_typeMap;

public:
  /** Create a declaration scope. */
  DeclarationScope();

  /** Destroy a declaration scope. */
  ~DeclarationScope();

  /** Bind an expression to a name in the current scope level.
   * If <code>name</code> is already bound in the current level, then the
   * binding is replaced. If <code>name</code> is bound in a previous
   * level, then the binding is "covered" by this one until the current
   * scope is popped.
   *
   * @param name an identifier
   * @param obj the expression to bind to <code>name</code>
   */
  void bind(const std::string& name, const Expr& obj) throw ();

  /** Bind a type to a name in the current scope.
   * If <code>name</code> is already bound to a type in the current level,
   * then the binding is replaced. If <code>name</code> is bound in a
   * previous level, then the binding is "covered" by this one until the
   * current scope is popped.
   *
   * @param name an identifier
   * @param t the type to bind to <code>name</code>
   */
  void bindType(const std::string& name, const Type& t) throw ();

  /** Check whether a name is bound to an expression.
   *
   * @param name the identifier to check.
   * @returns true iff name is bound in the current scope.
   */
  bool isBound(const std::string& name) const throw ();

  /** Check whether a name is bound to a type.
   *
   * @param name the identifier to check.
   * @returns true iff name is bound to a type in the current scope.
   */
  bool isBoundType(const std::string& name) const throw ();

  /** Lookup a bound expression.
   *
   * @param name the identifier to lookup
   * @returns the expression bound to <code>name</code> in the current scope.
   */
  Expr lookup(const std::string& name) const throw ();

  /** Lookup a bound type.
   *
   * @param name the identifier to lookup
   * @returns the type bound to <code>name</code> in the current scope.
   */
  Type lookupType(const std::string& name) const throw ();

  /** Pop a scope level. Deletes all bindings since the last call to
   * <code>pushScope</code>. Calls to <code>pushScope</code> and
   * <code>popScope</code> must be "properly nested." I.e., a call to
   * <code>popScope</code> is only legal if the number of prior calls to
   * <code>pushScope</code> on this <code>DeclarationScope</code> is strictly
   * greater than then number of prior calls to <code>popScope</code>. */
  void popScope() throw (ScopeException);

  /** Push a scope level. */
  void pushScope() throw ();
};/* class DeclarationScope */

}/* namespace CVC4 */

#endif /* DECLARATION_SCOPE_H */
