/*********************                                                        */
/*! \file symbol_table.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Convenience class for scoping variable and type declarations.
 **
 ** Convenience class for scoping variable and type declarations.
 **/

#include "cvc4_public.h"

#ifndef CVC4__SYMBOL_TABLE_H
#define CVC4__SYMBOL_TABLE_H

#include <memory>
#include <string>
#include <vector>

#include "base/exception.h"
#include "expr/expr.h"
#include "expr/type.h"

namespace CVC4 {

class CVC4_PUBLIC ScopeException : public Exception {};

/**
 * A convenience class for handling scoped declarations. Implements the usual
 * nested scoping rules for declarations, with separate bindings for expressions
 * and types.
 */
class CVC4_PUBLIC SymbolTable {
 public:
  /** Create a symbol table. */
  SymbolTable();
  ~SymbolTable();

  /**
   * Bind an expression to a name in the current scope level.
   *
   * When doOverload is false:
   * if <code>name</code> is already bound to an expression in the current
   * level, then the binding is replaced. If <code>name</code> is bound
   * in a previous level, then the binding is "covered" by this one
   * until the current scope is popped.
   * If levelZero is true the name shouldn't be already bound.
   *
   * When doOverload is true:
   * if <code>name</code> is already bound to an expression in the current
   * level, then we mark the previous bound expression and obj as overloaded
   * functions.
   *
   * @param name an identifier
   * @param obj the expression to bind to <code>name</code>
   * @param levelZero set if the binding must be done at level 0
   * @param doOverload set if the binding can overload the function name.
   *
   * Returns false if the binding was invalid.
   */
  bool bind(const std::string& name,
            Expr obj,
            bool levelZero = false,
            bool doOverload = false);

  /**
   * Bind a type to a name in the current scope.  If <code>name</code>
   * is already bound to a type in the current level, then the binding
   * is replaced. If <code>name</code> is bound in a previous level,
   * then the binding is "covered" by this one until the current scope
   * is popped.
   *
   * @param name an identifier
   * @param t the type to bind to <code>name</code>
   * @param levelZero set if the binding must be done at level 0
   */
  void bindType(const std::string& name, Type t, bool levelZero = false);

  /**
   * Bind a type to a name in the current scope.  If <code>name</code>
   * is already bound to a type or type constructor in the current
   * level, then the binding is replaced. If <code>name</code> is
   * bound in a previous level, then the binding is "covered" by this
   * one until the current scope is popped.
   *
   * @param name an identifier
   * @param params the parameters to the type
   * @param t the type to bind to <code>name</code>
   * @param levelZero true to bind it globally (default is to bind it
   * locally within the current scope)
   */
  void bindType(const std::string& name,
                const std::vector<Type>& params,
                Type t,
                bool levelZero = false);

  /**
   * Check whether a name is bound to an expression with bind().
   *
   * @param name the identifier to check.
   * @returns true iff name is bound in the current scope.
   */
  bool isBound(const std::string& name) const;

  /**
   * Check whether a name is bound to a type (or type constructor).
   *
   * @param name the identifier to check.
   * @returns true iff name is bound to a type in the current scope.
   */
  bool isBoundType(const std::string& name) const;

  /**
   * Lookup a bound expression.
   *
   * @param name the identifier to lookup
   * @returns the unique expression bound to <code>name</code> in the current
   * scope.
   * It returns the null expression if there is not a unique expression bound to
   * <code>name</code> in the current scope (i.e. if there is not exactly one).
   */
  Expr lookup(const std::string& name) const;

  /**
   * Lookup a bound type.
   *
   * @param name the type identifier to lookup
   * @returns the type bound to <code>name</code> in the current scope.
   */
  Type lookupType(const std::string& name) const;

  /**
   * Lookup a bound parameterized type.
   *
   * @param name the type-constructor identifier to lookup
   * @param params the types to use to parameterize the type
   * @returns the type bound to <code>name(<i>params</i>)</code> in
   * the current scope.
   */
  Type lookupType(const std::string& name,
                  const std::vector<Type>& params) const;

  /**
   * Lookup the arity of a bound parameterized type.
   */
  size_t lookupArity(const std::string& name);

  /**
   * Pop a scope level, deletes all bindings since the last call to pushScope,
   * and decreases the level by 1.
   *
   * @throws ScopeException if the scope level is 0.
   */
  void popScope();

  /** Push a scope level and increase the scope level by 1. */
  void pushScope();

  /** Get the current level of this symbol table. */
  size_t getLevel() const;

  /** Reset everything. */
  void reset();

  //------------------------ operator overloading
  /** is this function overloaded? */
  bool isOverloadedFunction(Expr fun) const;

  /** Get overloaded constant for type.
   * If possible, it returns the defined symbol with name
   * that has type t. Otherwise returns null expression.
  */
  Expr getOverloadedConstantForType(const std::string& name, Type t) const;

  /**
   * If possible, returns the unique defined function for a name
   * that expects arguments with types "argTypes".
   * For example, if argTypes = (T1, ..., Tn), then this may return an
   * expression with type function(T1, ..., Tn), or constructor(T1, ...., Tn).
   *
   * If there is not a unique defined function for the name and argTypes,
   * this returns the null expression. This can happen either if there are
   * no functions with name and expected argTypes, or alternatively there is
   * more than one function with name and expected argTypes.
   */
  Expr getOverloadedFunctionForTypes(const std::string& name,
                                     const std::vector< Type >& argTypes) const;
  //------------------------ end operator overloading

 private:
  // Copying and assignment have not yet been implemented.
  SymbolTable(const SymbolTable&);
  SymbolTable& operator=(SymbolTable&);

  class Implementation;
  std::unique_ptr<Implementation> d_implementation;
}; /* class SymbolTable */

}  // namespace CVC4

#endif /* CVC4__SYMBOL_TABLE_H */
