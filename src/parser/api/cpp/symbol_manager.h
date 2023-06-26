/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The symbol manager.
 */

#include "cvc5_public.h"

#ifndef CVC5__PARSER__API__CPP__SYMBOL_MANAGER_H
#define CVC5__PARSER__API__CPP__SYMBOL_MANAGER_H

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_export.h>

#include <map>
#include <memory>
#include <string>

namespace cvc5 {

namespace internal::parser {
class SymbolTable;
}

namespace parser {
/** Represents the result of a call to `setExpressionName()`. */
enum class NamingResult
{
  /** The expression name was set successfully. */
  SUCCESS,
  /** The expression already has a name. */
  ERROR_ALREADY_NAMED,
  /** The expression is in a binder. */
  ERROR_IN_BINDER
};

/**
 * Symbol manager, which manages:
 * (1) The symbol table used by the parser,
 * (2) Information related to the (! ... :named s) feature in SMT-LIB version 2.
 *
 * Like SymbolTable, this class currently lives in src/expr/ since it uses
 * context-dependent data structures.
 */
class CVC5_EXPORT SymbolManager
{
 public:
  SymbolManager(cvc5::Solver* s);
  ~SymbolManager();
  /** Get the underlying symbol table */
  internal::parser::SymbolTable* getSymbolTable();

  /**
   * Bind an expression to a name in the current scope level in the underlying
   * symbol table.
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
   * @param doOverload set if the binding can overload the function name.
   *
   * Returns false if the binding was invalid.
   */
  bool bind(const std::string& name, cvc5::Term obj, bool doOverload = false);

  /**
   * Bind a type to a name in the current scope.  If <code>name</code>
   * is already bound to a type in the current level, then the binding
   * is replaced. If <code>name</code> is bound in a previous level,
   * then the binding is "covered" by this one until the current scope
   * is popped.
   *
   * @param name an identifier
   * @param t the type to bind to <code>name</code>
   */
  void bindType(const std::string& name, cvc5::Sort t);

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
   */
  void bindType(const std::string& name,
                const std::vector<cvc5::Sort>& params,
                cvc5::Sort t);
  /**
   * Binds sorts of a list of mutually-recursive datatype declarations.
   *
   * If bindTesters is true, we bind the testers of this datatype to
   * `is-C` where `C` is the name of the constructor for that tester.
   */
  bool bindMutualDatatypeTypes(const std::vector<cvc5::Sort>& datatypes,
                               bool bindTesters = true);

  //---------------------------- named expressions
  /** Set name of term t to name
   *
   * @param t The term to name
   * @param name The given name
   * @param isAssertion Whether t is being given a name in an assertion
   * context. In particular, this is true if and only if there was an assertion
   * command of the form (assert (! t :named name)).
   * @return true if the name was set. This method may return false if t
   * already has a name.
   */
  NamingResult setExpressionName(cvc5::Term t,
                                 const std::string& name,
                                 bool isAssertion = false);
  /** Get name for term t
   *
   * @param t The term
   * @param name The argument to update with the name of t
   * @param isAssertion Whether we only wish to get the assertion name of t
   * @return true if t has a name. If so, name is updated to that name.
   * Otherwise, name is unchanged.
   */
  bool getExpressionName(cvc5::Term t,
                         std::string& name,
                         bool isAssertion = false) const;
  /**
   * Convert list of terms to list of names. This adds to names the names of
   * all terms in ts that has names. Terms that do not have names are not
   * included.
   *
   * Notice that we do not distinguish what terms among those in ts have names.
   * If the caller of this method wants more fine-grained information about what
   * specific terms had names, then use the more fine grained interface above,
   * per term.
   *
   * @param ts The terms
   * @param names The name list
   * @param areAssertions Whether we only wish to include assertion names
   */
  void getExpressionNames(const std::vector<cvc5::Term>& ts,
                          std::vector<std::string>& names,
                          bool areAssertions = false) const;
  /**
   * Get a mapping of all expression names.
   *
   * @param areAssertions Whether we only wish to include assertion names
   * @return the mapping containing all expression names.
   */
  std::map<cvc5::Term, std::string> getExpressionNames(
      bool areAssertions = false) const;
  /**
   * @return The sorts we have declared that should be printed in the model.
   */
  std::vector<cvc5::Sort> getModelDeclareSorts() const;
  /**
   * @return The terms we have declared that should be printed in the model.
   */
  std::vector<cvc5::Term> getModelDeclareTerms() const;
  /**
   * @return The functions we have declared that should be printed in a response
   * to check-synth.
   */
  std::vector<cvc5::Term> getFunctionsToSynthesize() const;
  /**
   * Add declared sort to the list of model declarations.
   */
  void addModelDeclarationSort(cvc5::Sort s);
  /**
   * Add declared term to the list of model declarations.
   */
  void addModelDeclarationTerm(cvc5::Term t);
  /**
   * Add a function to synthesize. This ensures the solution for f is printed
   * in a successful response to check-synth.
   */
  void addFunctionToSynthesize(cvc5::Term f);

  //---------------------------- end named expressions
  /**
   * Get the scope level of the symbol table.
   */
  size_t scopeLevel() const;
  /**
   * Push a scope in the symbol table.
   *
   * @param isUserContext If true, this push is denoting a push of the user
   * context, e.g. via an smt2 push/pop command. Otherwise, this push is
   * due to a let/quantifier binding.
   */
  void pushScope(bool isUserContext);
  /**
   * Pop a scope in the symbol table.
   */
  void popScope();
  /**
   * Reset this symbol manager, which resets the symbol table.
   */
  void reset();
  /**
   * Reset assertions for this symbol manager, which resets the symbol table.
   */
  void resetAssertions();
  /** Set global declarations to the value flag. */
  void setGlobalDeclarations(bool flag);
  /** Get global declarations flag. */
  bool getGlobalDeclarations() const;
  /**
   * Set the last abduct or interpolant to synthesize had the given name. This
   * is required since e.g. get-abduct-next must know the name of the
   * abduct-to-synthesize to print its result. For example, the sequence:
   *   (get-abduct A <conjecture>)
   *   (get-abduct-next)
   * The latter command must know the symbol "A".
   */
  void setLastSynthName(const std::string& name);
  /** Get the name of the last abduct or interpolant to synthesize */
  const std::string& getLastSynthName() const;

  /**
   * Force the logic to the given string. Note that this information is
   * context-independent.
   *
   * @param logic The string of the logic
   * @param isForced If true, the logic is set and we ignore subsequent calls
   * to this method where isForced is false.
   */
  void setLogic(const std::string& logic, bool isForced = false);
  /** Have we called the above method with isForced=true? */
  bool isLogicForced() const;
  /** Get the last string in an above call */
  const std::string& getLogic() const;

 private:
  /** The API Solver object. */
  cvc5::Solver* d_solver;
  /** The implementation of the symbol manager */
  class Implementation;
  std::unique_ptr<Implementation> d_implementation;
  /**
   * Whether the global declarations option is enabled. This corresponds to the
   * SMT-LIB option :global-declarations. By default, its value is false.
   */
  bool d_globalDeclarations;
  /** Whether the logic has been forced with --force-logic. */
  bool d_logicIsForced;
  /** The logic. */
  std::string d_logic;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__EXPR__SYMBOL_MANAGER_H */
