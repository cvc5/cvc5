/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The symbol manager.
 */

#include "cvc5_public.h"

#ifndef CVC5__EXPR__SYMBOL_MANAGER_H
#define CVC5__EXPR__SYMBOL_MANAGER_H

#include <map>
#include <memory>
#include <string>

#include "api/cpp/cvc5.h"
#include "cvc5_export.h"
#include "expr/symbol_table.h"

namespace cvc5 {

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
  SymbolManager(api::Solver* s);
  ~SymbolManager();
  /** Get the underlying symbol table */
  SymbolTable* getSymbolTable();
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
  NamingResult setExpressionName(api::Term t,
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
  bool getExpressionName(api::Term t,
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
  void getExpressionNames(const std::vector<api::Term>& ts,
                          std::vector<std::string>& names,
                          bool areAssertions = false) const;
  /**
   * Get a mapping of all expression names.
   *
   * @param areAssertions Whether we only wish to include assertion names
   * @return the mapping containing all expression names.
   */
  std::map<api::Term, std::string> getExpressionNames(
      bool areAssertions = false) const;
  /**
   * @return The sorts we have declared that should be printed in the model.
   */
  std::vector<api::Sort> getModelDeclareSorts() const;
  /**
   * @return The terms we have declared that should be printed in the model.
   */
  std::vector<api::Term> getModelDeclareTerms() const;
  /**
   * Add declared sort to the list of model declarations.
   */
  void addModelDeclarationSort(api::Sort s);
  /**
   * Add declared term to the list of model declarations.
   */
  void addModelDeclarationTerm(api::Term t);

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

 private:
  /** The API Solver object. */
  api::Solver* d_solver;
  /**
   * The declaration scope that is "owned" by this symbol manager.
   */
  SymbolTable d_symtabAllocated;
  /** The implementation of the symbol manager */
  class Implementation;
  std::unique_ptr<Implementation> d_implementation;
  /**
   * Whether the global declarations option is enabled. This corresponds to the
   * SMT-LIB option :global-declarations. By default, its value is false.
   */
  bool d_globalDeclarations;
};

}  // namespace cvc5

#endif /* CVC5__EXPR__SYMBOL_MANAGER_H */
