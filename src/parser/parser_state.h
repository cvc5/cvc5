/*********************                                                        */
/** parser_state.h
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A collection of state for use by parser implementations.
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__PARSER_STATE_H
#define __CVC4__PARSER__PARSER_STATE_H

#include <string>

#include "expr/expr.h"
#include "expr/kind.h"
#include "parser/input.h"
#include "parser/parser_exception.h"
#include "parser/parser_options.h"
#include "parser/symbol_table.h"
#include "util/Assert.h"

namespace CVC4 {

// Forward declarations
class BooleanType;
class ExprManager;
class Command;
class FunctionType;
class KindType;
class Type;

namespace parser {

/** Types of check for the symols */
enum DeclarationCheck {
  /** Enforce that the symbol has been declared */
  CHECK_DECLARED,
  /** Enforce that the symbol has not been declared */
  CHECK_UNDECLARED,
  /** Don't check anything */
  CHECK_NONE
};

/** Returns a string representation of the given object (for
 debugging). */
inline std::string toString(DeclarationCheck check) {
  switch(check) {
  case CHECK_NONE:
    return "CHECK_NONE";
  case CHECK_DECLARED:
    return "CHECK_DECLARED";
  case CHECK_UNDECLARED:
    return "CHECK_UNDECLARED";
  default:
    Unreachable();
  }
}

/**
 * Types of symbols. Used to define namespaces.
 */
enum SymbolType {
  /** Variables */
  SYM_VARIABLE,
  /** Sorts */
  SYM_SORT
};

/** Returns a string representation of the given object (for
 debugging). */
inline std::string toString(SymbolType type) {
  switch(type) {
  case SYM_VARIABLE:
    return "SYM_VARIABLE";
  case SYM_SORT:
    return "SYM_SORT";
  default:
    Unreachable();
  }
}

class ParserState {

  /** The expression manager */
  ExprManager *d_exprManager;

  /** The input that we're parsing. */
  Input *d_input;

  /** The symbol table lookup */
  SymbolTable<Expr> d_varTable;

  /** The sort table */
  SymbolTable<Type*> d_sortTable;

  /** The name of the input file. */
  std::string d_filename;

  /** Are we done */
  bool d_done;

  /** Are semantic checks enabled during parsing? */
  bool d_checksEnabled;


  /** Lookup a symbol in the given namespace. */
  Expr getSymbol(const std::string& var_name, SymbolType type);

public:
  ParserState(ExprManager* exprManager, const std::string& filename, Input* input);

  /** Get the associated <code>ExprManager</code>. */
  inline ExprManager* getExprManager() const {
    return d_exprManager;
  }

  /** Get the associated input. */
  inline Input* getInput() const {
    return d_input;
  }

  /**
   * Check if we are done -- either the end of input has been reached, or some
   * error has been encountered.
   * @return true if parser is done
   */
  inline bool done() const {
    return d_done;
  }

  /** Sets the done flag */
  inline void setDone(bool done = true) {
    d_done = done;
  }

  /** Enable semantic checks during parsing. */
  void enableChecks();

  /** Disable semantic checks during parsing. Disabling checks may lead to crashes on bad inputs. */
  void disableChecks();

  /** Get the name of the input file. */
  inline const std::string getFilename() {
    return d_filename;
  }

  /**
   * Sets the logic for the current benchmark. Declares any logic symbols.
   *
   * @param name the name of the logic (e.g., QF_UF, AUFLIA)
   */
  void setLogic(const std::string& name);

  /**
   * Returns a variable, given a name and a type.
   * @param var_name the name of the variable
   * @return the variable expression
   */
  Expr getVariable(const std::string& var_name);

  /**
   * Returns a sort, given a name
   */
  Type* getSort(const std::string& sort_name);

  /**
   * Checks if a symbol has been declared.
   * @param name the symbol name
   * @param type the symbol type
   * @return true iff the symbol has been declared with the given type
   */
  bool isDeclared(const std::string& name, SymbolType type = SYM_VARIABLE);

  /**
   * Checks if the declaration policy we want to enforce holds
   * for the given symbol.
   * @param name the symbol to check
   * @param check the kind of check to perform
   * @param type the type of the symbol
   * @throws ParserException if checks are enabled and the check fails
   */
  void checkDeclaration(const std::string& name, DeclarationCheck check,
                        SymbolType type = SYM_VARIABLE) throw (ParserException);

  /**
   * Checks whether the given name is bound to a function.
   * @param name the name to check
   * @throws ParserException if checks are enabled and name is not bound to a function
   */
  void checkFunction(const std::string& name) throw (ParserException);

  /**
   * Check that <code>kind</code> can accept <code>numArgs</codes> arguments.
   * @param kind the built-in operator to check
   * @param numArgs the number of actual arguments
   * @throws ParserException if checks are enabled and the operator <code>kind</code> cannot be
   * applied to <code>numArgs</code> arguments.
   */
  void checkArity(Kind kind, unsigned int numArgs) throw (ParserException);

  /**
   * Returns the type for the variable with the given name.
   * @param name the symbol to lookup
   * @param type the (namespace) type of the symbol
   */
  Type* getType(const std::string& var_name, SymbolType type = SYM_VARIABLE);

  /** Create a new CVC4 variable expression of the given type. */
  Expr mkVar(const std::string& name, Type* type);

  /** Create a set of new CVC4 variable expressions of the given
   type. */
  const std::vector<Expr>
  mkVars(const std::vector<std::string> names, Type* type);

  /** Create a new variable definition (e.g., from a let binding). */
  void defineVar(const std::string& name, const Expr& val);
  /** Remove a variable definition (e.g., from a let binding). */
  void undefineVar(const std::string& name);

  /**
   * Creates a new sort with the given name.
   */
  Type* newSort(const std::string& name);

  /**
   * Creates a new sorts with the given names.
   */
  const std::vector<Type*>
  newSorts(const std::vector<std::string>& names);

  /** Is the symbol bound to a boolean variable? */
  bool isBoolean(const std::string& name);

  /** Is the symbol bound to a function? */
  bool isFunction(const std::string& name);

  /** Is the symbol bound to a predicate? */
  bool isPredicate(const std::string& name);

  inline void parseError(const std::string& msg) throw (ParserException) {
    d_input->parseError(msg);
  }

}; // class ParserState

} // namespace parser

} // namespace CVC4

#endif /* __CVC4__PARSER__PARSER_STATE_H */
