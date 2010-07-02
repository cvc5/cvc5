/*********************                                                        */
/*! \file parser.h
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
 ** \brief A collection of state for use by parser implementations.
 **
 ** A collection of state for use by parser implementations.
 **/

#include "cvc4parser_public.h"

#ifndef __CVC4__PARSER__PARSER_STATE_H
#define __CVC4__PARSER__PARSER_STATE_H

#include <string>
#include <set>

#include "input.h"
#include "parser_exception.h"
#include "parser_options.h"
#include "expr/declaration_scope.h"
#include "expr/expr.h"
#include "expr/kind.h"
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

/**
 * This class encapsulates all of the state of a parser, including the
 * name of the file, line number and column information, and in-scope
 * declarations.
 */
class CVC4_PUBLIC Parser {
  friend class ParserBuilder;

  /** The expression manager */
  ExprManager *d_exprManager;

  /** The input that we're parsing. */
  Input *d_input;

  /** The symbol table */
  DeclarationScope d_declScope;

  /** The name of the input file. */
//  std::string d_filename;

  /** Are we done */
  bool d_done;

  /** Are semantic checks enabled during parsing? */
  bool d_checksEnabled;

  /** Are we parsing in strict mode? */
  bool d_strictMode;

  /** The set of operators available in the current logic. */
  std::set<Kind> d_logicOperators;

  /** Lookup a symbol in the given namespace. */
  Expr getSymbol(const std::string& var_name, SymbolType type);

protected:
  /** Create a parser state. NOTE: The parser takes "ownership" of the given
   * input and will delete it on destruction.
   *
   * @param exprManager the expression manager to use when creating expressions
   * @param input the parser input
   */
  Parser(ExprManager* exprManager, Input* input, bool strictMode = false);

public:

  virtual ~Parser() {
    delete d_input;
  }

  /** Get the associated <code>ExprManager</code>. */
  inline ExprManager* getExprManager() const {
    return d_exprManager;
  }

  /** Get the associated input. */
  inline Input* getInput() const {
    return d_input;
  }

  /** Set the declaration scope manager for this input. NOTE: This should <em>only</me> be
   * called before parsing begins. Otherwise, previous declarations will be lost. */
/*  inline void setDeclarationScope(DeclarationScope declScope) {
    d_declScope = declScope;
  }*/

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
  void enableChecks() { d_checksEnabled = true; }

  /** Disable semantic checks during parsing. Disabling checks may lead to crashes on bad inputs. */
  void disableChecks() { d_checksEnabled = false; }

  /** Enable strict parsing, according to the language standards. */
  void enableStrictMode() { d_strictMode = true; }

  /** Disable strict parsing. Allows certain syntactic infelicities to pass without comment. */
  void disableStrictMode() { d_strictMode = false; }

  bool strictModeEnabled() { return d_strictMode; }

  /** Get the name of the input file. */
/*
  inline const std::string getFilename() {
    return d_filename;
  }
*/

  /**
   * Sets the logic for the current benchmark. Declares any logic symbols.
   *
   * @param name the name of the logic (e.g., QF_UF, AUFLIA)
   */
//  void setLogic(const std::string& name);

  /**
   * Returns a variable, given a name and a type.
   * @param var_name the name of the variable
   * @return the variable expression
   */
  Expr getVariable(const std::string& var_name);

  /**
   * Returns a sort, given a name
   */
  Type getSort(const std::string& sort_name);

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
   * Check that <code>kind</code> can accept <code>numArgs</code> arguments.
   * @param kind the built-in operator to check
   * @param numArgs the number of actual arguments
   * @throws ParserException if checks are enabled and the operator <code>kind</code> cannot be
   * applied to <code>numArgs</code> arguments.
   */
  void checkArity(Kind kind, unsigned int numArgs) throw (ParserException);

  /** Check that <code>kind</code> is a legal operator in the current logic and
   * that it can accept <code>numArgs</code> arguments.
   *
   * @param kind the built-in operator to check
   * @param numArgs the number of actual arguments
   * @throws ParserException if the parser mode is strict and the operator <code>kind</kind>
   * has not been enabled
   */
  void checkOperator(Kind kind, unsigned int numArgs) throw (ParserException);

  /**
   * Returns the type for the variable with the given name.
   * @param var_name the symbol to lookup
   * @param type the (namespace) type of the symbol
   */
  Type getType(const std::string& var_name, SymbolType type = SYM_VARIABLE);

  /** Create a new CVC4 variable expression of the given type. */
  Expr mkVar(const std::string& name, const Type& type);

  /** Create a set of new CVC4 variable expressions of the given
   type. */
  const std::vector<Expr>
  mkVars(const std::vector<std::string> names, const Type& type);

  /** Create a new variable definition (e.g., from a let binding). */
  void defineVar(const std::string& name, const Expr& val);

  /** Create a new type definition. */
  void defineType(const std::string& name, const Type& type);

  /**
   * Creates a new sort with the given name.
   */
  Type mkSort(const std::string& name);

  /**
   * Creates a new sorts with the given names.
   */
  const std::vector<Type>
  mkSorts(const std::vector<std::string>& names);

  /** Add an operator to the current legal set.
   *
   * @param kind the built-in operator to add
   */
  void addOperator(Kind kind);

  /** Is the symbol bound to a boolean variable? */
  bool isBoolean(const std::string& name);

  /** Is the symbol bound to a function? */
  bool isFunction(const std::string& name);

  /** Is the symbol bound to a predicate? */
  bool isPredicate(const std::string& name);

  Command* nextCommand() throw(ParserException);
  Expr nextExpression() throw(ParserException);

  inline void parseError(const std::string& msg) throw (ParserException) {
    d_input->parseError(msg);
  }

  inline void pushScope() { d_declScope.pushScope(); }
  inline void popScope() { d_declScope.popScope(); }
}; // class Parser

} // namespace parser

} // namespace CVC4

#endif /* __CVC4__PARSER__PARSER_STATE_H */
