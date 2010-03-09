/*********************                                                        */
/** antlr_parser.h
 ** Original author: dejan
 ** Major contributors: cconway
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Base for ANTLR parser classes.
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__ANTLR_PARSER_H
#define __CVC4__PARSER__ANTLR_PARSER_H

#include <vector>
#include <string>
#include <iostream>

#include <antlr/LLkParser.hpp>
#include <antlr/SemanticException.hpp>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "util/Assert.h"
#include "parser/symbol_table.h"

namespace CVC4 {

class Command;
class Type;
class FunctionType;

namespace parser {

/**
 * Wrapper of the ANTLR parser that includes convenience methods that interacts
 * with the expression manager. The grammars should have as little C++ code as
 * possible and all the state and actual functionality (besides parsing) should
 * go into this class.
 */
class AntlrParser : public antlr::LLkParser {

public:

  /** Types of check for the symols */
  enum DeclarationCheck {
    /** Enforce that the symbol has been declared */
    CHECK_DECLARED,
    /** Enforce that the symbol has not been declared */
    CHECK_UNDECLARED,
    /** Don't check anything */
    CHECK_NONE
  };

  /**
   * Sets the expression manager to use when creating/managing expression.
   * @param expr_manager the expression manager
   */
  void setExpressionManager(ExprManager* expr_manager);

  /**
   * Sets the logic for the current benchmark. Declares any logic symbols.
   *
   * @param name the name of the logic (e.g., QF_UF, AUFLIA)
   */
  void setLogic(const std::string& name);

  /**
   * Parse a command.
   * @return a command
   */
  virtual Command* parseCommand() = 0;

  /**
   * Parse an expression.
   * @return the expression
   */
  virtual Expr parseExpr() = 0;

  /** Enable semantic checks during parsing. */
  void enableChecks();

  /** Disable semantic checks during parsing. Disabling checks may lead to crashes on bad inputs. */
  void disableChecks();

protected:

  /**
   * Create a parser with the given input state and token lookahead.
   *
   * @param state the shared input state
   * @param k lookahead
   */
  AntlrParser(const antlr::ParserSharedInputState& state, int k);

  /**
   * Create a parser with the given token buffer and lookahead.
   *
   * @param tokenBuf the token buffer to use in parsing
   * @param k lookahead
   */
  AntlrParser(antlr::TokenBuffer& tokenBuf, int k);

  /**
   * Create a parser with the given token stream and lookahead.
   *
   * @param lexer the lexer to use in parsing
   * @param k lookahead
   */
  AntlrParser(antlr::TokenStream& lexer, int k);

  /**
   * Throws an ANTLR semantic exception with the given message.
   */
  void parseError(const std::string& msg) throw (antlr::SemanticException);

  /**
   * Returns a variable, given a name and a type.
   * @param var_name the name of the variable
   * @return the variable expression
   */
  Expr getVariable(const std::string& var_name);

  /**
   * Returns a function, given a name and a type.
   * @param name the name of the function
   * @return the function expression
   */
  Expr getFunction(const std::string& name);

  /**
   * Returns a sort, given a name
   */
  const Type* getSort(const std::string& sort_name);

  /**
   * Types of symbols. Used to define namespaces.
   */
  enum SymbolType {
    /** Variables */
    SYM_VARIABLE,
    /** Functions */
    SYM_FUNCTION,
    /** Sorts */
    SYM_SORT
  };

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
   * @throws SemanticException if checks are enabled and the check fails
   */
  void checkDeclaration(const std::string& name,
                        DeclarationCheck check,
                        SymbolType type = SYM_VARIABLE)
    throw (antlr::SemanticException);

  /**
   * Checks whether the given name is bound to a function.
   * @param name the name to check
   * @throws SemanticException if checks are enabled and name is not bound to a function
   */
  void checkFunction(const std::string& name) throw (antlr::SemanticException);

  /**
   * Check that <code>kind</code> can accept <code>numArgs</codes> arguments.
   * @param kind the built-in operator to check
   * @param numArgs the number of actual arguments
   * @throws SemanticException if checks are enabled and the operator <code>kind</code> cannot be
   * applied to <code>numArgs</code> arguments.
   */
  void checkArity(Kind kind, unsigned int numArgs) throw (antlr::SemanticException);

  /** 
   * Returns the type for the variable with the given name. 
   * @param name the symbol to lookup 
   * @param type the (namespace) type of the symbol
   */
  const Type* getType(const std::string& var_name,
                      SymbolType type = SYM_VARIABLE);

  /**
   * Returns the true expression.
   * @return the true expression
   */
  Expr getTrueExpr() const;

  /**
   * Returns the false expression.
   * @return the false expression
   */
  Expr getFalseExpr() const;

  /**
   * Creates a new unary CVC4 expression using the expression manager.
   * @param kind the kind of the expression
   * @param child the child
   * @return the new unary expression
   */
  Expr mkExpr(Kind kind, const Expr& child);

  /**
   * Creates a new binary CVC4 expression using the expression manager.
   * @param kind the kind of the expression
   * @param child1 the first child
   * @param child2 the second child
   * @return the new binary expression
   */
  Expr mkExpr(Kind kind, const Expr& child_1, const Expr& child_2);

  /**
   * Creates a new ternary CVC4 expression using the expression manager.
   * @param kind the kind of the expression
   * @param child_1 the first child
   * @param child_2 the second child
   * @param child_3
   * @return the new ternary expression
   */
  Expr mkExpr(Kind kind, const Expr& child_1, const Expr& child_2,
              const Expr& child_3);

  /**
   * Creates a new CVC4 expression using the expression manager.
   * @param kind the kind of the expression
   * @param children the children of the expression
   */
  Expr mkExpr(Kind kind, const std::vector<Expr>& children);

  /** Create a new CVC4 variable expression of the given type. */
  Expr mkVar(const std::string& name, const Type* type);

  /** Create a set of new CVC4 variable expressions of the given
      type. */
  const std::vector<Expr> 
  mkVars(const std::vector<std::string> names, 
         const Type* type);


  /** Returns a function type over the given domain and range types. */
  const Type* functionType(const Type* domain, const Type* range);

  /** Returns a function type over the given types. argTypes must be
      non-empty. */
  const Type* functionType(const std::vector<const Type*>& argTypes,
                           const Type* rangeType);

  /** 
   * Returns a function type over the given types. If types has only
   * one element, then the type is just types[0].
   *
   * @param types a non-empty list of input and output types. 
   */
  const Type* functionType(const std::vector<const Type*>& types);

  /** 
   * Returns a predicate type over the given sorts. If sorts is empty,
   * then the type is just BOOLEAN.

   * @param sorts a list of input types
   */
  const Type* predicateType(const std::vector<const Type*>& sorts);

  /**
   * Creates a new sort with the given name.
   */
  const Type* newSort(const std::string& name);

  /**
   * Creates a new sorts with the given names.
   */
  const std::vector<const Type*>
  newSorts(const std::vector<std::string>& names);

  /** Is the symbol bound to a boolean variable? */
  bool isBoolean(const std::string& name);

  /** Is the symbol bound to a function? */
  bool isFunction(const std::string& name);

  /** Is the symbol bound to a predicate? */
  bool isPredicate(const std::string& name);

  /** Returns the boolean type. */
  const BooleanType* booleanType();

  /** Returns the kind type (i.e., the type of types). */
  const KindType* kindType();

  /** Returns the minimum arity of the given kind. */
  static unsigned int minArity(Kind kind);

  /** Returns the maximum arity of the given kind. */
  static unsigned int maxArity(Kind kind);

  /** Returns a string representation of the given object (for
      debugging). */
  inline std::string toString(DeclarationCheck check) {
    switch(check) {
    case CHECK_NONE: return "CHECK_NONE";
    case CHECK_DECLARED:  return "CHECK_DECLARED";
    case CHECK_UNDECLARED: return "CHECK_UNDECLARED";
    default: Unreachable();
    }
  }

  /** Returns a string representation of the given object (for
      debugging). */
  inline std::string toString(SymbolType type) {
    switch(type) {
    case SYM_VARIABLE: return "SYM_VARIABLE";
    case SYM_FUNCTION: return "SYM_FUNCTION";
    case SYM_SORT: return "SYM_SORT";
    default: Unreachable();
    }
  }

//  bool checksEnabled();

private:

  /** The expression manager */
  ExprManager* d_exprManager;

  /** The symbol table lookup */
  SymbolTable<Expr> d_varSymbolTable;

  /** The sort table */
  SymbolTable<const Type*> d_sortTable;

  /** Are semantic checks enabled during parsing? */
  bool d_checksEnabled;

  /** Lookup a symbol in the given namespace. */
  Expr getSymbol(const std::string& var_name, SymbolType type);
};

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__ANTLR_PARSER_H */
