/*********************                                           -*- C++ -*-  */
/** antlr_parser.h
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Base for ANTLR parser classes.
 **/

#ifndef CVC4_PARSER_H_
#define CVC4_PARSER_H_

#include <vector>
#include <string>
#include <iostream>

#include <antlr/LLkParser.hpp>
#include <antlr/SemanticException.hpp>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "util/command.h"
#include "util/Assert.h"
#include "parser/symbol_table.h"

namespace CVC4 {
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
   * Parse a command.
   * @return a command
   */
  virtual Command* parseCommand() = 0;

  /**
   * Parse an expression.
   * @return the expression
   */
  virtual Expr parseExpr() = 0;

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
   * Renames the antlr semantic expression to a given message.
   */
  void rethrow(antlr::SemanticException& e, std::string msg) throw (antlr::SemanticException);

  /**
   * Returns a variable, given a name and a type.
   * @param var_name the name of the variable
   * @return the variable expression
   */
  Expr getVariable(std::string var_name);

  /**
   * Return true if the the declaration policy we want to enforce is true.
   * @param varName the symbol to check
   * @oaram check the kind of check to perform
   * @return true if the check holds
   */
  bool checkDeclation(std::string varName, DeclarationCheck check);

  /**
   * Types of symbols.
   */
  enum SymbolType {
    /** Variables */
    SYM_VARIABLE,
    /** Predicates */
    SYM_PREDICATE,
    /** Functions */
    SYM_FUNCTION
  };

  /**
   * Checks if the variable has been declared.
   * @param the variable name
   */
  bool isDeclared(std::string var_name, SymbolType type = SYM_VARIABLE);

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
   */
  Expr mkExpr(Kind kind, const Expr& child);

  /**
   * Creates a new binary CVC4 expression using the expression manager.
   * @param kind the kind of the expression
   * @param children the children of the expression
   */
  Expr mkExpr(Kind kind, const Expr& child_1, const Expr& child_2);

  /**
   * Creates a new CVC4 expression using the expression manager.
   * @param kind the kind of the expression
   * @param children the children of the expression
   */
  Expr mkExpr(Kind kind, const std::vector<Expr>& children);

  /**
   * Creates a new predicated over the given sorts.
   * @param p_name the name of the predicate
   * @param p_sorts the arity sorts
   */
  void newPredicate(std::string p_name, const std::vector<std::string>& p_sorts);

  /**
   * Creates new predicates of given types.
   * @param p_names the names of the predicates
   */
  void newPredicates(const std::vector<std::string>& p_names);

  /**
   * Returns the precedence rank of the kind.
   */
  static unsigned getPrecedence(Kind kind);

private:

  /** The expression manager */
  ExprManager* d_exprManager;

  /** The symbol table lookup */
  SymbolTable<Expr> d_varSymbolTable;
};

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* CVC4_PARSER_H_ */
