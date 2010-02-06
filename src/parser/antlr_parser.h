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

#ifndef CVC4_PARSER_H_
#define CVC4_PARSER_H_

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
  void rethrow(antlr::SemanticException& e, std::string msg)
      throw (antlr::SemanticException);

  /**
   * Returns a variable, given a name and a type.
   * @param var_name the name of the variable
   * @return the variable expression
   */
  Expr getVariable(std::string var_name);
  Expr getFunction(std::string var_name);
  /* Expr getPredicate(std::string var_name); */

  /**
   * Returns a sort, given a name
   */
  const Type* getSort(std::string sort_name);

  /**
   * Types of symbols.
   */
  enum SymbolType {
    /** Variables */
    SYM_VARIABLE,
    /** Predicates */
    /* SYM_PREDICATE, */
    /** Functions */
    SYM_FUNCTION,
    /** Sorts */
    SYM_SORT
  };

  /**
   * Checks if the variable has been declared.
   * @param the variable name
   */
  bool isDeclared(std::string var_name, SymbolType type = SYM_VARIABLE);

  /**
   * Return true if the the declaration policy we want to enforce is true.
   * @param varName the symbol to check
   * @oaram check the kind of check to perform
   * @return true if the check holds
   */
  bool checkDeclaration(std::string varName, 
                        DeclarationCheck check,
                        SymbolType type = SYM_VARIABLE);


  /** Returns the type for the variable with the given name. */
  const Type* getType(std::string var_name,
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

  /* Create a new CVC4 variable expression . */
  Expr mkVar(const std::string name, const Type* type);

  const std::vector<Expr> 
  mkVars(const std::vector<std::string> names, 
         const Type* type);


  /** Returns a function type over the given domain and range types. */
  const FunctionType* functionType(const Type* domain, const Type* range);
  /** Returns a function type over the given types. argTypes must have
      at least 1 element. */
  const FunctionType* functionType(const std::vector<const Type*>& argTypes,
                             const Type* rangeType);
  /** Returns a function type over the given types. types must have
      at least 2 elements (i.e., a domain and range). */
  const FunctionType* functionType(const std::vector<const Type*>& types);

  /**
   * Creates a new function over the given sorts. The function
   * has arity sorts.size() - 1 and range type sorts[sorts.size() - 1].
   * @param name the name of the function
   * @param sorts the sorts
   */
  Expr newFunction(std::string name, 
                   const std::vector<const Type*>& sorts);

  /**
   * Creates new functions over the given sorts. Each function has
   * arity sorts.size() - 1 and range type sorts[sorts.size() - 1].
   * @param name the name of the function
   * @param sorts the sorts
   */
  const std::vector<Expr> 
  newFunctions(const std::vector<std::string>& names, 
               const std::vector<const Type*>& sorts);

  /** Returns a predicate type over the given sorts. sorts must be 
      non-empty. If sorts has size 1, then the type is just BOOLEAN. */
  const Type* predicateType(const std::vector<const Type*>& sorts);

  /**
   * Creates a new predicate (a function with range boolean) over the 
   * given sorts. The predicate has sorts.size().
   * @param name the name of the predicate
   * @param sorts the sorts
   */
  Expr newPredicate(std::string name, const std::vector<const Type*>& sorts);

  /**
   * Creates new predicates (a function with range boolean) over the 
   * given sorts. Each predicate will have arity sorts.size().
   * @param p_names the names of the predicates
   */
  const std::vector<Expr>
  newPredicates(const std::vector<std::string>& names,
                const std::vector<const Type*>& sorts);

  /**
   * Creates a new sort with the given name.
   */
  const Type* newSort(std::string name);

  /**
   * Creates a new sorts with the given names.
   */
  const std::vector<const Type*>
  newSorts(const std::vector<std::string>& names);

  bool isBoolean(std::string name);
  bool isFunction(std::string name);
  bool isPredicate(std::string name);

  const BooleanType* booleanType();
  const KindType* kindType();

  unsigned int minArity(Kind kind);
  unsigned int maxArity(Kind kind);

  /**
   * Returns the precedence rank of the kind.
   */
  static unsigned getPrecedence(Kind kind);

  inline std::string toString(DeclarationCheck check) {
    switch(check) {
    case CHECK_NONE: return "CHECK_NONE";
    case CHECK_DECLARED:  return "CHECK_DECLARED";
    case CHECK_UNDECLARED: return "CHECK_UNDECLARED";
    default: Unreachable();
    }
  }

  inline std::string toString(SymbolType type) {
    switch(type) {
    case SYM_VARIABLE: return "SYM_VARIABLE";
    case SYM_FUNCTION: return "SYM_FUNCTION";
    case SYM_SORT: return "SYM_SORT";
    default: Unreachable();
    }
  }

private:

  /** The expression manager */
  ExprManager* d_exprManager;

  /** The symbol table lookup */
  SymbolTable<Expr> d_varSymbolTable;

  /** A temporary hack: keep all the variable types in their own special
      table. These should actually be Expr attributes. */
  SymbolTable<const Type*> d_varTypeTable;

  /** The sort table */
  SymbolTable<const Type*> d_sortTable;

  Expr getSymbol(std::string var_name, SymbolType type);

};




}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* CVC4_PARSER_H_ */
