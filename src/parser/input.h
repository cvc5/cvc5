/*********************                                                        */
/** input.h
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser abstraction.
 **/

#include "cvc4parser_public.h"

#ifndef __CVC4__PARSER__PARSER_H
#define __CVC4__PARSER__PARSER_H

#include <string>
#include <iostream>

#include "expr/expr.h"
#include "expr/kind.h"
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
  case CHECK_NONE: return "CHECK_NONE";
  case CHECK_DECLARED:  return "CHECK_DECLARED";
  case CHECK_UNDECLARED: return "CHECK_UNDECLARED";
  default: Unreachable();
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
  case SYM_VARIABLE: return "SYM_VARIABLE";
  case SYM_SORT: return "SYM_SORT";
  default: Unreachable();
  }
}

/**
 * The parser. The parser should be obtained by calling the static methods
 * getNewParser, and should be deleted when done.
 *
 * This class includes convenience methods for interacting with the ExprManager
 * from within a grammar.
 */
class CVC4_PUBLIC Input {

  /** Whether to de-allocate the input */
//  bool d_deleteInput;

  /** The expression manager */
  ExprManager* d_exprManager;

  /** The symbol table lookup */
  SymbolTable<Expr> d_varSymbolTable;

  /** The sort table */
  SymbolTable<Type*> d_sortTable;

  /** The name of the input file. */
  std::string d_filename;

  /** Are we done */
  bool d_done;

  /** Are semantic checks enabled during parsing? */
  bool d_checksEnabled;

public:

  /**
   * Create a new parser for the given file.
   * @param exprManager the ExprManager to use
   * @param filename the path of the file to parse
   */
  Input(ExprManager* exprManager, const std::string& filename);

  /**
   * Destructor.
   */
  ~Input();

  /** Create a parser for the given file.
    *
    * @param exprManager the ExprManager for creating expressions from the input
    * @param lang the input language
    * @param filename the input filename
    */
   static Input* newFileParser(ExprManager* exprManager, InputLanguage lang, const std::string& filename, bool useMmap=false);

  /** Create a parser for the given input stream.
   *
   * @param exprManager the ExprManager for creating expressions from the input
   * @param lang the input language
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  //static Parser* getNewParser(ExprManager* exprManager, InputLanguage lang, std::istream& input, const std::string& name);

  /** Create a parser for the given input string
   *
   * @param exprManager the ExprManager for creating expressions from the input
   * @param lang the input language
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  static Input* newStringParser(ExprManager* exprManager, InputLanguage lang, const std::string& input, const std::string& name);

  /** Get the <code>ExprManager</code> associated with this input. */
  inline ExprManager* getExprManager() const {
    return d_exprManager;
  }

  /**
   * Parse the next command of the input. If EOF is encountered a EmptyCommand
   * is returned and done flag is set.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  Command* parseNextCommand() throw(ParserException);

  /**
   * Parse the next expression of the stream. If EOF is encountered a null
   * expression is returned and done flag is set.
   * @return the parsed expression
   * @throws ParserException if an error is encountered during parsing.
   */
  Expr parseNextExpression() throw(ParserException);

  /**
   * Check if we are done -- either the end of input has been reached, or some
   * error has been encountered.
   * @return true if parser is done
   */
  bool done() const;

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
    void checkDeclaration(const std::string& name,
                          DeclarationCheck check,
                          SymbolType type = SYM_VARIABLE)
      throw (ParserException);

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
    Type* getType(const std::string& var_name,
                        SymbolType type = SYM_VARIABLE);

    /** Create a new CVC4 variable expression of the given type. */
    Expr mkVar(const std::string& name, Type* type);

    /** Create a set of new CVC4 variable expressions of the given
        type. */
    const std::vector<Expr>
    mkVars(const std::vector<std::string> names,
           Type* type);


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

    /** Throws a <code>ParserException</code> with the given error message.
     * Implementations should fill in the <code>ParserException</code> with
     * line number information, etc. */
    virtual void parseError(const std::string& msg) throw (ParserException) = 0;

protected:

  /** Called by <code>parseNextCommand</code> to actually parse a command from
   * the input by invoking the implementation-specific parsing method.  Returns
   * <code>NULL</code> if there is no command there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  virtual Command* doParseCommand() throw(ParserException) = 0;

  /** Called by <code>parseNextExpression</code> to actually parse an
   * expression from the input by invoking the implementation-specific
   * parsing method. Returns a null <code>Expr</code> if there is no
   * expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  virtual Expr doParseExpr() throw(ParserException) = 0;

private:

  /** Sets the done flag */
  void setDone(bool done = true);

  /** Lookup a symbol in the given namespace. */
  Expr getSymbol(const std::string& var_name, SymbolType type);

}; // end of class Parser

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_H */
