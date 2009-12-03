/*********************                                           -*- C++ -*-  */
/** parser_state.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Extra state of the parser shared by the lexer and parser.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4__PARSER__PARSER_STATE_H
#define __CVC4__PARSER__PARSER_STATE_H

#include <vector>
#include <iostream>
#include <map>
#include "expr/expr.h"
#include "smt/smt_engine.h"

namespace CVC4 {
namespace parser {

/**
 * The state of the parser.
 */
class ParserState {
public:

  /** Possible status values of a benchmark */
  enum BenchmarkStatus {
    SATISFIABLE,
    UNSATISFIABLE,
    UNKNOWN
  };

  /** The default constructor. */
  ParserState(SmtEngine* smt, ExprManager* em) : d_uid(0), d_prompt_main("CVC>"), d_prompt_continue("- "), d_prompt("CVC"), d_expressionManager(em), d_smtEngine(smt), d_input_line(0), d_done(false) {}

  /** Parser error handling */
  int parseError(const std::string& s);

  /** Get the next uniqueID as a string */
  std::string getNextUniqueID();

  /** Get the current prompt */
  std::string getCurrentPrompt() const;

  /** Set the prompt to the main one */
  void setPromptMain();

  /** Set the prompt to the secondary one */
  void setPromptNextLine();

  /** Increases the current line number */
  void increaseLineNumber();

  /** Gets the line number */
  int getLineNumber() const;

  /** Gets the file we are parsing, if any */
  std::string getFileName() const;

  /**
   * Are we done yet?
   */
  bool done() const { return d_done; }

  /**
   * We are done.
   */
  void setDone() { d_done = true; }

  /**
   * Parses the next chunk of input from the stream. Reads at most size characters
   * from the input stream and copies them into the buffer.
   * @param the buffer to put the read characters into
   * @param size the max numer of character
   */
  int read(char* buffer, int size);

  /**
   * Makes room for a new string literal (empties the buffer).
   */
  void newStringLiteral() { d_string_buffer.clear(); }

  /**
   * Returns the current string literal.
   */
  std::string getStringLiteral() const { return d_string_buffer; }

  /**
   * Appends the first character of str to the string literal buffer. If
   * is_escape is true, the first character should be '\' and second character
   * is examined to determine the escaped character.
   */
  void appendCharToStringLiteral(const char* str, bool is_escape = false) {
    if(is_escape) {
      // fixme
    } else d_string_buffer += str[0];
  }

  /**
   * Sets the name of the benchmark.
   */
  void setBenchmarkName(const std::string bench_name) { d_benchmark_name = bench_name; }

  /**
   * Returns the benchmark name.
   */
  std::string getBenchmarkName() const { return d_benchmark_name; }

  /**
   * Set the status of the parsed benchmark.
   */
  void setBenchmarkStatus(BenchmarkStatus status) { d_status = status; }

  /**
   * Get the status of the parsed benchmark.
   */
  BenchmarkStatus getBenchmarkStatus() const { return d_status; }

  /**
   * Set the logic of the benchmark.
   */
  void setBenchmarkLogic(const std::string logic) { d_logic = logic; }

  /**
   * Declare a unary predicate (Boolean variable).
   */
  void declareNewPredicate(const std::string pred_name) {
    d_preds.insert( make_pair(pred_name, d_expressionManager->mkExpr(VARIABLE)) );
  }

  /**
   * Creates a new expression, given the kind and the children
   */
  CVC4::Expr* newExpression(CVC4::Kind kind, std::vector<CVC4::Expr>& children) {
    return new Expr(d_expressionManager->mkExpr(kind, children));
  }

  /**
   * Returns a new TRUE Boolean constant.
   */
  CVC4::Expr* getNewTrue() { return new Expr(d_expressionManager->mkExpr(TRUE)); }

  /**
   * Returns a new TRUE Boolean constant.
   */
  CVC4::Expr* getNewFalse() { return new Expr(d_expressionManager->mkExpr(FALSE)); }

  /**
   * Returns a variable, given the name.
   */
  CVC4::Expr* getNewVariableByName(const std::string var_name) const {
    std::map<std::string, Expr>::const_iterator i = d_preds.find(var_name);
    return (i == d_preds.end()) ? 0 : new Expr(i->second);
  }

  /**
   * Sets the command that is the result of the parser.
   */
  void setCommand(CVC4::Command* cmd) { d_command = cmd; }

  /**
   * Gets the command that is the result of the parser.
   */
  CVC4::Command* getCommand() { return d_command; }

  /**
   * Sets the interactive flag on/off. If on, every time we go to a new line
   * (via increaseLineNumber()) the prompt will be printed to stdout.
   */
  void setInteractive(bool interactive = true);

  /**
   * Gets the value of the interactive flag.
   */
  bool interactive() { return d_interactive; }

  /**
   * Gets the SMT Engine
   */
  CVC4::SmtEngine* getSmtEngine() { return d_smtEngine; }

  /**
   * Sets the SMT Engine
   */
  void setSmtEngine(CVC4::SmtEngine* smtEngine) { d_smtEngine = smtEngine; }

  /**
   * Gets the Expression Manager
   */
  CVC4::ExprManager* getExpressionManager() { return d_expressionManager; }

  /**
   * Sets the Expression Manager
   */
  void setExpressionManager(CVC4::ExprManager* exprMgr) { d_expressionManager = exprMgr; }

  /**
   * Sets the input stream
   */
  void setInputStream(std::istream& in) { d_input_stream = &in; }

private:

  /** Counter for uniqueID of bound variables */
  int d_uid;
  /** The main prompt when running interactive */
  std::string d_prompt_main;
  /** The interactive prompt in the middle of a multiline command */
  std::string d_prompt_continue;
  /** The currently used prompt */
  std::string d_prompt;
  /** The expression manager we will be using */
  ExprManager* d_expressionManager;
  /** The smt engine we will be using */
  SmtEngine* d_smtEngine;
  /** The stream we are reading off */
  std::istream* d_input_stream;
  /** The current input line */
  unsigned d_input_line;
  /** File we are parsing */
  std::string d_file_name;
  /** Whether we are done or not */
  bool d_done;
  /** Whether we are running in interactive mode */
  bool d_interactive;

  /** String to buffer the string literals */
  std::string d_string_buffer;

  /** The name of the benchmark if any */
  std::string d_benchmark_name;

  /** The benchmark's status */
  BenchmarkStatus d_status;

  /** The benchmark's logic */
  std::string d_logic;

  /** declared predicates */
  std::map<std::string, Expr> d_preds;

  /** result of parser */
  Command* d_command;
};

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_STATE_H */
