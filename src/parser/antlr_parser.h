/*
 * antlr_parser.h
 *
 *  Created on: Nov 30, 2009
 *      Author: dejan
 */

#ifndef CVC4_PARSER_H_
#define CVC4_PARSER_H_

#include <vector>
#include <string>
#include <iostream>

#include <antlr/LLkParser.hpp>
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "util/command.h"
#include "util/assert.h"

namespace CVC4 {

namespace parser {

/**
 * Wrapper of the ANTLR parser that includes convenience methods that interacts
 * with the expression manager. The grammars should have as little C++ code as
 * possible and all the state and actuall functionality (besides parsing) should
 * go into this class.
 */
class AntlrParser : public antlr::LLkParser {

public:

  /** The status an SMT benchmark can have */
  enum BenchmarkStatus {
    /** Benchmark is satisfiable */
    SMT_SATISFIABLE,
    /** Benchmark is unsatisfiable */
    SMT_UNSATISFIABLE,
    /** The status of the benchmark is unknown */
    SMT_UNKNOWN
  };

protected:

  /**
   * Class constructor, just tunnels the construction to the antlr
   * LLkParser class.
   *
   * @param state the shared input state
   * @param k lookahead
   */
  AntlrParser(const antlr::ParserSharedInputState& state, int k);

  /**
   * Class constructor, just tunnels the construction to the antlr
   * LLkParser class.
   *
   * @param tokenBuf the token buffer to use in parsing
   * @param k lookahead
   */
  AntlrParser(antlr::TokenBuffer& tokenBuf, int k);

  /**
   * Class constructor, just tunnels the construction to the antlr
   * LLkParser class.
   *
   * @param lexer the lexer to use in parsing
   * @param k lookahead
   */
  AntlrParser(antlr::TokenStream& lexer, int k);

  /**
   * Returns a variable, given a name and a type.
   * @param var_name the name of the variable
   * @return the variable expression
   */
  Expr getVariable(std::string var_name);

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
   * Creates a new CVC4 expression using the expression manager.
   * @param kind the kind of the expression
   * @param children the children of the expression
   */
  Expr newExpression(Kind kind, const std::vector<Expr>& children);

  /**
   * Creates a new predicated over the given sorts.
   * @param p_name the name of the predicate
   * @param p_sorts the arity sorts
   */
  void newPredicate(std::string p_name, std::vector<std::string>& p_sorts);

  /**
   * Sets the status of the benchmark.
   * @param status the status of the benchmark
   */
  void setBenchmarkStatus(BenchmarkStatus status);

  /**
   * Returns the status of the parsed benchmark.
   * @return the status of the parsed banchmark
   */
  BenchmarkStatus getBenchmarkStatus() const;

  /**
   * Adds the extra sorts to the signature of the benchmark.
   * @param extra_sorts the sorts to add
   */
  void addExtraSorts(std::vector<std::string>& extra_sorts);

  /**
   *
   */
  void addCommand(Command* cmd);

  /**
   * Set's the expression manager to use when creating/managing expression.
   * @param expr_manager the expression manager
   */
  void setExpressionManager(ExprManager* expr_manager);

private:

  /** The status of the benchmark */
  BenchmarkStatus d_benchmark_status;

  /** The expression manager */
  ExprManager* d_expr_manager;
};

std::ostream& operator << (std::ostream& out, AntlrParser::BenchmarkStatus status);

}

}

#endif /* CVC4_PARSER_H_ */
