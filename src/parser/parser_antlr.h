/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A collection of state for use by parser implementations.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__PARSER_ANTLR_H
#define CVC5__PARSER__PARSER_ANTLR_H

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_export.h>

#include <list>
#include <memory>
#include <set>
#include <string>

#include "parser/api/cpp/symbol_manager.h"
#include "parser/input.h"
#include "parser/parse_op.h"
#include "parser/parser.h"
#include "parser/parser_exception.h"
#include "parser/parser_utils.h"
#include "symbol_table.h"

namespace cvc5 {
namespace parser {

class Command;
class Input;

/**
 * This class is deprecated and used only for the ANTLR parser.
 */
class CVC5_EXPORT Parser : public ParserStateCallback
{
  friend class ParserBuilder;

 private:
  /** The input that we're parsing. */
  std::unique_ptr<Input> d_input;

  /** Are we done */
  bool d_done;
  /**
   * Can we include files?  (Set to false for security purposes in
   * e.g. the online version.)
   */
  bool d_canIncludeFile;

  /**
   * "Preemption commands": extra commands implied by subterms that
   * should be issued before the currently-being-parsed command is
   * issued.  Used to support SMT-LIBv2 ":named" attribute on terms.
   *
   * Owns the memory of the Commands in the queue.
   */
  std::list<std::unique_ptr<Command>> d_commandQueue;

  /** Memory allocation for included files */
  class IncludeFileCache;
  std::unique_ptr<IncludeFileCache> d_incCache;

  /** Get the include file cache */
  IncludeFileCache* getIncludeFileCache();

 protected:
  /**
   * Create a parser state.
   *
   * @attention The parser takes "ownership" of the given
   * input and will delete it on destruction.
   *
   * @param solver solver API object
   * @param symm reference to the symbol manager
   * @param input the parser input
   * @param strictMode whether to incorporate strict(er) compliance checks
   */
  Parser();

 public:

  /** Get the state */
  virtual ParserState* getState() = 0;
  
  virtual ~Parser();

  /** Get the associated input. */
  Input* getInput() const { return d_input.get(); }

  /** Deletes and replaces the current parser input. */
  void setInput(Input* input)
  {
    d_input.reset(input);
    d_input->setParser(*this);
    d_done = false;
  }

  /**
   * Check if we are done -- either the end of input has been reached, or some
   * error has been encountered.
   * @return true if parser is done
   */
  bool done() const { return d_done; }

  /** Sets the done flag */
  void setDone(bool done = true) { d_done = done; }
  /** Enable semantic checks during parsing. */
  void enableChecks();

  /** Disable semantic checks during parsing. Disabling checks may lead to
   * crashes on bad inputs. */
  void disableChecks();

  void allowIncludeFile() { d_canIncludeFile = true; }
  void disallowIncludeFile() { d_canIncludeFile = false; }
  bool canIncludeFile() const { return d_canIncludeFile; }

  /**
   * Preempt the next returned command with other ones; used to
   * support the :named attribute in SMT-LIBv2, which implicitly
   * inserts a new command before the current one. Also used in TPTP
   * because function and predicate symbols are implicitly declared.
   */
  void preemptCommand(std::unique_ptr<Command> cmd) override;

  /** Parse and return the next command. */
  std::unique_ptr<Command> nextCommand();

  /** Parse and return the next expression. */
  cvc5::Term nextExpression();

  /** Issue a warning to the user. */
  void warning(const std::string& msg) override { d_input->warning(msg); }

  /** Raise a parse error with the given message. */
  void parseError(const std::string& msg) override { d_input->parseError(msg); }
  /** Unexpectedly encountered an EOF */
  void unexpectedEOF(const std::string& msg) override
  {
    d_input->parseError(msg, true);
  }

  /**
   * Include smt2 file
   */
  void includeSmt2File(const std::string& filename);
  /**
   * Include tptp file
   */
  void includeTptpFile(const std::string& filename, const std::string& tptpDir);

}; /* class Parser */

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__PARSER_STATE_H */
