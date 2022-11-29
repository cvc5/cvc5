/******************************************************************************
 * Top contributors (to current version):
 *   Christopher L. Conway, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Base for parser inputs.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__INPUT_H
#define CVC5__PARSER__INPUT_H

#include <stdio.h>

#include <iostream>
#include <string>
#include <vector>

#include "api/cpp/cvc5.h"
#include "cvc5_export.h"
#include "options/language.h"
#include "parser/parser_exception.h"

namespace cvc5::parser {

class Command;

class InputStreamException : public internal::Exception
{
 public:
  InputStreamException(const std::string& msg);
};

/** Wrapper around an input stream. */
class InputStream
{
  /** The name of this input stream. */
  std::string d_name;

  /** Indicates whether the input file is a temporary that we should
    * delete on exit. */
  bool d_fileIsTemporary;

 protected:
  /** Initialize the input stream with a name. */
  InputStream(std::string name, bool isTemporary=false) :
    d_name(name),
    d_fileIsTemporary(isTemporary) {
  }

 public:
  /** Destructor. */
  virtual ~InputStream() {
    if( d_fileIsTemporary ) {
      remove(d_name.c_str());
    }
  }

  /** Get the name of this input stream. */
  const std::string getName() const;
}; /* class InputStream */

class Parser;

/**
 * An input to be parsed. The static factory methods in this class (e.g.,
 * <code>newFileInput</code>, <code>newStringInput</code>) create a parser
 * for the given input language and attach it to an input source of the
 * appropriate type.
 *
 * This class is deprecated and used only for the ANTLR parser.
 */
class CVC5_EXPORT Input
{
  friend class Parser; // for parseError, parseCommand, parseExpr
  friend class ParserBuilder;

  /** The input stream. */
  InputStream *d_inputStream;

  /* Since we own d_inputStream and it needs to be freed, we need to prevent
   * copy construction and assignment.  Mark them private and do not define
   * them.
   */
  Input(const Input& input) = delete;
  Input& operator=(const Input& input) = delete;

 public:
  /** Create an input for the given file.
    *
    * @param lang the input language
    * @param filename the input filename
    */
  static Input* newFileInput(const std::string& lang,
                             const std::string& filename);

  /** Create an input for the given stream.
   *
   * @param lang the input language
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   * @param lineBuffered whether this Input should be line-buffered
   * (false, the default, means that the entire Input might be read
   * before being lexed and parsed)
   */
  static Input* newStreamInput(const std::string& lang,
                               std::istream& input,
                               const std::string& name);

  /** Create an input for the given string
   *
   * @param lang the input language
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  static Input* newStringInput(const std::string& lang,
                               const std::string& input,
                               const std::string& name);

  /** Destructor. Frees the input stream and closes the input. */
  virtual ~Input();

  /** Retrieve the name of the input stream */
  const std::string getInputStreamName() { return getInputStream()->getName(); }
 protected:
  /** Create an input.
   *
   * @param inputStream the input stream
   */
  Input(InputStream& inputStream);

  /** Retrieve the input stream for this parser. */
  InputStream *getInputStream();

  /** Parse a command from the input by invoking the
   * implementation-specific parsing method.  Returns
   * <code>NULL</code> if there is no command there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  virtual Command* parseCommand() = 0;

  /**
   * Issue a warning to the user, with source file, line, and column info.
   */
  virtual void warning(const std::string& msg) = 0;

  /**
   * Throws a <code>ParserException</code> with the given message.
   */
  virtual void parseError(const std::string& msg,
                          bool eofException = false) = 0;

  /** Parse an expression from the input by invoking the
   * implementation-specific parsing method. Returns a null
   * <code>cvc5::Term</code> if there is no expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  virtual cvc5::Term parseExpr() = 0;

  /** Set the Parser object for this input. */
  virtual void setParser(Parser& parser) = 0;

}; /* class Input */

}  // namespace cvc5::parser

#endif /* CVC5__PARSER__ANTLR_INPUT_H */
