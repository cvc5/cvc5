/*********************                                                        */
/*! \file input.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Base for parser inputs.
 **
 ** Base for parser inputs.
 **/

#include "cvc4parser_public.h"

#ifndef __CVC4__PARSER__INPUT_H
#define __CVC4__PARSER__INPUT_H

#include <iostream>
#include <string>
#include <stdio.h>
#include <vector>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "parser/parser_exception.h"
#include "util/Assert.h"
#include "util/language.h"

namespace CVC4 {

class Command;
class Type;
class FunctionType;

namespace parser {

class CVC4_PUBLIC InputStreamException : public Exception {

public:
  InputStreamException(const std::string& msg);
  virtual ~InputStreamException() throw() { }
};

/** Wrapper around an input stream. */
class InputStream {

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
};

class Parser;

/**
 * An input to be parsed. The static factory methods in this class (e.g.,
 * <code>newFileInput</code>, <code>newStringInput</code>) create a parser
 * for the given input language and attach it to an input source of the
 * appropriate type.
 */
class CVC4_PUBLIC Input {
  friend class Parser; // for parseError, parseCommand, parseExpr
  friend class ParserBuilder;

  /** The input stream. */
  InputStream *d_inputStream;

  /* Since we own d_inputStream and it needs to be freed, we need to prevent
   * copy construction and assignment.  Mark them private and do not define
   * them.
   */
  Input(const Input& input) CVC4_UNUSED;
  Input& operator=(const Input& input) CVC4_UNUSED;

public:

  /** Create an input for the given file.
    *
    * @param lang the input language
    * @param filename the input filename
    * @param useMmap true if the parser should use memory-mapped I/O (default: false)
    */
  static Input* newFileInput(InputLanguage lang, 
                             const std::string& filename, 
                             bool useMmap = false)
    throw (InputStreamException, AssertionException);

  /** Create an input for the given stream.
   *
   * @param lang the input language
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  static Input* newStreamInput(InputLanguage lang, 
                               std::istream& input, 
                               const std::string& name,
                               bool lineBuffered = false)
    throw (InputStreamException, AssertionException);

  /** Create an input for the given string
   *
   * @param lang the input language
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  static Input* newStringInput(InputLanguage lang, 
                               const std::string& input, 
                               const std::string& name)
    throw (InputStreamException, AssertionException);


  /** Destructor. Frees the input stream and closes the input. */
  virtual ~Input();

  /** Retrieve the remaining text in this input. */
  virtual std::string getUnparsedText() = 0;

  /** Get the language that this Input is reading. */
  virtual InputLanguage getLanguage() const throw() = 0;

  /** Retrieve the name of the input stream */
  const std::string getInputStreamName(){
    return getInputStream()->getName();
  }

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
  virtual Command* parseCommand()
    throw (ParserException, TypeCheckingException, AssertionException) = 0;

  /**
   * Issue a warning to the user, with source file, line, and column info.
   */
  virtual void warning(const std::string& msg) = 0;

  /**
   * Throws a <code>ParserException</code> with the given message.
   */
  virtual void parseError(const std::string& msg)
    throw (ParserException, AssertionException) = 0;

  /** Parse an expression from the input by invoking the
   * implementation-specific parsing method. Returns a null
   * <code>Expr</code> if there is no expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  virtual Expr parseExpr()
    throw (ParserException, TypeCheckingException, AssertionException) = 0;

  /** Set the Parser object for this input. */
  virtual void setParser(Parser& parser) = 0;

};/* class Input */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__ANTLR_INPUT_H */
