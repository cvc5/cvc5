/*********************                                           -*- C++ -*-  */
/** parser.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser abstraction.
 **/

#ifndef __CVC4__PARSER__PARSER_H
#define __CVC4__PARSER__PARSER_H

#include <string>
#include <iostream>

namespace CVC4
{
namespace parser
{

// Forward declarations
class Expr;
class Command;
class ExprManager;
class ParserState;

/**
 * The parser.
 */
class Parser
{
  private:

    /** Internal parser state we are keeping */
    ParserState* d_data;

    /** Initialize the parser */
    void initParser();

    /** Remove the parser components */
    void deleteParser();

  public:

    /** The supported input languages */
    enum InputLanguage {
      /** SMT-LIB language */
      INPUT_SMTLIB,
      /** CVC language */
      INPUT_CVC
    };

    /**
     * Constructor for parsing out of a file.
     * @param em the expression manager to use
     * @param lang the language syntax to use
     * @param file_name the file to parse
     */
    Parser(ExprManager* em, InputLanguage lang, const std::string& file_name);

    /**
     * Destructor.
     */
    ~Parser();

    /** Parse a command */
    Command parseNextCommand();

    /** Parse an expression of the stream */
    Expr parseNextExpression();

    // Check if we are done (end of input has been reached)
    bool done() const;

    // The same check can be done by using the class Parser's value as a Boolean
    operator bool() const { return done(); }

    /** Prints the location to the output stream */
    void printLocation(std::ostream& out) const;

    /** Reset any local data */
    void reset();

}; // end of class Parser

/**
 * The global pointer to ParserTemp.  Each instance of class Parser sets this pointer
 * before any calls to the lexer.  We do it this way because flex and bison use global
 * vars, and we want each Parser object to appear independent.
 */
extern ParserState* _global_parser_state;

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_H */
