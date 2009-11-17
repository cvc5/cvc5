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

#ifndef __CVC4_PARSER_H
#define __CVC4_PARSER_H

#include "core/exception.h"
#include "core/lang.h"

namespace CVC4 {

  class ValidityChecker;
  class Expr;
  
  // Internal parser state and other data
  class ParserData;

  class Parser {
  private:
    ParserData* d_data;
    // Internal methods for constructing and destroying the actual parser
    void initParser();
    void deleteParser();
  public:
    // Constructors
    Parser(ValidityChecker* vc, InputLanguage lang,
	   // The 'interactive' flag is ignored when fileName != ""
	   bool interactive = true,
	   const std::string& fileName = "");
    Parser(ValidityChecker* vc, InputLanguage lang, std::istream& is,
	   bool interactive = false);
    // Destructor
    ~Parser();
    // Read the next command.  
    Expr next();
    // Check if we are done (end of input has been reached)
    bool done() const;
    // The same check can be done by using the class Parser's value as
    // a Boolean
    operator bool() const { return done(); }
    void printLocation(std::ostream & out) const;
    // Reset any local data that depends on validity checker
    void reset();
  }; // end of class Parser

  // The global pointer to ParserTemp.  Each instance of class Parser
  // sets this pointer before any calls to the lexer.  We do it this
  // way because flex and bison use global vars, and we want each
  // Parser object to appear independent.
  class ParserTemp;
  extern ParserTemp* parserTemp;

}/* CVC4 namespace */

#endif /* __CVC4_PARSER_H */
