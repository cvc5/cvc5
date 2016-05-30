/*********************                                                        */
/*! \file parser_exception.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Exception class for parse errors.
 **
 ** Exception class for parse errors.
 **/

#include "cvc4parser_public.h"

#ifndef __CVC4__PARSER__PARSER_EXCEPTION_H
#define __CVC4__PARSER__PARSER_EXCEPTION_H

#include <iostream>
#include <string>
#include <sstream>

#include "base/exception.h"

namespace CVC4 {
namespace parser {

class CVC4_PUBLIC ParserException : public Exception {
public:
  // Constructors
  ParserException() throw() :
    d_filename(),
    d_line(0),
    d_column(0) {
  }

  ParserException(const std::string& msg) throw() :
    Exception(msg),
    d_filename(),
    d_line(0),
    d_column(0) {
  }

  ParserException(const char* msg) throw() :
    Exception(msg),
    d_filename(),
    d_line(0),
    d_column(0) {
  }

  ParserException(const std::string& msg, const std::string& filename,
                  unsigned long line, unsigned long column) throw() :
    Exception(msg),
    d_filename(filename),
    d_line(line),
    d_column(column) {
  }

  // Destructor
  virtual ~ParserException() throw() {}

  virtual void toStream(std::ostream& os) const throw() {
    if( d_line > 0 ) {
      os <<  "Parse Error: " << d_filename << ":" << d_line << "."
         << d_column << ": " << d_msg;
    } else {
      os << "Parse Error: " << d_msg;
    }
  }

  std::string getFilename() const throw() {
    return d_filename;
  }

  int getLine() const throw() {
    return d_line;
  }

  int getColumn() const throw() {
    return d_column;
  }

protected:
  std::string d_filename;
  unsigned long d_line;
  unsigned long d_column;
};/* class ParserException */

class CVC4_PUBLIC ParserEndOfFileException : public ParserException {
public:

  // Constructors same as ParserException's

  ParserEndOfFileException() throw() :
    ParserException() {
  }

  ParserEndOfFileException(const std::string& msg) throw() :
    ParserException(msg) {
  }

  ParserEndOfFileException(const char* msg) throw() :
    ParserException(msg) {
  }

  ParserEndOfFileException(const std::string& msg, const std::string& filename,
                           unsigned long line, unsigned long column) throw() :
    ParserException(msg, filename, line, column) {
  }

};/* class ParserEndOfFileException */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_EXCEPTION_H */
