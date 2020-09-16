/*********************                                                        */
/*! \file parser_exception.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Exception class for parse errors.
 **
 ** Exception class for parse errors.
 **/

#include "cvc4parser_public.h"

#ifndef CVC4__PARSER__PARSER_EXCEPTION_H
#define CVC4__PARSER__PARSER_EXCEPTION_H

#include <iostream>
#include <string>
#include <sstream>

#include "base/exception.h"

namespace CVC4 {
namespace parser {

class CVC4_PUBLIC ParserException : public Exception {
 public:
  // Constructors
  ParserException() : d_filename(), d_line(0), d_column(0) {}

  ParserException(const std::string& msg)
      : Exception(msg), d_filename(), d_line(0), d_column(0)
  {
  }

  ParserException(const char* msg)
      : Exception(msg), d_filename(), d_line(0), d_column(0)
  {
  }

  ParserException(const std::string& msg,
                  const std::string& filename,
                  unsigned long line,
                  unsigned long column)
      : Exception(msg), d_filename(filename), d_line(line), d_column(column)
  {
  }

  // Destructor
  ~ParserException() override {}

  void toStream(std::ostream& os) const override
  {
    if( d_line > 0 ) {
      os <<  "Parse Error: " << d_filename << ":" << d_line << "."
         << d_column << ": " << d_msg;
    } else {
      os << "Parse Error: " << d_msg;
    }
  }

  std::string getFilename() const { return d_filename; }

  int getLine() const { return d_line; }

  int getColumn() const { return d_column; }

 protected:
  std::string d_filename;
  unsigned long d_line;
  unsigned long d_column;
};/* class ParserException */

class CVC4_PUBLIC ParserEndOfFileException : public ParserException {
 public:
  // Constructors same as ParserException's

  ParserEndOfFileException() : ParserException() {}

  ParserEndOfFileException(const std::string& msg) : ParserException(msg) {}

  ParserEndOfFileException(const char* msg) : ParserException(msg) {}

  ParserEndOfFileException(const std::string& msg,
                           const std::string& filename,
                           unsigned long line,
                           unsigned long column)
      : ParserException(msg, filename, line, column)
  {
  }

};/* class ParserEndOfFileException */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* CVC4__PARSER__PARSER_EXCEPTION_H */
