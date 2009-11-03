/*********************                                           -*- C++ -*-  */
/** parser.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_PARSER_H
#define __CVC4_PARSER_H

#include <iostream>
#include "vc.h"
#include "expr.h"

namespace CVC4 {

// In terms of abstraction, this is below (and provides services to)
// the main CVC4 binary and above (and requires the services of)
// ValidityChecker.

class Parser {
private:// maybe protected is better ?
  ValidityChecker *d_vc;

public:
  Parser(ValidityChecker* vc);

  /**
   * Process a file.  Overridden in subclasses to support SMT-LIB
   * format, CVC4 presentation language, etc.  In subclasses, this
   * function should parse terms, build Command objects, and pass them
   * to dispatch().
   */
  virtual Expr process(std::istream&) = 0;

  /**
   * Dispatch a command.
   */
  void dispatch(const Command&);
};/* class Parser */

} /* CVC4 namespace */

#endif /* __CVC4_PARSER_H */
