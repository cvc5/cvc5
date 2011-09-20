/*********************                                                        */
/*! \file exception.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief CVC4's exception base class and some associated utilities.
 **
 ** CVC4's exception base class and some associated utilities.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__EXCEPTION_H
#define __CVC4__EXCEPTION_H

#include <iostream>
#include <string>
#include <sstream>

namespace CVC4 {

class CVC4_PUBLIC Exception {
protected:
  std::string d_msg;

public:
  // Constructors
  Exception() : d_msg("Unknown exception") {}
  Exception(const std::string& msg) : d_msg(msg) {}
  Exception(const char* msg) : d_msg(msg) {}

  // Destructor
  virtual ~Exception() throw() {}

  // NON-VIRTUAL METHOD for setting and printing the error message
  void setMessage(const std::string& msg) { d_msg = msg; }
  std::string getMessage() const { return d_msg; }

  /**
   * Get this exception as a string.  Note that
   *   cout << ex.toString();
   * is subtly different from
   *   cout << ex;
   * which is equivalent to
   *   ex.toStream(cout);
   * That is because with the latter two, the output language (and
   * other preferences) for exprs on the stream is respected.  In
   * toString(), there is no stream, so the parameters are default
   * and you'll get exprs and types printed using the AST language.
   */
  std::string toString() const {
    std::stringstream ss;
    toStream(ss);
    return ss.str();
  }

  /**
   * Printing: feel free to redefine toStream().  When overridden in
   * a derived class, it's recommended that this method print the
   * type of exception before the actual message.
   */
  virtual void toStream(std::ostream& os) const { os << d_msg; }

};/* class Exception */

inline std::ostream& operator<<(std::ostream& os, const Exception& e) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const Exception& e) {
  e.toStream(os);
  return os;
}

}/* CVC4 namespace */

#endif /* __CVC4__EXCEPTION_H */
