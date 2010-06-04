/*********************                                                        */
/*! \file exception.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

#include <string>

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
    // Printing: feel free to redefine toString().  When inherited,
  // it's recommended that this method print the type of exception
  // before the actual message.
  virtual std::string toString() const { return d_msg; }
  // No need to overload operator<< for the inherited classes
  friend std::ostream& operator<<(std::ostream& os, const Exception& e);
};/* class Exception */

inline std::ostream& operator<<(std::ostream& os, const Exception& e) {
  return os << e.toString();
}

}/* CVC4 namespace */

#endif /* __CVC4__EXCEPTION_H */
