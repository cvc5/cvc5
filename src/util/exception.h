/*********************                                                        */
/** exception.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** CVC4's exception base class and some associated utilities.
 **/

#ifndef __CVC4__EXCEPTION_H
#define __CVC4__EXCEPTION_H

#include <string>
#include <iostream>
#include "cvc4_config.h"

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
  virtual ~Exception() {}
  // NON-VIRTUAL METHOD for setting and printing the error message
  void setMessage(const std::string& msg) { d_msg = msg; }
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
