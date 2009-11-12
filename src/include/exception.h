/*********************                                           -*- C++ -*-  */
/** exception.h
 ** This file is part of the CVC4 prototype.
 **
 ** Exception class.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_EXCEPTION_H
#ifndef __CVC4_EXCEPTION_H

#include <string>
#include <iostream>

namespace CVC4 {

  class Exception {
  protected:
    std::string d_msg;
  public:
    // Constructors
    Exception(): d_msg("Unknown exception") { }
    Exception(const std::string& msg): d_msg(msg) { }
    Exception(const char* msg): d_msg(msg) { }
    // Destructor
    virtual ~Exception() { }
    // NON-VIRTUAL METHODs for setting and printing the error message
    void setMessage(const std::string& msg) { d_msg = msg; }
    // Printing: feel free to redefine toString().  When inherited,
    // it's recommended that this method print the type of exception
    // before the actual message.
    virtual std::string toString() const { return d_msg; }
    // No need to overload operator<< for the inherited classes
    friend std::ostream& operator<<(std::ostream& os, const Exception& e);

  }; // end of class Exception

  inline std::ostream& operator<<(std::ostream& os, const Exception& e) {
    return os << e.toString();
  }

}/* CVC4 namespace */

#endif /* __CVC4_EXCEPTION_H */
