/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * cvc5's exception base class and some associated utilities.
 */

#include "cvc5_public.h"

#ifndef CVC5__EXCEPTION_H
#define CVC5__EXCEPTION_H

#include <cvc5/cvc5_export.h>

#include <exception>
#include <iosfwd>
#include <string>

namespace cvc5::internal {

class CVC5_EXPORT Exception : public std::exception
{
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
  std::string getMessage() const { return d_msg; }

  // overridden from base class std::exception
  const char* what() const noexcept override { return d_msg.c_str(); }

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
  std::string toString() const;

  /**
   * Printing: feel free to redefine toStream().  When overridden in
   * a derived class, it's recommended that this method print the
   * type of exception before the actual message.
   */
  virtual void toStream(std::ostream& os) const;

}; /* class Exception */

class CVC5_EXPORT IllegalArgumentException : public Exception
{
 protected:
  IllegalArgumentException() : Exception() {}

  void construct(const char* header, const char* extra,
                 const char* function, const char* tail);

  void construct(const char* header, const char* extra,
                 const char* function);

  static std::string format_extra(const char* condStr, const char* argDesc);

  static const char* s_header;

public:

  IllegalArgumentException(const char* condStr, const char* argDesc,
                           const char* function, const char* tail) :
    Exception() {
    construct(s_header, format_extra(condStr, argDesc).c_str(), function, tail);
  }

  IllegalArgumentException(const char* condStr, const char* argDesc,
                           const char* function) :
    Exception() {
    construct(s_header, format_extra(condStr, argDesc).c_str(), function);
  }

  /**
   * This is a convenience function for building usages that are variadic.
   *
   * Having IllegalArgumentException itself be variadic is problematic for
   * making sure calls to IllegalArgumentException clean up memory.
   */
  static std::string formatVariadic();
  static std::string formatVariadic(const char* format, ...);
}; /* class IllegalArgumentException */

inline std::ostream& operator<<(std::ostream& os, const Exception& e);
inline std::ostream& operator<<(std::ostream& os, const Exception& e)
{
  e.toStream(os);
  return os;
}

template <class T>
inline void CheckArgument(bool cond, const T& arg, const char* tail);
template <class T>
inline void CheckArgument(bool cond,
                          const T& arg CVC5_UNUSED,
                          const char* tail CVC5_UNUSED)
{
  if(__builtin_expect( ( !cond ), false )) {
    throw cvc5::internal::IllegalArgumentException("", "", tail);
  }
}
template <class T>
inline void CheckArgument(bool cond, const T& arg);
template <class T>
inline void CheckArgument(bool cond, const T& arg CVC5_UNUSED)
{
  if(__builtin_expect( ( !cond ), false )) {
    throw cvc5::internal::IllegalArgumentException("", "", "");
  }
}

class CVC5_EXPORT LastExceptionBuffer
{
 public:
  LastExceptionBuffer();
  ~LastExceptionBuffer();

  void setContents(const char* string);
  const char* getContents() const { return d_contents; }

  static LastExceptionBuffer* getCurrent() { return s_currentBuffer; }
  static void setCurrent(LastExceptionBuffer* buffer) { s_currentBuffer = buffer; }

  static const char* currentContents() {
    return (getCurrent() == nullptr) ? nullptr : getCurrent()->getContents();
  }

private:
  /* Disallow copies */
  LastExceptionBuffer(const LastExceptionBuffer&) = delete;
  LastExceptionBuffer& operator=(const LastExceptionBuffer&) = delete;

  char* d_contents;

  static thread_local LastExceptionBuffer* s_currentBuffer;
}; /* class LastExceptionBuffer */

}  // namespace cvc5::internal

#endif /* CVC5__EXCEPTION_H */
