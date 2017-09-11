/*********************                                                        */
/*! \file cvc4_assert.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Assertion utility classes, functions, exceptions, and macros.
 **
 ** Assertion utility classes, functions, exceptions, and macros.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__ASSERT_H
#define __CVC4__ASSERT_H

#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <sstream>
#include <string>

#include "base/exception.h"
#include "base/portability.h"

// output.h not strictly needed for this header, but it _is_ needed to
// actually _use_ anything in this header, so let's include it.
// Tim : Disabling this and moving it into cvc4_assert.cpp
//#include "util/output.h"


namespace CVC4 {


class AssertionException : public Exception {
 protected:
  void construct(const char* header, const char* extra, const char* function,
                 const char* file, unsigned line, const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    construct(header, extra, function, file, line, fmt, args);
    va_end(args);
  }

  void construct(const char* header, const char* extra, const char* function,
                 const char* file, unsigned line, const char* fmt,
                 va_list args);

  void construct(const char* header, const char* extra, const char* function,
                 const char* file, unsigned line);

  AssertionException() : Exception() {}

  static const std::string s_header;

 public:
  AssertionException(const char* extra, const char* function, const char* file,
                     unsigned line, const char* fmt, ...)
      : Exception() {
    va_list args;
    va_start(args, fmt);
    construct(s_header.c_str(), extra, function, file, line, fmt, args);
    va_end(args);
  }

  AssertionException(const char* extra, const char* function, const char* file,
                     unsigned line)
      : Exception() {
    construct(s_header.c_str(), extra, function, file, line);
  }

  AssertionException(const std::string& msg) : Exception() {
    setMessage(s_header + ".\n" + msg);
  }
}; /* class AssertionException */

class UnreachableCodeException : public AssertionException {
 protected:
  UnreachableCodeException() : AssertionException() {}
  static const std::string s_header;

 public:
  UnreachableCodeException(const char* function, const char* file,
                           unsigned line, const char* fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct(s_header.c_str(), NULL, function, file, line, fmt,
              args);
    va_end(args);
  }

  UnreachableCodeException(const char* function, const char* file,
                           unsigned line)
      : AssertionException() {
    construct(s_header.c_str(), NULL, function, file, line);
  }

  UnreachableCodeException(const std::string& msg) : AssertionException() {
    setMessage(s_header + ".\n" + msg);
  }

}; /* class UnreachableCodeException */
class UnhandledCaseException : public UnreachableCodeException {
 protected:
  UnhandledCaseException() : UnreachableCodeException() {}
  static const std::string s_header;

 public:
  UnhandledCaseException(const char* function, const char* file, unsigned line,
                         const char* fmt, ...)
      : UnreachableCodeException() {
    va_list args;
    va_start(args, fmt);
    construct(s_header.c_str(), NULL, function, file, line, fmt,
              args);
    va_end(args);
  }

  template <class T>
  UnhandledCaseException(const char* function, const char* file, unsigned line,
                         T theCase)
      : UnreachableCodeException() {
    std::stringstream sb;
    sb << theCase;
    construct(s_header.c_str(), NULL, function, file, line,
              "The case was: %s", sb.str().c_str());
  }

  UnhandledCaseException(const char* function, const char* file, unsigned line)
      : UnreachableCodeException() {
    construct(s_header.c_str(), NULL, function, file, line);
  }

  UnhandledCaseException(const std::string& msg) : UnreachableCodeException () {
      setMessage(s_header + ".\n" + msg);
  }
}; /* class UnhandledCaseException */

class UnimplementedOperationException : public AssertionException {
 protected:
  UnimplementedOperationException() : AssertionException() {}
  static const std::string s_header;

 public:
  UnimplementedOperationException(const char* function, const char* file,
                                  unsigned line, const char* fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct(s_header.c_str(), NULL, function, file, line, fmt,
              args);
    va_end(args);
  }

  UnimplementedOperationException(const char* function, const char* file,
                                  unsigned line)
      : AssertionException() {
    construct(s_header.c_str(), NULL, function, file, line);
  }

  UnimplementedOperationException(const std::string& msg) : AssertionException() {
    setMessage(s_header + ".\n" + msg);
  }
}; /* class UnimplementedOperationException */

class AssertArgumentException : public AssertionException {
 protected:
  AssertArgumentException() : AssertionException() {}
  static const std::string s_header;

 public:
  AssertArgumentException(const char* argDesc, const char* function,
                          const char* file, unsigned line, const char* fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct(s_header.c_str(),
              (std::string("`") + argDesc + "' is a bad argument").c_str(),
              function, file, line, fmt, args);
    va_end(args);
  }

  AssertArgumentException(const char* argDesc, const char* function,
                          const char* file, unsigned line)
      : AssertionException() {
    construct(s_header.c_str(),
              (std::string("`") + argDesc + "' is a bad argument").c_str(),
              function, file, line);
  }

  AssertArgumentException(const char* condStr, const char* argDesc,
                          const char* function, const char* file, unsigned line,
                          const char* fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct(s_header.c_str(),
              (std::string("`") + argDesc + "' is a bad argument; expected " +
               condStr + " to hold")
                  .c_str(),
              function, file, line, fmt, args);
    va_end(args);
  }

  AssertArgumentException(const char* condStr, const char* argDesc,
                          const char* function, const char* file, unsigned line)
      : AssertionException() {
    construct(s_header.c_str(),
              (std::string("`") + argDesc + "' is a bad argument; expected " +
               condStr + " to hold")
                  .c_str(),
              function, file, line);
  }

  AssertArgumentException(const std::string& msg) : AssertionException() {
    setMessage(s_header + ".\n" + msg);
  }
}; /* class AssertArgumentException */

class InternalErrorException : public AssertionException {
 protected:
  InternalErrorException() : AssertionException() {}
  static const std::string s_header;

 public:
  InternalErrorException(const char* function, const char* file, unsigned line)
      : AssertionException() {
    construct(s_header.c_str(), "", function, file, line);
  }

  InternalErrorException(const char* function, const char* file, unsigned line,
                         const char* fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct(s_header.c_str(), "", function, file, line, fmt, args);
    va_end(args);
  }

  InternalErrorException(const char* function, const char* file, unsigned line,
                         std::string fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct(s_header.c_str(), "", function, file, line, fmt.c_str(),
              args);
    va_end(args);
  }

  InternalErrorException(const std::string& msg) : AssertionException() {
    setMessage(s_header + ".\n" + msg);
  }

}; /* class InternalErrorException */



#ifdef CVC4_DEBUG

/**
 * Special assertion failure handling in debug mode; in non-debug
 * builds, the exception is thrown from the macro.  We factor out this
 * additional logic so as not to bloat the code at every Assert()
 * expansion.
 *
 * Note this name is prefixed with "debug" because it is included in
 * debug builds only; in debug builds, it handles all assertion
 * failures (even those that exist in non-debug builds).
 */
__CVC4__noreturn void debugAssertionFailed(const AssertionException& thisException,
                          const char* lastException);

/* need to dispatch to ::CVC4::debugAssertionFailed on assertionException */
template <>
class Thrower<::CVC4::AssertionException> {
  protected:
    std::stringstream d_msg;

  public:
    Thrower() {}
    __CVC4__noreturn ~Thrower() throw(::CVC4::AssertionException) {
      /* save the last assertion failure */
      ::CVC4::LastExceptionBuffer* buffer = ::CVC4::LastExceptionBuffer::getCurrent();
      const char* lastException = (buffer == NULL) ? NULL : buffer->getContents();
      ::CVC4::AssertionException exception(d_msg.str());
      ::CVC4::debugAssertionFailed(exception, lastException);
    }

    inline std::ostream& msg() { return d_msg; }
}; /* class Thrower<::CVC4::AssertionException> */

#endif /* CVC4_DEBUG */

#define __CVC4__UNCONDITIONAL_THROW(E)                  \
  ::CVC4::OstreamVoider()                               \
    & ::CVC4::Thrower<E>().msg()

#define __CVC4__CONDITIONAL_THROW(E, cond)              \
  (__CVC4__expect(!(cond), true)) ? (void)0 :           \
    __CVC4__UNCONDITIONAL_THROW(E)

#define __CVC4__STANDARD_EXCEPT_FORMAT                  \
  __CVC4__FUNC_STRING << std::endl                      \
  << __FILE__ << ":" << __LINE__


#define AlwaysAssert(cond)                                            \
  __CVC4__CONDITIONAL_THROW(CVC4::AssertionException, !(cond))        \
    << __CVC4__STANDARD_EXCEPT_FORMAT << ":" << std::endl             \
    << std::endl                                                      \
    << "  " << #cond << std::endl

#define Unreachable()                                                 \
  __CVC4__UNCONDITIONAL_THROW(CVC4::UnreachableCodeException)         \
    << __CVC4__STANDARD_EXCEPT_FORMAT << std::endl

#define Unhandled()                                                   \
  __CVC4__UNCONDITIONAL_THROW(CVC4::UnhandledCaseException)           \
    << __CVC4__STANDARD_EXCEPT_FORMAT << std::endl

#define Unimplemented()                                               \
  __CVC4__UNCONDITIONAL_THROW(CVC4::UnimplementedOperationException)  \
    << __CVC4__STANDARD_EXCEPT_FORMAT << std::endl

#define InternalError()                                               \
  __CVC4__UNCONDITIONAL_THROW(CVC4::InternalErrorException)           \
    << __CVC4__STANDARD_EXCEPT_FORMAT << std::endl

#define IllegalArgument(arg)                                          \
  __CVC4__UNCONDITIONAL_THROW(CVC4::IllegalArgumentException)         \
    << __CVC4__FUNC_STRING <<  std::endl                              \
    << "`" << #arg << "' is a bad argument" << std::endl

#define PrettyCheckArgument(cond, arg)                                \
  __CVC4__CONDITIONAL_THROW(CVC4::IllegalArgumentException, !(cond))  \
    << __CVC4__FUNC_STRING <<  std::endl                              \
    << "`" << #arg << "' is a bad argument; expected "                \
    << #cond << "to hold" << std::endl

#define AlwaysAssertArgument(cond, arg)                               \
  __CVC4__CONDITIONAL_THROW(CVC4::AssertArgumentException, !(cond))   \
    << __CVC4__FUNC_STRING <<  std::endl                              \
    << "`" << #arg << "' is a bad argument; expected "                \
    << #cond << "to hold" << std::endl

#ifdef CVC4_ASSERTIONS
#define Assert(cond) AlwaysAssert(cond)
#define AssertArgument(cond, arg) AlwaysAssertArgument(cond, arg)
#define DebugCheckArgument(cond, arg) PrettyCheckArgument(cond, arg)
#else                                     /* ! CVC4_ASSERTIONS */
#define Assert(cond) AlwaysAssert(true)
#define AssertArgument(cond, arg) AlwaysAssertArgument(true, arg)
#define DebugCheckArgument(cond, arg) PrettyCheckArgument(true, arg)
#endif                             /* CVC4_ASSERTIONS */

} /* CVC4 namespace */

#endif /* __CVC4__ASSERT_H */
