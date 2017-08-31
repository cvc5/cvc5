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

 public:
  AssertionException(const char* extra, const char* function, const char* file,
                     unsigned line, const char* fmt, ...)
      : Exception() {
    va_list args;
    va_start(args, fmt);
    construct("Assertion failure", extra, function, file, line, fmt, args);
    va_end(args);
  }

  AssertionException(const char* extra, const char* function, const char* file,
                     unsigned line)
      : Exception() {
    construct("Assertion failure", extra, function, file, line);
  }
}; /* class AssertionException */

class UnreachableCodeException : public AssertionException {
 protected:
  UnreachableCodeException() : AssertionException() {}

 public:
  UnreachableCodeException(const char* function, const char* file,
                           unsigned line, const char* fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct("Unreachable code reached", NULL, function, file, line, fmt,
              args);
    va_end(args);
  }

  UnreachableCodeException(const char* function, const char* file,
                           unsigned line)
      : AssertionException() {
    construct("Unreachable code reached", NULL, function, file, line);
  }
}; /* class UnreachableCodeException */

class UnhandledCaseException : public UnreachableCodeException {
 protected:
  UnhandledCaseException() : UnreachableCodeException() {}

 public:
  UnhandledCaseException(const char* function, const char* file, unsigned line,
                         const char* fmt, ...)
      : UnreachableCodeException() {
    va_list args;
    va_start(args, fmt);
    construct("Unhandled case encountered", NULL, function, file, line, fmt,
              args);
    va_end(args);
  }

  template <class T>
  UnhandledCaseException(const char* function, const char* file, unsigned line,
                         T theCase)
      : UnreachableCodeException() {
    std::stringstream sb;
    sb << theCase;
    construct("Unhandled case encountered", NULL, function, file, line,
              "The case was: %s", sb.str().c_str());
  }

  UnhandledCaseException(const char* function, const char* file, unsigned line)
      : UnreachableCodeException() {
    construct("Unhandled case encountered", NULL, function, file, line);
  }
}; /* class UnhandledCaseException */

class UnimplementedOperationException : public AssertionException {
 protected:
  UnimplementedOperationException() : AssertionException() {}

 public:
  UnimplementedOperationException(const char* function, const char* file,
                                  unsigned line, const char* fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct("Unimplemented code encountered", NULL, function, file, line, fmt,
              args);
    va_end(args);
  }

  UnimplementedOperationException(const char* function, const char* file,
                                  unsigned line)
      : AssertionException() {
    construct("Unimplemented code encountered", NULL, function, file, line);
  }
}; /* class UnimplementedOperationException */

class AssertArgumentException : public AssertionException {
 protected:
  AssertArgumentException() : AssertionException() {}

 public:
  AssertArgumentException(const char* argDesc, const char* function,
                          const char* file, unsigned line, const char* fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct("Illegal argument detected",
              (std::string("`") + argDesc + "' is a bad argument").c_str(),
              function, file, line, fmt, args);
    va_end(args);
  }

  AssertArgumentException(const char* argDesc, const char* function,
                          const char* file, unsigned line)
      : AssertionException() {
    construct("Illegal argument detected",
              (std::string("`") + argDesc + "' is a bad argument").c_str(),
              function, file, line);
  }

  AssertArgumentException(const char* condStr, const char* argDesc,
                          const char* function, const char* file, unsigned line,
                          const char* fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct("Illegal argument detected",
              (std::string("`") + argDesc + "' is a bad argument; expected " +
               condStr + " to hold")
                  .c_str(),
              function, file, line, fmt, args);
    va_end(args);
  }

  AssertArgumentException(const char* condStr, const char* argDesc,
                          const char* function, const char* file, unsigned line)
      : AssertionException() {
    construct("Illegal argument detected",
              (std::string("`") + argDesc + "' is a bad argument; expected " +
               condStr + " to hold")
                  .c_str(),
              function, file, line);
  }
}; /* class AssertArgumentException */

class InternalErrorException : public AssertionException {
 protected:
  InternalErrorException() : AssertionException() {}

 public:
  InternalErrorException(const char* function, const char* file, unsigned line)
      : AssertionException() {
    construct("Internal error detected", "", function, file, line);
  }

  InternalErrorException(const char* function, const char* file, unsigned line,
                         const char* fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct("Internal error detected", "", function, file, line, fmt, args);
    va_end(args);
  }

  InternalErrorException(const char* function, const char* file, unsigned line,
                         std::string fmt, ...)
      : AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct("Internal error detected", "", function, file, line, fmt.c_str(),
              args);
    va_end(args);
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
void debugAssertionFailed(const AssertionException& thisException,
                          const char* lastException);

// If we're currently handling an exception, print a warning instead;
// otherwise std::terminate() is called by the runtime and we lose
// details of the exception
#define AlwaysAssert(cond, msg...)                                     \
  do {                                                                 \
    if (__builtin_expect((!(cond)), false)) {                          \
      /* save the last assertion failure */                            \
      ::CVC4::LastExceptionBuffer* buffer =                            \
          ::CVC4::LastExceptionBuffer::getCurrent();                   \
      const char* lastException =                                      \
          (buffer == NULL) ? NULL : buffer->getContents();             \
      ::CVC4::AssertionException exception(#cond, __PRETTY_FUNCTION__, \
                                           __FILE__, __LINE__, ##msg); \
      ::CVC4::debugAssertionFailed(exception, lastException);          \
    }                                                                  \
  } while (0)

#else /* CVC4_DEBUG */
// These simpler (but less useful) versions for non-debug builds fails
// will terminate() if thrown during stack unwinding.
#define AlwaysAssert(cond, msg...)                                           \
  do {                                                                       \
    if (__builtin_expect((!(cond)), false)) {                                \
      throw ::CVC4::AssertionException(#cond, __PRETTY_FUNCTION__, __FILE__, \
                                       __LINE__, ##msg);                     \
    }                                                                        \
  } while (0)
#endif /* CVC4_DEBUG */

#define Unreachable(msg...)                                             \
  throw ::CVC4::UnreachableCodeException(__PRETTY_FUNCTION__, __FILE__, \
                                         __LINE__, ##msg)
#define Unhandled(msg...)                                             \
  throw ::CVC4::UnhandledCaseException(__PRETTY_FUNCTION__, __FILE__, \
                                       __LINE__, ##msg)
#define Unimplemented(msg...)                                                  \
  throw ::CVC4::UnimplementedOperationException(__PRETTY_FUNCTION__, __FILE__, \
                                                __LINE__, ##msg)
#define InternalError(msg...)                                         \
  throw ::CVC4::InternalErrorException(__PRETTY_FUNCTION__, __FILE__, \
                                       __LINE__, ##msg)
#define IllegalArgument(arg, msg...)      \
  throw ::CVC4::IllegalArgumentException( \
      "", #arg, __PRETTY_FUNCTION__,      \
      ::CVC4::IllegalArgumentException::formatVariadic(msg).c_str());
// This cannot use check argument directly as this forces
// CheckArgument to use a va_list. This is unsupported in Swig.
#define PrettyCheckArgument(cond, arg, msg...)                            \
  do {                                                                    \
    if (__builtin_expect((!(cond)), false)) {                             \
      throw ::CVC4::IllegalArgumentException(                             \
          #cond, #arg, __PRETTY_FUNCTION__,                               \
          ::CVC4::IllegalArgumentException::formatVariadic(msg).c_str()); \
    }                                                                     \
  } while (0)
#define AlwaysAssertArgument(cond, arg, msg...)                               \
  do {                                                                        \
    if (__builtin_expect((!(cond)), false)) {                                 \
      throw ::CVC4::AssertArgumentException(#cond, #arg, __PRETTY_FUNCTION__, \
                                            __FILE__, __LINE__, ##msg);       \
    }                                                                         \
  } while (0)

#ifdef CVC4_ASSERTIONS
#define Assert(cond, msg...) AlwaysAssert(cond, ##msg)
#define AssertArgument(cond, arg, msg...) AlwaysAssertArgument(cond, arg, ##msg)
#define DebugCheckArgument(cond, arg, msg...) CheckArgument(cond, arg, ##msg)
#else                                     /* ! CVC4_ASSERTIONS */
#define Assert(cond, msg...)              /*__builtin_expect( ( cond ), true )*/
#define AssertArgument(cond, arg, msg...) /*__builtin_expect( ( cond ), true \
                                             )*/
#define DebugCheckArgument(cond, arg, \
                           msg...) /*__builtin_expect( ( cond ), true )*/
#endif                             /* CVC4_ASSERTIONS */

} /* CVC4 namespace */

#endif /* __CVC4__ASSERT_H */
