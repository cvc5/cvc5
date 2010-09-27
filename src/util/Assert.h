/*********************                                                        */
/*! \file Assert.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Assertion utility classes, functions, exceptions, and macros.
 **
 ** Assertion utility classes, functions, exceptions, and macros.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__ASSERT_H
#define __CVC4__ASSERT_H

#include <string>
#include <sstream>
#include <cstdio>
#include <cstdlib>
#include <cstdarg>

#include "util/exception.h"
#include "util/output.h"
#include "util/tls.h"

namespace CVC4 {

class CVC4_PUBLIC AssertionException : public Exception {
protected:
  void construct(const char* header, const char* extra,
                 const char* function, const char* file,
                 unsigned line, const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    construct(header, extra, function, file, line, fmt, args);
    va_end(args);
  }

  void construct(const char* header, const char* extra,
                 const char* function, const char* file,
                 unsigned line, const char* fmt, va_list args);

  void construct(const char* header, const char* extra,
                 const char* function, const char* file,
                 unsigned line);

  AssertionException() : Exception() {}

public:
  AssertionException(const char* extra, const char* function,
                     const char* file, unsigned line,
                     const char* fmt, ...) :
    Exception() {
    va_list args;
    va_start(args, fmt);
    construct("Assertion failure", extra, function, file, line, fmt, args);
    va_end(args);
  }

  AssertionException(const char* extra, const char* function,
                     const char* file, unsigned line) :
    Exception() {
    construct("Assertion failure", extra, function, file, line);
  }
};/* class AssertionException */

class CVC4_PUBLIC UnreachableCodeException : public AssertionException {
protected:
  UnreachableCodeException() : AssertionException() {}

public:
  UnreachableCodeException(const char* function, const char* file,
                           unsigned line, const char* fmt, ...) :
    AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct("Unreachable code reached",
              NULL, function, file, line, fmt, args);
    va_end(args);
  }

  UnreachableCodeException(const char* function, const char* file,
                           unsigned line) :
    AssertionException() {
    construct("Unreachable code reached", NULL, function, file, line);
  }
};/* class UnreachableCodeException */

class CVC4_PUBLIC UnhandledCaseException : public UnreachableCodeException {
protected:
  UnhandledCaseException() : UnreachableCodeException() {}

public:
  UnhandledCaseException(const char* function, const char* file,
                         unsigned line, const char* fmt, ...) :
    UnreachableCodeException() {
    va_list args;
    va_start(args, fmt);
    construct("Unhandled case encountered",
              NULL, function, file, line, fmt, args);
    va_end(args);
  }

  template <class T>
  UnhandledCaseException(const char* function, const char* file,
                         unsigned line, T theCase) :
    UnreachableCodeException() {
    std::stringstream sb;
    sb << theCase;
    construct("Unhandled case encountered",
              NULL, function, file, line, "The case was: %s", sb.str().c_str());
  }

  UnhandledCaseException(const char* function, const char* file,
                         unsigned line) :
    UnreachableCodeException() {
    construct("Unhandled case encountered", NULL, function, file, line);
  }
};/* class UnhandledCaseException */

class CVC4_PUBLIC UnimplementedOperationException : public AssertionException {
protected:
  UnimplementedOperationException() : AssertionException() {}

public:
  UnimplementedOperationException(const char* function, const char* file,
                                  unsigned line, const char* fmt, ...) :
    AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct("Unimplemented code encountered",
              NULL, function, file, line, fmt, args);
    va_end(args);
  }

  UnimplementedOperationException(const char* function, const char* file,
                                  unsigned line) :
    AssertionException() {
    construct("Unimplemented code encountered", NULL, function, file, line);
  }
};/* class UnimplementedOperationException */

class CVC4_PUBLIC IllegalArgumentException : public AssertionException {
protected:
  IllegalArgumentException() : AssertionException() {}

public:
  IllegalArgumentException(const char* argDesc, const char* function,
                           const char* file, unsigned line,
                           const char* fmt, ...) :
    AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct("Illegal argument detected",
              ( std::string(argDesc) + " invalid" ).c_str(),
              function, file, line, fmt, args);
    va_end(args);
  }

  IllegalArgumentException(const char* argDesc, const char* function,
                           const char* file, unsigned line) :
    AssertionException() {
    construct("Illegal argument detected",
              ( std::string(argDesc) + " invalid" ).c_str(),
              function, file, line);
  }

  IllegalArgumentException(const char* condStr, const char* argDesc,
                           const char* function, const char* file,
                           unsigned line, const char* fmt, ...) :
    AssertionException() {
    va_list args;
    va_start(args, fmt);
    construct("Illegal argument detected",
              ( std::string(argDesc) + " invalid; expected " +
                condStr + " to hold" ).c_str(),
              function, file, line, fmt, args);
    va_end(args);
  }

  IllegalArgumentException(const char* condStr, const char* argDesc,
                           const char* function, const char* file,
                           unsigned line) :
    AssertionException() {
    construct("Illegal argument detected",
              ( std::string(argDesc) + " invalid; expected " +
                condStr + " to hold" ).c_str(),
              function, file, line);
  }
};/* class IllegalArgumentException */

#ifdef CVC4_DEBUG

#ifdef CVC4_DEBUG
extern CVC4_THREADLOCAL_PUBLIC(const char*) s_debugLastException;
#endif /* CVC4_DEBUG */

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
                          const char* lastException) CVC4_PUBLIC;

// If we're currently handling an exception, print a warning instead;
// otherwise std::terminate() is called by the runtime and we lose
// details of the exception
#  define AlwaysAssert(cond, msg...)                                    \
    do {                                                                \
      if(EXPECT_FALSE( ! (cond) )) {                                    \
        /* save the last assertion failure */                           \
        const char* lastException = s_debugLastException;               \
        AssertionException exception(#cond, __PRETTY_FUNCTION__, __FILE__, __LINE__, ## msg); \
        debugAssertionFailed(exception, lastException);                 \
      }                                                                 \
    } while(0)

#else /* CVC4_DEBUG */
// These simpler (but less useful) versions for non-debug builds fails
// will terminate() if thrown during stack unwinding.
#  define AlwaysAssert(cond, msg...)                                    \
     do {                                                               \
       if(EXPECT_FALSE( ! (cond) )) {                                   \
         throw AssertionException(#cond, __PRETTY_FUNCTION__, __FILE__, __LINE__, ## msg); \
       }                                                                \
     } while(0)
#endif /* CVC4_DEBUG */

#define Unreachable(msg...) \
  throw UnreachableCodeException(__PRETTY_FUNCTION__, __FILE__, __LINE__, ## msg)
#define Unhandled(msg...) \
  throw UnhandledCaseException(__PRETTY_FUNCTION__, __FILE__, __LINE__, ## msg)
#define Unimplemented(msg...) \
  throw UnimplementedOperationException(__PRETTY_FUNCTION__, __FILE__, __LINE__, ## msg)
#define IllegalArgument(arg, msg...) \
  throw IllegalArgumentException(#arg, __PRETTY_FUNCTION__, __FILE__, __LINE__, ## msg)
#define CheckArgument(cond, arg, msg...)         \
  AlwaysAssertArgument(cond, arg, ## msg)
#define AlwaysAssertArgument(cond, arg, msg...)  \
  do { \
    if(EXPECT_FALSE( ! (cond) )) { \
      throw IllegalArgumentException(#cond, #arg, __PRETTY_FUNCTION__, __FILE__, __LINE__, ## msg); \
    } \
  } while(0)

#ifdef CVC4_ASSERTIONS
#  define Assert(cond, msg...) AlwaysAssert(cond, ## msg)
#  define AssertArgument(cond, arg, msg...) AlwaysAssertArgument(cond, arg, ## msg)
#else /* ! CVC4_ASSERTIONS */
#  define Assert(cond, msg...) /*EXPECT_TRUE( cond )*/
#  define AssertArgument(cond, arg, msg...) /*EXPECT_TRUE( cond )*/
#endif /* CVC4_ASSERTIONS */

}/* CVC4 namespace */

#endif /* __CVC4__ASSERT_H */
