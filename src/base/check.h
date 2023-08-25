/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Tim King, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Assertion utility classes, functions and macros.
 *
 * Assertion macros assert a condition and aborts() the process if the
 * condition is not satisfied. These macro leave a hanging ostream for the user
 * to specify additional information about the failure.
 *
 * Example usage:
 *   AlwaysAssert(x >= 0) << "x must be positive.";
 *
 * Assert is an AlwaysAssert that is only enabled in debug builds.
 *   Assert(pointer != nullptr);
 *
 * CVC5_FATAL() can be used to indicate unreachable code.
 *
 * Note: The AlwaysAssert and Assert macros are not safe for use in
 *       signal-handling code.
 */

#include "cvc5_private_library.h"

#ifndef CVC5__CHECK_H
#define CVC5__CHECK_H

#include <cvc5/cvc5_export.h>

#include <cstdarg>
#include <ostream>

#include "base/exception.h"

namespace cvc5::internal {

// Implementation notes:
// To understand FatalStream and OStreamVoider, it is useful to understand
// how a AlwaysAssert is structured. AlwaysAssert(cond) is roughly the following
// pattern:
//  cond ? (void)0 : OstreamVoider() & FatalStream().stream()
// This is a carefully crafted message to achieve a hanging ostream using
// operator precedence. The line `AlwaysAssert(cond) << foo << bar;` will bind
// as follows:
//  `cond ? ((void)0) : (OSV() & ((FS().stream() << foo) << bar));`
// Once the expression is evaluated, the destructor ~FatalStream() of the
// temporary object is then run, which abort()'s the process. The role of the
// OStreamVoider() is to match the void type of the true branch.

// Class that provides an ostream and whose destructor aborts! Direct usage of
// this class is discouraged.
class CVC5_EXPORT FatalStream
{
 public:
  FatalStream(const char* function, const char* file, int line);
  [[noreturn]] ~FatalStream();

  std::ostream& stream();

 private:
  void Flush();
};

// Helper class that changes the type of an std::ostream& into a void. See
// "Implementation notes" for more information.
class OstreamVoider
{
 public:
  OstreamVoider() {}
  // The operator precedence between operator& and operator<< is critical here.
  void operator&(std::ostream&) {}
};

// CVC5_FATAL() always aborts a function and provides a convenient way of
// formatting error messages. This can be used instead of a return type.
//
// Example function that returns a type Foo:
//   Foo bar(T t) {
//     switch(t.type()) {
//     ...
//     default:
//       CVC5_FATAL() << "Unknown T type " << t.enum();
//     }
//   }
#define CVC5_FATAL() \
  internal::FatalStream(__PRETTY_FUNCTION__, __FILE__, __LINE__).stream()

/* GCC <= 9.2 ignores CVC5_NO_RETURN of ~FatalStream() if
 * used in template classes (e.g., CDHashMap::save()).  As a workaround we
 * explicitly call abort() to let the compiler know that the
 * corresponding function call will not return. */
#define SuppressWrongNoReturnWarning abort()

// If `cond` is true, log an error message and abort the process.
// Otherwise, does nothing. This leaves a hanging std::ostream& that can be
// inserted into.
#define CVC5_FATAL_IF(cond, function, file, line) \
  CVC5_PREDICT_FALSE(!(cond))                     \
  ? (void)0                                       \
  : cvc5::internal::OstreamVoider()               \
          & cvc5::internal::FatalStream(function, file, line).stream()

// If `cond` is false, log an error message and abort()'s the process.
// Otherwise, does nothing. This leaves a hanging std::ostream& that can be
// inserted into using operator<<. Example usages:
//   AlwaysAssert(x >= 0);
//   AlwaysAssert(x >= 0) << "x must be positive";
//   AlwaysAssert(x >= 0) << "expected a positive value. Got " << x << "
//   instead";
#define AlwaysAssert(cond)                                        \
  CVC5_FATAL_IF(!(cond), __PRETTY_FUNCTION__, __FILE__, __LINE__) \
      << "Check failure\n\n " << #cond << "\n"

// Assert is a variant of AlwaysAssert() that is only checked when
// CVC5_ASSERTIONS is defined. We rely on the optimizer to remove the deadcode.
#ifdef CVC5_ASSERTIONS
#define Assert(cond) AlwaysAssert(cond)
#else
#define Assert(cond) \
  CVC5_FATAL_IF(false, __PRETTY_FUNCTION__, __FILE__, __LINE__)
#endif

class AssertArgumentException : public Exception
{
 protected:
  AssertArgumentException() : Exception() {}

  void construct(const char* header,
                 const char* extra,
                 const char* function,
                 const char* file,
                 unsigned line,
                 const char* fmt,
                 va_list args);

  void construct(const char* header,
                 const char* extra,
                 const char* function,
                 const char* file,
                 unsigned line);

 public:
  AssertArgumentException(const char* condStr,
                          const char* argDesc,
                          const char* function,
                          const char* file,
                          unsigned line,
                          const char* fmt,
                          ...);

  AssertArgumentException(const char* condStr,
                          const char* argDesc,
                          const char* function,
                          const char* file,
                          unsigned line);

}; /* class AssertArgumentException */

#define Unreachable() CVC5_FATAL() << "Unreachable code reached "

#define Unhandled() CVC5_FATAL() << "Unhandled case encountered "

#define Unimplemented() CVC5_FATAL() << "Unimplemented code encountered "

#define InternalError() CVC5_FATAL() << "Internal error detected "

#define IllegalArgument(arg, msg...)              \
  throw cvc5::internal::IllegalArgumentException( \
      "",                                         \
      #arg,                                       \
      __PRETTY_FUNCTION__,                        \
      cvc5::internal::IllegalArgumentException::formatVariadic(msg).c_str());
// This cannot use check argument directly as this forces
// CheckArgument to use a va_list. This is unsupported in Swig.
#define PrettyCheckArgument(cond, arg, msg...)                          \
  do                                                                    \
  {                                                                     \
    if (__builtin_expect((!(cond)), false))                             \
    {                                                                   \
      throw cvc5::internal::IllegalArgumentException(                   \
          #cond,                                                        \
          #arg,                                                         \
          __PRETTY_FUNCTION__,                                          \
          cvc5::internal::IllegalArgumentException::formatVariadic(msg) \
              .c_str());                                                \
    }                                                                   \
  } while (0)
#define AlwaysAssertArgument(cond, arg, msg...)                         \
  do                                                                    \
  {                                                                     \
    if (__builtin_expect((!(cond)), false))                             \
    {                                                                   \
      throw cvc5::internal::AssertArgumentException(                    \
          #cond, #arg, __PRETTY_FUNCTION__, __FILE__, __LINE__, ##msg); \
    }                                                                   \
  } while (0)

#ifdef CVC5_ASSERTIONS
#define AssertArgument(cond, arg, msg...) AlwaysAssertArgument(cond, arg, ##msg)
#define DebugCheckArgument(cond, arg, msg...) CheckArgument(cond, arg, ##msg)
#else                                     /* ! CVC5_ASSERTIONS */
#define AssertArgument(cond, arg, msg...) /*__builtin_expect( ( cond ), true \
                                             )*/
#define DebugCheckArgument( \
    cond, arg, msg...) /*__builtin_expect( ( cond ), true )*/
#endif                 /* CVC5_ASSERTIONS */

}  // namespace cvc5::internal

#endif /* CVC5__CHECK_H */
