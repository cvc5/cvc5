/*********************                                                        */
/*! \file check.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Assertion utility classes, functions and macros.
 **
 ** The AlwaysAssert utility classes, functions and macros.
 **
 ** The main usage in the file is the AlwaysAssert macros. The AlwaysAssert
 ** macros assert a condition and aborts()'s the process if the condition is
 ** not satisfied. The macro leaves a hanging ostream for the user to specify
 ** additional information about the failure. Example usage:
 **   AlwaysAssert(x >= 0) << "x must be positive.";
 **
 ** Assert is a AlwaysAssert that is only enabled in debug builds.
 **   Assert(pointer != nullptr);
 **
 ** CVC4_FATAL() can be used to indicate unreachable code.
 **
 ** The AlwaysAssert and Assert macros are not safe for use in
 ** signal-handling code. In future, a a signal-handling safe version of
 ** AlwaysAssert may be added.
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__CHECK_H
#define CVC4__CHECK_H

#include <cstdarg>
#include <ostream>

#include "base/exception.h"

// Define CVC4_NO_RETURN macro replacement for [[noreturn]].
#if defined(SWIG)
#define CVC4_NO_RETURN
// SWIG does not yet support [[noreturn]] so emit nothing instead.
#else
#define CVC4_NO_RETURN [[noreturn]]
// Not checking for whether the compiler supports [[noreturn]] using
// __has_cpp_attribute as GCC 4.8 is too widespread and does not support this.
// We instead assume this is C++11 (or later) and [[noreturn]] is available.
#endif  // defined(SWIG)

// Define CVC4_PREDICT_FALSE(x) that helps the compiler predict that x will be
// false (if there is compiler support).
#ifdef __has_builtin
#if __has_builtin(__builtin_expect)
#define CVC4_PREDICT_FALSE(x) (__builtin_expect(x, false))
#define CVC4_PREDICT_TRUE(x) (__builtin_expect(x, true))
#else
#define CVC4_PREDICT_FALSE(x) x
#define CVC4_PREDICT_TRUE(x) x
#endif
#else
#define CVC4_PREDICT_FALSE(x) x
#define CVC4_PREDICT_TRUE(x) x
#endif

#ifdef __has_cpp_attribute
#if __has_cpp_attribute(fallthrough)
#define CVC4_FALLTHROUGH [[fallthrough]]
#endif // __has_cpp_attribute(fallthrough)
#endif // __has_cpp_attribute
#ifndef CVC4_FALLTHROUGH
#define CVC4_FALLTHROUGH
#endif

namespace CVC4 {

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
class FatalStream
{
 public:
  FatalStream(const char* function, const char* file, int line);
  CVC4_NO_RETURN ~FatalStream();

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

// CVC4_FATAL() always aborts a function and provides a convenient way of
// formatting error messages. This can be used instead of a return type.
//
// Example function that returns a type Foo:
//   Foo bar(T t) {
//     switch(t.type()) {
//     ...
//     default:
//       CVC4_FATAL() << "Unknown T type " << t.enum();
//     }
//   }
#define CVC4_FATAL() \
  FatalStream(__PRETTY_FUNCTION__, __FILE__, __LINE__).stream()

/* GCC <= 9.2 ignores CVC4_NO_RETURN of ~FatalStream() if
 * used in template classes (e.g., CDHashMap::save()).  As a workaround we
 * explicitly call abort() to let the compiler know that the
 * corresponding function call will not return. */
#define SuppressWrongNoReturnWarning abort()

// If `cond` is true, log an error message and abort the process.
// Otherwise, does nothing. This leaves a hanging std::ostream& that can be
// inserted into.
#define CVC4_FATAL_IF(cond, function, file, line) \
  CVC4_PREDICT_FALSE(!(cond))                     \
  ? (void)0 : OstreamVoider() & FatalStream(function, file, line).stream()

// If `cond` is false, log an error message and abort()'s the process.
// Otherwise, does nothing. This leaves a hanging std::ostream& that can be
// inserted into using operator<<. Example usages:
//   AlwaysAssert(x >= 0);
//   AlwaysAssert(x >= 0) << "x must be positive";
//   AlwaysAssert(x >= 0) << "expected a positive value. Got " << x << "
//   instead";
#define AlwaysAssert(cond)                                        \
  CVC4_FATAL_IF(!(cond), __PRETTY_FUNCTION__, __FILE__, __LINE__) \
      << "Check failure\n\n " << #cond << "\n"

// Assert is a variant of AlwaysAssert() that is only checked when
// CVC4_ASSERTIONS is defined. We rely on the optimizer to remove the deadcode.
#ifdef CVC4_ASSERTIONS
#define Assert(cond) AlwaysAssert(cond)
#else
#define Assert(cond) \
  CVC4_FATAL_IF(false, __PRETTY_FUNCTION__, __FILE__, __LINE__)
#endif /* CVC4_DEBUG */

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

#define Unreachable() CVC4_FATAL() << "Unreachable code reached"

#define Unhandled() CVC4_FATAL() << "Unhandled case encountered"

#define Unimplemented() CVC4_FATAL() << "Unimplemented code encountered"

#define InternalError() CVC4_FATAL() << "Internal error detected"

#define IllegalArgument(arg, msg...)      \
  throw ::CVC4::IllegalArgumentException( \
      "",                                 \
      #arg,                               \
      __PRETTY_FUNCTION__,                \
      ::CVC4::IllegalArgumentException::formatVariadic(msg).c_str());
// This cannot use check argument directly as this forces
// CheckArgument to use a va_list. This is unsupported in Swig.
#define PrettyCheckArgument(cond, arg, msg...)                            \
  do                                                                      \
  {                                                                       \
    if (__builtin_expect((!(cond)), false))                               \
    {                                                                     \
      throw ::CVC4::IllegalArgumentException(                             \
          #cond,                                                          \
          #arg,                                                           \
          __PRETTY_FUNCTION__,                                            \
          ::CVC4::IllegalArgumentException::formatVariadic(msg).c_str()); \
    }                                                                     \
  } while (0)
#define AlwaysAssertArgument(cond, arg, msg...)                         \
  do                                                                    \
  {                                                                     \
    if (__builtin_expect((!(cond)), false))                             \
    {                                                                   \
      throw ::CVC4::AssertArgumentException(                            \
          #cond, #arg, __PRETTY_FUNCTION__, __FILE__, __LINE__, ##msg); \
    }                                                                   \
  } while (0)

#ifdef CVC4_ASSERTIONS
#define AssertArgument(cond, arg, msg...) AlwaysAssertArgument(cond, arg, ##msg)
#define DebugCheckArgument(cond, arg, msg...) CheckArgument(cond, arg, ##msg)
#else                                     /* ! CVC4_ASSERTIONS */
#define AssertArgument(cond, arg, msg...) /*__builtin_expect( ( cond ), true \
                                             )*/
#define DebugCheckArgument( \
    cond, arg, msg...) /*__builtin_expect( ( cond ), true )*/
#endif                 /* CVC4_ASSERTIONS */

}  // namespace CVC4

#endif /* CVC4__CHECK_H */
