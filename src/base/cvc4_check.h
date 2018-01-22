/*********************                                                        */
/*! \file cvc4_check.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Assertion utility classes, functions and macros.
 **
 ** The CHECK utility classes, functions and macros are related to the Assert()
 ** macros defined in base/cvc4_assert.h. The major distinguishing attribute
 ** is the CHECK's abort() the process on failures while Assert() statements
 ** throw C++ exceptions.
 **
 ** The main usage in the file is the CHECK macros. The CHECK macros assert a
 ** condition and aborts()'s the process if the condition is not satisfied. The
 ** macro leaves a hanging ostream for the user to specify additional
 ** information about the failure. Example usage:
 **   CHECK(x >= 0) << "x must be positive.";
 **
 ** DCHECK is a CHECK that is only enabled in debug builds.
 **   DCHECK(pointer != nullptr);
 **
 ** CVC4_FATAL() can be used to indicate unreachable code.
 **
 ** The CHECK and DCHECK macros are not safe for use in signal-handling code.
 ** TODO(taking): Add a signal-handling safe version of CHECK.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CHECK_H
#define __CVC4__CHECK_H

#include <ostream>

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
#else
#define CVC4_PREDICT_FALSE(x) x
#endif
#else
#define CVC4_PREDICT_FALSE(x) x
#endif

namespace CVC4 {

// Implementation notes:
// To understand FatalStream and OStreamVoider, it is useful to understand
// how a CHECK is structured. CHECK(cond) is roughly the following pattern:
//  cond ? (void)0 : OstreamVoider() & FatalStream().stream()
// This is a carefully crafted message to achieve a hanging ostream using
// operator precedence. The line `CHECK(cond) << foo << bar;` will bind as
// follows:
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

// If `cond` is true, log an error message and abort the process.
// Otherwise, does nothing. This leaves a hanging std::ostream& that can be
// inserted into.
#define CVC4_FATAL_IF(cond, function, file, line) \
  CVC4_PREDICT_FALSE(!(cond))                     \
  ? (void)0 : OstreamVoider() & FatalStream(function, file, line).stream()

// If `cond` is false, log an error message and abort()'s the process.
// Otherwise, does nothing. This leaves a hanging std::ostream& that can be
// inserted into using operator<<. Example usages:
//   CHECK(x >= 0);
//   CHECK(x >= 0) << "x must be positive";
//   CHECK(x >= 0) << "expected a positive value. Got " << x << " instead";
#define CHECK(cond)                                               \
  CVC4_FATAL_IF(!(cond), __PRETTY_FUNCTION__, __FILE__, __LINE__) \
      << "Check failure\n\n " << #cond << "\n"

// DCHECK is a variant of CHECK() that is only checked when CVC4_ASSERTIONS is
// defined. We rely on the optimizer to remove the deadcode.
#ifdef CVC4_ASSERTIONS
#define DCHECK(cond) CHECK(cond)
#else
#define DCHECK(cond) \
  CONDITIONAL_FATAL(false, __PRETTY_FUNCTION__, __FILE__, __LINE__)
#endif /* CVC4_DEBUG */

}  // namespace CVC4

#endif /* __CVC4__CHECK_H */
