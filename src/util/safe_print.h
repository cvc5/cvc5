/*********************                                                        */
/*! \file safe_print.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Print functions that are safe to use in a signal handler.
 **
 ** Signal handlers only allow a very limited set of operations, e.g. dynamic
 ** memory allocation is not possible. This set of functions can be used to
 ** print information from a signal handler.
 **
 ** The safe_print function takes a template parameter T and prints an argument
 ** of type const T& to avoid copying, e.g. when printing std::strings. For
 ** consistency, we also pass primitive types by reference (otherwise, functions
 ** in statistics_registry.h would require specialization or we would have to
 ** use function overloading).
 **
 ** If there exists a function `toString(obj)` for a given object, it will be
 ** used automatically. This is useful for printing enum values for example.
 ** IMPORTANT: The `toString(obj)` function *must not* perform any allocations
 ** or call other functions that are not async-signal-safe.
 **
 ** This header is a "cvc4_private_library.h" header because it is private but
 ** the safe_print functions are used in the driver. See also the description
 ** of "statistics_registry.h" for more information on
 ** "cvc4_private_library.h".
 **/

#include "cvc4_private_library.h"

#ifndef CVC4__SAFE_PRINT_H
#define CVC4__SAFE_PRINT_H

#if __cplusplus >= 201103L
// For c++11 and newer
#include <cstdint>
#else
#include <stdint.h>
#endif

#include <unistd.h>

#include <cstring>
#include <type_traits>

#include "lib/clock_gettime.h"
#include "util/result.h"

namespace CVC4 {

/**
 * Prints arrays of chars (e.g. string literals) of length N. Safe to use in a
 * signal handler.
 */
template <size_t N>
void CVC4_PUBLIC safe_print(int fd, const char (&msg)[N]) {
  ssize_t nb = N - 1;
  if (write(fd, msg, nb) != nb) {
    abort();
  }
}

/**
 * The default method for converting an object to a string for safe printing.
 * This method simply returns "<unsupported>". The `long` argument is used to
 * indicate that we do not prefer this method over the version that calls
 * `toString()`.
 */
template <typename T>
const char* toStringImpl(const T& obj, long)
{
  return "<unsupported>";
}

/**
 * Returns the result of calling `toString(obj)`. This method is only defined
 * if such an overload of `toString()` exists. To detect the existence of such
 * a method, we use SFINAE and a trailing return type. The trailing return type
 * is necessary because it allows us to refer to `obj`. The `int` argument is
 * used to prefer this version of the function instead of the one that prints
 * "<unsupported>".
 */
template <typename T>
auto toStringImpl(const T& obj, int) -> decltype(toString(obj))
{
  return toString(obj);
}

/**
 * Prints a variable of type T. Safe to use in a signal handler. The default
 * implementation either prints "<unsupported>" or the result of calling
 * `toString(obj)` if such a method exists (this is useful for printing enum
 * values for example without implementing a template specialization here).
 *
 * @param fd The file descriptor to print to
 * @param obj The object to print
 */
template <typename T>
void CVC4_PUBLIC safe_print(int fd, const T& obj)
{
  const char* s =
      toStringImpl(obj, /* prefer the method that uses `toString()` */ 0);
  ssize_t slen = static_cast<ssize_t>(strlen(s));
  if (write(fd, s, slen) != slen)
  {
    abort();
  }
}

template <>
void CVC4_PUBLIC safe_print(int fd, const std::string& msg);
template <>
void CVC4_PUBLIC safe_print(int fd, const int64_t& _i);
template <>
void CVC4_PUBLIC safe_print(int fd, const int32_t& i);
template <>
void CVC4_PUBLIC safe_print(int fd, const uint64_t& _i);
template <>
void CVC4_PUBLIC safe_print(int fd, const uint32_t& i);
template <>
void CVC4_PUBLIC safe_print(int fd, const double& _d);
template <>
void CVC4_PUBLIC safe_print(int fd, const float& f);
template <>
void CVC4_PUBLIC safe_print(int fd, const bool& b);
template <>
void CVC4_PUBLIC safe_print(int fd, void* const& addr);
template <>
void CVC4_PUBLIC safe_print(int fd, const timespec& t);

/** Prints an integer in hexadecimal. Safe to use in a signal handler. */
void safe_print_hex(int fd, uint64_t i);

/**
 * Prints a right aligned number. Fills up remaining space with zeros. Safe to
 * use in a signal handler.
 */
void safe_print_right_aligned(int fd, uint64_t i, ssize_t width);

} /* CVC4 namespace */

#endif /* CVC4__SAFE_PRINT_H */
