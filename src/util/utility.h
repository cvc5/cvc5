/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Some standard STL-related utility functions for cvc5.
 */

#include "cvc5_private.h"

#ifndef CVC5__UTILITY_H
#define CVC5__UTILITY_H

#include <algorithm>
#include <fstream>
#include <memory>
#include <optional>
#include <string>

namespace cvc5::internal {

/**
 * Using std::find_if(), finds the first iterator in [first,last)
 * range that satisfies predicate.  If none, return last; otherwise,
 * search for a second one.  If there IS a second one, return last,
 * otherwise return the first (and unique) iterator satisfying pred().
 */
template <class InputIterator, class Predicate>
inline InputIterator find_if_unique(InputIterator first, InputIterator last, Predicate pred) {
  InputIterator match = std::find_if(first, last, pred);
  if(match == last) {
    return last;
  }

  InputIterator match2 = match;
  match2 = std::find_if(++match2, last, pred);
  return (match2 == last) ? match : last;
}

template <typename T>
void container_to_stream(std::ostream& out,
                         const T& container,
                         const char* prefix = "[",
                         const char* postfix = "]",
                         const char* sep = ", ")
{
  out << prefix;
  bool is_first = true;
  for (const auto& item : container)
  {
    out << (!is_first ? sep : "") << item;
    is_first = false;
  }
  out << postfix;
}

/**
 * Generates a string representation of std::optional and inserts it into a
 * stream.
 *
 * @param out The stream
 * @param m The value
 * @return The stream
 */
template <class T>
std::ostream& operator<<(std::ostream& out, const std::optional<T>& m)
{
  out << "{";
  if (m)
  {
    out << "Just ";
    out << *m;
  }
  else
  {
    out << "Nothing";
  }
  out << "}";
  return out;
}

/**
 * Opens a new temporary file with a given filename pattern and returns an
 * fstream to it. The directory that the file is created in is either TMPDIR or
 * /tmp/ if TMPDIR is not set.
 *
 * @param pattern The filename pattern. This string is modified to contain the
 * name of the temporary file.
 *
 * @return A unique pointer to the filestream for the temporary file.
 *
 * Note: We use `std::unique_ptr<std::fstream>` instead of `std::fstream`
 * because GCC < 5 does not support the move constructor of `std::fstream`. See
 * https://gcc.gnu.org/bugzilla/show_bug.cgi?id=54316 for details.
 */
std::unique_ptr<std::fstream> openTmpFile(std::string* pattern);

}  // namespace cvc5::internal

#endif /* CVC5__UTILITY_H */
