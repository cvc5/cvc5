/*********************                                                        */
/*! \file utility.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andres Noetzli, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Some standard STL-related utility functions for CVC4
 **
 ** Some standard STL-related utility functions for CVC4.
 **/

#include "cvc4_private.h"

#ifndef CVC4__UTILITY_H
#define CVC4__UTILITY_H

#include <algorithm>
#include <fstream>
#include <functional>
#include <memory>
#include <string>
#include <utility>

namespace CVC4 {


/**
 * Like std::equal_to<>, but tests equality between the first element
 * of a pair and an element.
 */
template <class T, class U>
struct first_equal_to : std::binary_function<std::pair<T, U>, T, bool> {
  bool operator()(const std::pair<T, U>& pr, const T& x) const {
    return pr.first == x;
  }
};/* struct first_equal_to<T> */


/**
 * Like std::equal_to<>, but tests equality between the second element
 * of a pair and an element.
 */
template <class T, class U>
struct second_equal_to : std::binary_function<std::pair<T, U>, U, bool> {
  bool operator()(const std::pair<T, U>& pr, const U& x) const {
    return pr.second == x;
  }
};/* struct first_equal_to<T> */


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

}/* CVC4 namespace */

#endif /* CVC4__UTILITY_H */
