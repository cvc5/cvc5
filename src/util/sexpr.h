/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simple stateless conversion to s-expressions.
 *
 * This file contains a collection of conversion routines from various data to
 * s-expressions as strings. The actual conversion is provided by methods of
 * the following form, where T is some type:
 *
 *   toSExpr(std::ostream& out, const T& t)
 *
 * A fallback is provided where T is a template type that forwards to the
 * generic streaming operator `operator<<()` for T.
 * To make usage easier, `std::string toSExpr(const T&)` is provided as well.
 * For containers, an overload that accepts two iterators is available.
 */

#include "cvc5_private.h"

#ifndef CVC5__SEXPR_H
#define CVC5__SEXPR_H

#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace cvc5::internal {

// Forward declarations
struct StatisticBaseValue;

// Non-templated overloads that live in the source file
void toSExpr(std::ostream& out, const std::string& s);
void toSExpr(std::ostream& out, const std::unique_ptr<StatisticBaseValue>& sbv);

/**
 * Fallback overload for basic types.
 *
 * Prints Boolean values as `true` and `false`, integral numbers as numbers and
 * all other types using their respective streaming operators, enclosed with
 * double quotes.
 */
template <typename T>
void toSExpr(std::ostream& out, const T& t)
{
  if constexpr (std::is_same_v<T, bool>)
  {
    out << (t ? "true" : "false");
  }
  if constexpr (std::is_integral_v<T>)
  {
    out << t;
  }
  else
  {
    out << "\"" << t << "\"";
  }
}

// Forward declarations of templated overloads
template <typename T>
void toSExpr(std::ostream& out, const std::vector<T>& v);

/**
 * Render an `std::pair` to an s-expression string.
 */
template <typename T1, typename T2>
void toSExpr(std::ostream& out, const std::pair<T1, T2>& p)
{
  out << "(";
  toSExpr(out, p.first);
  out << " ";
  toSExpr(out, p.second);
  out << ")";
}

/**
 * Render an arbitrary iterator range to an s-expression string.
 */
template <typename Iterator>
void toSExpr(std::ostream& out, Iterator begin, Iterator end)
{
  out << "(";
  for (auto it = begin; it != end; ++it)
  {
    if (it != begin)
    {
      out << " ";
    }
    toSExpr(out, *it);
  }
  out << ")";
}

/**
 * Render a vector to an s-expression string.
 * Convenience wrapper for `std::vector` around the overload using iterators.
 */
template <typename T>
void toSExpr(std::ostream& out, const std::vector<T>& v)
{
  toSExpr(out, v.begin(), v.end());
}

/**
 * Convert arbitrary data to an s-expression string.
 */
template <typename T>
std::string toSExpr(const T& t)
{
  std::stringstream ss;
  toSExpr(ss, t);
  return ss.str();
}

/**
 * Convert an arbitrary iterator range to an s-expression string.
 */
template <typename Iterator>
std::string toSExpr(Iterator begin, Iterator end)
{
  std::stringstream ss;
  toSExpr(ss, begin, end);
  return ss.str();
}

}  // namespace cvc5::internal

#endif /* CVC5__SEXPR_H */
