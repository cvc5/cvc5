/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Syntax of the string representation of an Integer.
 */

#include "util/integer_parse.h"

namespace cvc5::internal {

namespace {

/** Determine whether c is a digit with a value below base. */
bool isDigitInBase(char c, unsigned base)
{
  unsigned value;
  if (c >= '0' && c <= '9')
  {
    value = static_cast<unsigned>(c - '0');
  }
  else if (c >= 'a' && c <= 'z')
  {
    value = static_cast<unsigned>(c - 'a') + 10;
  }
  else if (c >= 'A' && c <= 'Z')
  {
    value = static_cast<unsigned>(c - 'A') + 10;
  }
  else
  {
    return false;
  }
  return value < base;
}

}  // namespace

bool isValidIntegerLiteral(const std::string& s, unsigned base)
{
  size_t i = (!s.empty() && s[0] == '-') ? 1 : 0;
  if (i == s.size())
  {
    // no magnitude at all, i.e. "" or "-"
    return false;
  }
  unsigned digitBase = base;
  // Whether the digit sequence may be empty, which is the case only for the
  // inferred octal base, where the leading '0' is itself the value.
  bool allowEmpty = false;
  if (base == 0)
  {
    if (s[i] != '0')
    {
      digitBase = 10;
    }
    else if (i + 1 < s.size() && (s[i + 1] == 'x' || s[i + 1] == 'X'))
    {
      digitBase = 16;
      i += 2;
    }
    else if (i + 1 < s.size() && (s[i + 1] == 'b' || s[i + 1] == 'B'))
    {
      digitBase = 2;
      i += 2;
    }
    else
    {
      digitBase = 8;
      i += 1;
      allowEmpty = true;
    }
  }
  if (i == s.size())
  {
    return allowEmpty;
  }
  for (; i < s.size(); ++i)
  {
    if (!isDigitInBase(s[i], digitBase))
    {
      return false;
    }
  }
  return true;
}

}  // namespace cvc5::internal
