/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Abdalrhman Mohamed, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Quotes a string if necessary for smt2.
 */

#include "util/smt2_quote_string.h"

#include <sstream>
#include <string>

namespace cvc5::internal {

/**
 * SMT-LIB 2 quoting for symbols
 */
std::string quoteSymbol(const std::string& s)
{
  if (s.empty())
  {
    return "||";
  }

  // this is the set of SMT-LIBv2 permitted characters in "simple" (non-quoted)
  // symbols
  if (s.find_first_not_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
                          "0123456789~!@$%^&*_-+=<>.?/")
          == std::string::npos
      && (s[0] < '0' || s[0] > '9'))
  {
    return s;
  }
  std::string tmp = s;
  if (s.front() == '|' && s.back() == '|' && s.length() > 1)
  {
    // if s is already surrounded with vertical bars, we need to check the
    // characters between them
    tmp = s.substr(1, s.length() - 2);
  }

  // must quote the symbol, but it cannot contain | or \, we turn those into _
  size_t p;
  while ((p = tmp.find_first_of("\\|")) != std::string::npos)
  {
    tmp = tmp.replace(p, 1, "_");
  }
  return "|" + tmp + "|";
}

std::string quoteString(const std::string& s)
{
  // escape all double-quotes
  std::string output = s;
  size_t pos = 0;
  while ((pos = output.find('"', pos)) != std::string::npos)
  {
    output.replace(pos, 1, "\"\"");
    pos += 2;
  }
  return '"' + output + '"';
}

}  // namespace cvc5::internal
