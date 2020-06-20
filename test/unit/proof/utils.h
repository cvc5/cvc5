/*********************                                                        */
/*! \file utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for proof testing
 **/

#include <algorithm>
#include <string>
#include <cctype>
#include <iterator>

/**
 * Creates a new stream with whitespace removed.
 *
 * @param s the source string
 *
 * @return a string without whitespace
 */
std::string filterWhitespace(const std::string& s)
{
  std::string out;
  std::copy_if(s.cbegin(), s.cend(), std::inserter(out, out.end()), [](char c) {
    return !std::isspace(c);
  });
  return out;
}
