/*********************                                                        */
/*! \file smt2_quote_string.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andres Noetzli, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Quotes a string if necessary for smt2.
 **
 ** Quotes a string if necessary for smt2.
 **/

#include "util/smt2_quote_string.h"

#include <sstream>
#include <string>

namespace CVC4 {

/**
 * SMT-LIB 2 quoting for symbols
 */
std::string quoteSymbol(const std::string& s){
  // this is the set of SMT-LIBv2 permitted characters in "simple" (non-quoted)
  // symbols
  if (s.find_first_not_of("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
                          "0123456789~!@$%^&*_-+=<>.?/")
          != std::string::npos
      || s.empty() || (s[0] >= '0' && s[0] <= '9'))
  {
    std::string tmp(s);
    // must quote the symbol, but it cannot contain | or \, we turn those into _
    size_t p;
    while((p = tmp.find_first_of("\\|")) != std::string::npos) {
      tmp = tmp.replace(p, 1, "_");
    }
    return "|" + tmp + "|";
  }
  return s;
}

}/* CVC4 namespace */
