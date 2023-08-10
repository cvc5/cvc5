/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The symbol manager.
 */

#include "cvc5_public.h"

#ifndef CVC5__PARSER__API__CPP__SYMBOL_MANAGER_H
#define CVC5__PARSER__API__CPP__SYMBOL_MANAGER_H

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_export.h>

#include <map>
#include <memory>
#include <string>

namespace cvc5 {
namespace parser {

class SymManager;
class Smt2Parser;

/**
 * Symbol manager
 */
class CVC5_EXPORT SymbolManager
{
  friend class Smt2Parser;
 public:
  SymbolManager(cvc5::Solver* s);
  ~SymbolManager();
 private:
  /** The implementation of the symbol manager */
  std::shared_ptr<SymManager> d_sm;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__API__CPP__SYMBOL_MANAGER_H */
