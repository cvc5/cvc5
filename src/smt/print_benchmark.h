/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Print benchmark utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PRINT_BENCHMARK_H
#define CVC5__SMT__PRINT_BENCHMARK_H

#include <iosfwd>
#include <vector>

#include "expr/node.h"

namespace cvc5 {
  
class Printer;

namespace smt {

/**
 * A utility for printing a benchmark.
 */
class PrintBenchmark {
 public:
  PrintBenchmark(Printer * p ) : d_printer(p) {}
  /**
   * Print assertions, without special handling of defined functions.
   */
  void printAssertions(std::ostream& out, const std::vector<Node>& assertions);
private:
  /** 
   * Pointer to the printer we are using, which is responsible for printing
   * individual commands.
   */
  Printer * d_printer;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__PRINT_BENCHMARK_H */
