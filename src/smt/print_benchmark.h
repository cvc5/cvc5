/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {

class Printer;

namespace smt {

/**
 * A utility for printing a benchmark. This utility requires no bookkeeping
 * about which commands have been executed. It reconstructs the set of
 * commands that would have been required for generating a benchmark based on
 * a list of nodes.
 */
class PrintBenchmark
{
 public:
  PrintBenchmark(const Printer* p) : d_printer(p) {}
  /**
   * Print assertions. This prints a parsable set of commands on the output
   * stream out that defines (recursive) functions in defs, and asserts
   * assertions. It does not print a set-logic or check-sat command.
   *
   * Each node in defs is either of the form:
   * (1) (= s t), where s is a (non-recursively) defined function, where
   * the term t may be a lambda if s has non-zero arity.
   * (2) (forall V (= (s V) t)), where s is a recursively defined function.
   */
  void printAssertions(std::ostream& out,
                       const std::vector<Node>& defs,
                       const std::vector<Node>& assertions);
  /**
   * Print assertions, without special handling of defined functions.
   */
  void printAssertions(std::ostream& out, const std::vector<Node>& assertions);

  /**
   * Print benchmark, which prints a parsable benchmark on the output stream
   * out. It relies on the printAssertions method above, as well as printing
   * the logic based on given string and a final check-sat command.
   *
   * For the best printing, defs should be given in the order in which
   * the symbols were declared. If this is not the case, then we may e.g.
   * group blocks of definitions that were not grouped in the input.
   */
  void printBenchmark(std::ostream& out,
                      const std::string& logic,
                      const std::vector<Node>& defs,
                      const std::vector<Node>& assertions);

 private:
  /**
   * print declared symbols in funs but not processed; updates processed to
   * include what was printed
   */
  void printDeclaredFuns(std::ostream& out,
                         const std::unordered_set<Node>& funs,
                         std::unordered_set<Node>& processed);
  /**
   * Get the connected types. This traverses subfield types of datatypes and
   * adds to connectedTypes everything that is necessary for printing tn.
   *
   * @param tn The type to traverse
   * @param connectedTypes The types that tn depends on
   * @param process The types we have already processed. We update this set
   * with those added to connectedTypes.
   */
  void getConnectedSubfieldTypes(TypeNode tn,
                                 std::vector<TypeNode>& connectedTypes,
                                 std::unordered_set<TypeNode>& processed);
  /**
   * Get connected definitions for symbol v.
   *
   * @param recDefs The recursive function definitions that v depends on
   * @param ordinaryDefs The non-recursive definitions that v depends on
   * @param syms The declared symbols that v depends on
   * @param defMap Map from symbols to their definitions
   * @param processedDefs The (recursive or non-recursive) definitions we have
   * processed already. We update this with symbols we add to recDefs and
   * ordinaryDefs.
   * @param visited The set of terms we have already visited when searching for
   * free symbols. This set is updated for the bodies of definitions processed
   * in this call.
   */
  void getConnectedDefinitions(
      Node v,
      std::vector<Node>& recDefs,
      std::vector<Node>& ordinaryDefs,
      std::unordered_set<Node>& syms,
      const std::unordered_map<Node, std::pair<bool, Node>>& defMap,
      std::unordered_set<Node>& processedDefs,
      std::unordered_set<TNode>& visited);
  /**
   * Decompose definition assertion a.
   *
   * @param a The definition assertion
   * @param isRecDef Updated to true if a is a recursive function definition (a
   * quantified formula)
   * @param sym Updated to the symbol that a defines
   * @param body Update to the term that defines sym
   * @return true if the definition was successfully inferred
   */
  bool decomposeDefinition(Node a, bool& isRecDef, Node& sym, Node& body);
  /**
   * Pointer to the printer we are using, which is responsible for printing
   * individual commands.
   */
  const Printer* d_printer;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__PRINT_BENCHMARK_H */
