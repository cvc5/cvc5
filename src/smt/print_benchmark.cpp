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

#include "smt/print_benchmark.h"

#include "expr/node_algorithm.h"
#include "printer/printer.h"

namespace cvc5 {
namespace smt {

void PrintBenchmark::printBenchmark(std::ostream& out, const std::vector<Node>& assertions)
{
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;
  std::unordered_set<TypeNode> types;
  std::unordered_set<TNode> typeVisited;
  for (const Node& a : assertions)
  {
    expr::getSymbols(a, syms, visited);
    expr::getTypes(a, types, typeVisited);
  }
  // print the declared types
  for (const TypeNode& st : types)
  {
    // note that we must get all "component types" of a type, so that
    // e.g. U is printed as a sort declaration when we have type (Array U Int).
    std::unordered_set<TypeNode> ctypes;
    expr::getComponentTypes(st, ctypes);
    for (const TypeNode& stc : ctypes)
    {
      if (sts.find(stc) != sts.end())
      {
        continue;
      }
      sts.insert(stc);
      if (stc.isSort())
      {
        d_printer->toStreamCmdDeclareType(out, stc);
      }
      else if (stc.isDatatype())
      {
        // get all connected datatypes to this one TODO
        std::vector<TypeNode> dts;
        dts.push_back(stc);
        d_printer->toStreamCmdDatatypeDeclaration(out, dts);
      }
    }
  }
}

}  // namespace smt
}  // namespace cvc5
