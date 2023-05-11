/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
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

#include "smt/print_benchmark.h"

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "printer/printer.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

void PrintBenchmark::printAssertions(std::ostream& out,
                                     const std::vector<Node>& defs,
                                     const std::vector<Node>& assertions)
{
  std::unordered_set<TypeNode> types;
  std::unordered_set<TNode> typeVisited;
  for (const Node& a : defs)
  {
    expr::getTypes(a, types, typeVisited);
  }
  for (const Node& a : assertions)
  {
    Assert(!expr::hasFreeVar(a));
    expr::getTypes(a, types, typeVisited);
  }
  // print the declared types first
  std::unordered_set<TypeNode> alreadyPrintedDeclSorts;
  for (const TypeNode& st : types)
  {
    // note that we must get all "component types" of a type, so that
    // e.g. U is printed as a sort declaration when we have type (Array U Int).
    std::unordered_set<TypeNode> ctypes;
    expr::getComponentTypes(st, ctypes);
    for (const TypeNode& stc : ctypes)
    {
      // get all connected datatypes to this one
      std::vector<TypeNode> connectedTypes;
      getConnectedSubfieldTypes(stc, connectedTypes, alreadyPrintedDeclSorts);
      // now, separate into sorts and datatypes
      std::vector<TypeNode> datatypeBlock;
      for (const TypeNode& ctn : connectedTypes)
      {
        if (ctn.isUninterpretedSort())
        {
          d_printer->toStreamCmdDeclareType(out, ctn);
        }
        else if (ctn.isDatatype())
        {
          datatypeBlock.push_back(ctn);
        }
      }
      // print the mutually recursive datatype block if necessary
      if (!datatypeBlock.empty())
      {
        d_printer->toStreamCmdDatatypeDeclaration(out, datatypeBlock);
      }
    }
  }

  // global visited cache for expr::getSymbols calls
  std::unordered_set<TNode> visited;

  // print the definitions
  std::unordered_map<Node, std::pair<bool, Node>> defMap;
  std::vector<Node> defSyms;
  // first, record all the defined symbols
  for (const Node& a : defs)
  {
    bool isRec;
    Node defSym;
    Node defBody;
    decomposeDefinition(a, isRec, defSym, defBody);
    if (!defSym.isNull())
    {
      Assert(defMap.find(defSym) == defMap.end());
      defMap[defSym] = std::pair<bool, Node>(isRec, defBody);
      defSyms.push_back(defSym);
    }
  }
  // go back and print the definitions
  std::unordered_set<Node> alreadyPrintedDecl;
  std::unordered_set<Node> alreadyPrintedDef;

  std::unordered_map<Node, std::pair<bool, Node>>::const_iterator itd;
  for (const Node& s : defSyms)
  {
    std::vector<Node> recDefs;
    std::vector<Node> ordinaryDefs;
    std::unordered_set<Node> syms;
    getConnectedDefinitions(
        s, recDefs, ordinaryDefs, syms, defMap, alreadyPrintedDef, visited);
    // print the declarations that are encountered for the first time in this
    // block
    printDeclaredFuns(out, syms, alreadyPrintedDecl);
    // print the ordinary definitions
    for (const Node& f : ordinaryDefs)
    {
      itd = defMap.find(f);
      Assert(itd != defMap.end());
      Assert(!itd->second.first);
      d_printer->toStreamCmdDefineFunction(out, f, itd->second.second);
      // a definition is also a declaration
      alreadyPrintedDecl.insert(f);
    }
    // print a recursive function definition block
    if (!recDefs.empty())
    {
      std::vector<Node> lambdas;
      for (const Node& f : recDefs)
      {
        lambdas.push_back(defMap[f].second);
        // a recursive definition is also a declaration
        alreadyPrintedDecl.insert(f);
      }
      d_printer->toStreamCmdDefineFunctionRec(out, recDefs, lambdas);
    }
  }

  // print the remaining declared symbols
  std::unordered_set<Node> syms;
  for (const Node& a : assertions)
  {
    expr::getSymbols(a, syms, visited);
  }
  printDeclaredFuns(out, syms, alreadyPrintedDecl);

  // print the assertions
  for (const Node& a : assertions)
  {
    d_printer->toStreamCmdAssert(out, a);
  }
}
void PrintBenchmark::printAssertions(std::ostream& out,
                                     const std::vector<Node>& assertions)
{
  std::vector<Node> defs;
  printAssertions(out, defs, assertions);
}

void PrintBenchmark::printDeclaredFuns(std::ostream& out,
                                       const std::unordered_set<Node>& funs,
                                       std::unordered_set<Node>& alreadyPrinted)
{
  for (const Node& f : funs)
  {
    Assert(f.isVar());
    // do not print selectors, constructors
    if (!f.getType().isFirstClass())
    {
      continue;
    }
    if (alreadyPrinted.find(f) == alreadyPrinted.end())
    {
      d_printer->toStreamCmdDeclareFunction(out, f);
    }
  }
  alreadyPrinted.insert(funs.begin(), funs.end());
}

void PrintBenchmark::getConnectedSubfieldTypes(
    TypeNode tn,
    std::vector<TypeNode>& connectedTypes,
    std::unordered_set<TypeNode>& processed)
{
  if (processed.find(tn) != processed.end())
  {
    return;
  }
  processed.insert(tn);
  if (tn.isUninterpretedSort())
  {
    connectedTypes.push_back(tn);
  }
  else if (tn.isDatatype())
  {
    connectedTypes.push_back(tn);
    std::unordered_set<TypeNode> subfieldTypes =
        tn.getDType().getSubfieldTypes();
    for (const TypeNode& ctn : subfieldTypes)
    {
      getConnectedSubfieldTypes(ctn, connectedTypes, processed);
    }
  }
}

void PrintBenchmark::getConnectedDefinitions(
    Node n,
    std::vector<Node>& recDefs,
    std::vector<Node>& ordinaryDefs,
    std::unordered_set<Node>& syms,
    const std::unordered_map<Node, std::pair<bool, Node>>& defMap,
    std::unordered_set<Node>& processedDefs,
    std::unordered_set<TNode>& visited)
{
  // does it have a definition?
  std::unordered_map<Node, std::pair<bool, Node>>::const_iterator it =
      defMap.find(n);
  if (it == defMap.end())
  {
    // an ordinary declared symbol
    syms.insert(n);
    return;
  }
  if (processedDefs.find(n) != processedDefs.end())
  {
    return;
  }
  processedDefs.insert(n);
  if (!it->second.first)
  {
    // an ordinary define-fun symbol
    ordinaryDefs.push_back(n);
  }
  else
  {
    // a recursively defined symbol
    recDefs.push_back(n);
  }
  // get the symbols in the body
  std::unordered_set<Node> symsBody;
  expr::getSymbols(it->second.second, symsBody, visited);
  for (const Node& s : symsBody)
  {
    getConnectedDefinitions(
        s, recDefs, ordinaryDefs, syms, defMap, processedDefs, visited);
  }
}

bool PrintBenchmark::decomposeDefinition(Node a,
                                         bool& isRecDef,
                                         Node& sym,
                                         Node& body)
{
  if (a.getKind() == EQUAL && a[0].isVar())
  {
    // an ordinary define-fun
    isRecDef = false;
    sym = a[0];
    body = a[1];
    return true;
  }
  else if (a.getKind() == FORALL && a[1].getKind() == EQUAL
           && a[1][0].getKind() == APPLY_UF)
  {
    isRecDef = true;
    sym = a[1][0].getOperator();
    body = NodeManager::currentNM()->mkNode(LAMBDA, a[0], a[1][1]);
    return true;
  }
  else
  {
    Warning() << "Unhandled definition: " << a << std::endl;
  }
  return false;
}

void PrintBenchmark::printBenchmark(std::ostream& out,
                                    const std::string& logic,
                                    const std::vector<Node>& defs,
                                    const std::vector<Node>& assertions)
{
  d_printer->toStreamCmdSetBenchmarkLogic(out, logic);
  printAssertions(out, defs, assertions);
  d_printer->toStreamCmdCheckSat(out);
}

}  // namespace smt
}  // namespace cvc5::internal
