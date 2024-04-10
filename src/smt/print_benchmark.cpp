/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include "expr/node_converter.h"
#include "printer/printer.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

void PrintBenchmark::printDeclarationsFrom(std::ostream& outDecl,
                                           std::ostream& outDef,
                                           const std::vector<Node>& defs,
                                           const std::vector<Node>& terms)
{
  std::unordered_set<TypeNode> types;
  std::unordered_set<TNode> typeVisited;
  for (const Node& a : defs)
  {
    expr::getTypes(a, types, typeVisited);
  }
  for (const Node& a : terms)
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
    // get all connected datatypes to this one
    std::vector<TypeNode> connectedTypes;
    getConnectedSubfieldTypes(st, connectedTypes, alreadyPrintedDeclSorts);
    // now, separate into sorts and datatypes
    std::vector<TypeNode> datatypeBlock;
    for (const TypeNode& ctn : connectedTypes)
    {
      if ((ctn.isUninterpretedSort() && ctn.getNumChildren() == 0)
          || ctn.isUninterpretedSortConstructor())
      {
        TypeNode ctnp = ctn;
        if (d_converter != nullptr)
        {
          ctnp = d_converter->convertType(ctnp);
        }
        d_printer->toStreamCmdDeclareType(outDecl, ctn);
        outDecl << std::endl;
      }
      else if (ctn.isDatatype() && !ctn.isTuple() && !ctn.isNullable())
      {
        datatypeBlock.push_back(ctn);
      }
    }
    // print the mutually recursive datatype block if necessary
    if (!datatypeBlock.empty())
    {
      d_printer->toStreamCmdDatatypeDeclaration(outDecl, datatypeBlock);
      outDecl << std::endl;
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
    bool isRec = false;
    Node defSym;
    Node defBody;
    if (!decomposeDefinition(a, isRec, defSym, defBody))
    {
      continue;
    }
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
    printDeclaredFuns(outDecl, syms, alreadyPrintedDecl);
    // print the ordinary definitions
    for (const Node& f : ordinaryDefs)
    {
      itd = defMap.find(f);
      Assert(itd != defMap.end());
      Assert(!itd->second.first);
      Node def = itd->second.second;
      if (d_converter != nullptr)
      {
        def = d_converter->convert(def);
      }
      d_printer->toStreamCmdDefineFunction(outDef, f, def);
      outDef << std::endl;
      // a definition is also a declaration
      alreadyPrintedDecl.insert(f);
    }
    // print a recursive function definition block
    if (!recDefs.empty())
    {
      std::vector<Node> lambdas;
      for (const Node& f : recDefs)
      {
        Node lam = defMap[f].second;
        if (d_converter != nullptr)
        {
          lam = d_converter->convert(lam);
        }
        lambdas.push_back(lam);
        // a recursive definition is also a declaration
        alreadyPrintedDecl.insert(f);
      }
      d_printer->toStreamCmdDefineFunctionRec(outDef, recDefs, lambdas);
      outDef << std::endl;
    }
  }

  // print the remaining declared symbols
  std::unordered_set<Node> syms;
  for (const Node& a : terms)
  {
    expr::getSymbols(a, syms, visited);
  }
  printDeclaredFuns(outDecl, syms, alreadyPrintedDecl);
}
void PrintBenchmark::printAssertions(std::ostream& out,
                                     const std::vector<Node>& defs,
                                     const std::vector<Node>& assertions)
{
  printDeclarationsFrom(out, out, defs, assertions);
  // print the assertions
  for (const Node& a : assertions)
  {
    Node ap = a;
    if (d_converter != nullptr)
    {
      ap = d_converter->convert(ap);
    }
    d_printer->toStreamCmdAssert(out, ap);
    out << std::endl;
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
      out << std::endl;
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
  if (tn.isParametricDatatype())
  {
    const DType& dt = tn.getDType();
    // ignore its parameters
    for (size_t i = 0, nparams = dt.getNumParameters(); i < nparams; i++)
    {
      processed.insert(dt.getParameter(i));
    }
    // we do not process the datatype here, instead we will traverse to the
    // head of the parameteric datatype (tn[0]), which will subsequently
    // process its subfield types.
  }
  else
  {
    connectedTypes.push_back(tn);
    if (tn.isDatatype())
    {
      std::unordered_set<TypeNode> subfieldTypes =
          tn.getDType().getSubfieldTypes();
      for (const TypeNode& ctn : subfieldTypes)
      {
        getConnectedSubfieldTypes(ctn, connectedTypes, processed);
      }
    }
  }
  for (unsigned i = 0, nchild = tn.getNumChildren(); i < nchild; i++)
  {
    getConnectedSubfieldTypes(tn[i], connectedTypes, processed);
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
  if (a.getKind() == Kind::EQUAL && a[0].isVar())
  {
    // an ordinary define-fun
    isRecDef = false;
    sym = a[0];
    body = a[1];
    return true;
  }
  else if (a.getKind() == Kind::FORALL && a[1].getKind() == Kind::EQUAL
           && a[1][0].getKind() == Kind::APPLY_UF)
  {
    isRecDef = true;
    sym = a[1][0].getOperator();
    body = NodeManager::currentNM()->mkNode(Kind::LAMBDA, a[0], a[1][1]);
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
  out << std::endl;
  printAssertions(out, defs, assertions);
  d_printer->toStreamCmdCheckSat(out);
  out << std::endl;
}

}  // namespace smt
}  // namespace cvc5::internal
