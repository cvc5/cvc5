/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Print benchmark utility.
 */

#include "smt/print_benchmark.h"

#include "expr/attribute.h"
#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/node_converter.h"
#include "printer/printer.h"
#include "expr/skolem_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

/**
 * Attribute true for symbols that should be excluded from the output of this
 * utility.
 */
struct BenchmarkNoPrintAttributeId
{
};
using BenchmarkNoPrintAttribute =
    expr::Attribute<BenchmarkNoPrintAttributeId, bool>;

void PrintBenchmark::printDeclarationsFrom(std::ostream& outDecl,
                                           std::ostream& outDef,
                                           const std::vector<Node>& defs,
                                           const std::vector<Node>& terms)
{
  std::unordered_set<TypeNode> unorderedTypes;
  std::unordered_set<TNode> typeVisited;
  for (const Node& a : defs)
  {
    expr::getTypes(a, unorderedTypes, typeVisited);
  }
  for (const Node& a : terms)
  {
    expr::getTypes(a, unorderedTypes, typeVisited);
  }
  std::vector<TypeNode> types{unorderedTypes.begin(), unorderedTypes.end()};
  if (d_sorted)
  {
    // We want to print declarations in a deterministic order, independent of
    // the implementation of data structures. Hence, we insert into a vector
    // and reorder. Note that collecting the types in an std::unordered_map,
    // then inserting them into a vector and sorting the vector is faster than
    // immediately using an std::set instead.
    std::sort(types.begin(), types.end());
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
    std::unordered_set<Node> unorderedSyms;
    getConnectedDefinitions(s,
                            recDefs,
                            ordinaryDefs,
                            unorderedSyms,
                            defMap,
                            alreadyPrintedDef,
                            visited);
    std::vector<Node> syms{unorderedSyms.begin(), unorderedSyms.end()};
    if (d_sorted)
    {
      // We want to print declarations in a deterministic order, independent of
      // the implementation of data structures. Hence, we insert into a vector
      // and reorder. Note that collecting `syms` in an std::unordered_map,
      // then inserting them into a vector and sorting the vector is faster than
      // immediately using an std::set instead.
      std::sort(syms.begin(), syms.end());
    }
    // print the declarations that are encountered for the first time in this
    // block
    printDeclaredFuns(outDecl, syms, alreadyPrintedDecl);
    if (d_sorted)
    {
      // Sort recursive definitions for deterministic order.
      std::sort(recDefs.begin(), recDefs.end());
      // In general, we cannot sort the ordinary definitions since they were
      // added to the vector in an order which ensures the functions they
      // depend on are defined first.
    }
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
  std::unordered_set<Node> unorderedSyms;
  for (const Node& a : terms)
  {
    expr::getSymbols(a, unorderedSyms, visited);
  }
  std::vector<Node> syms{unorderedSyms.begin(), unorderedSyms.end()};
  if (d_sorted)
  {
    // We want to print declarations in a deterministic order, independent of
    // the implementation of data structures. Hence, we insert into a vector
    // and reorder. Note that collecting `syms` in an std::unordered_map,
    // then inserting them into a vector and sorting the vector is faster than
    // immediately using an std::set instead.
    std::sort(syms.begin(), syms.end());
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
                                       const std::vector<Node>& funs,
                                       std::unordered_set<Node>& alreadyPrinted)
{
  bool printSkolemDefs = options::ioutils::getPrintSkolemDefinitions(out);
  SkolemManager* sm = d_nm->getSkolemManager();
  BenchmarkNoPrintAttribute bnpa;
  for (const Node& f : funs)
  {
    Assert(f.isVar());
    // do not print selectors, constructors, testers, updaters
    TypeNode ft = f.getType();
    if (ft.isDatatypeSelector() || ft.isDatatypeConstructor()
        || ft.isDatatypeTester() || ft.isDatatypeUpdater())
    {
      continue;
    }
    // don't print symbols that have been marked
    if (f.getAttribute(bnpa))
    {
      continue;
    }
    // if print skolem definitions is true, we shouldn't print declarations for
    // (exported) skolems, as they are printed as parsable terms.
    if (printSkolemDefs && f.getKind() == Kind::SKOLEM)
    {
      if (sm->getId(f)!= SkolemId::INTERNAL)
      {
        continue;
      }
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
  // get the symbols in the body
  std::unordered_set<Node> symsBody;
  expr::getSymbols(it->second.second, symsBody, visited);
  for (const Node& s : symsBody)
  {
    getConnectedDefinitions(
        s, recDefs, ordinaryDefs, syms, defMap, processedDefs, visited);
  }
  // add the symbol after we add the definitions
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
    body = NodeManager::mkNode(Kind::LAMBDA, a[0], a[1][1]);
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

void PrintBenchmark::markNoPrint(Node& sym)
{
  BenchmarkNoPrintAttribute bnpa;
  sym.setAttribute(bnpa, true);
}

}  // namespace smt
}  // namespace cvc5::internal
