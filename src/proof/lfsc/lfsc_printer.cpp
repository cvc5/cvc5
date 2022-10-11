/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The printer for LFSC proofs
 */

#include "proof/lfsc/lfsc_printer.h"

#include <sstream>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/dtype_selector.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "proof/lfsc/lfsc_list_sc_node_converter.h"
#include "proof/lfsc/lfsc_print_channel.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace proof {

LfscPrinter::LfscPrinter(LfscNodeConverter& ltp)
    : d_tproc(ltp), d_assumpCounter(0)
{
  NodeManager* nm = NodeManager::currentNM();
  d_boolType = nm->booleanType();
  // used for the `flag` type in LFSC
  d_tt = d_tproc.mkInternalSymbol("tt", d_boolType);
  d_ff = d_tproc.mkInternalSymbol("ff", d_boolType);
}

void LfscPrinter::print(std::ostream& out, const ProofNode* pn)
{
  Trace("lfsc-print-debug") << "; ORIGINAL PROOF: " << *pn << std::endl;
  Assert (!pn->getChildren().empty());
  // closing parentheses
  std::stringstream cparen;
  const std::vector<Node>& definitions = pn->getArguments();
  std::unordered_set<Node> definedSymbols;
  for (const Node& n : definitions)
  {
    definedSymbols.insert(n[0]);
    // Note that we don't have to convert it via the term processor (for the
    // sake of inferring declared symbols), since this is already done in the
    // lfsc post processor update method for the outermost SCOPE.
  }
  const std::vector<Node>& assertions = pn->getChildren()[0]->getArguments();
  const ProofNode* pnBody = pn->getChildren()[0]->getChildren()[0].get();

  // clear the rules we have warned about
  d_trustWarned.clear();

  // [1] convert assertions to internal and set up assumption map
  Trace("lfsc-print-debug") << "; print declarations" << std::endl;
  std::vector<Node> iasserts;
  std::map<Node, size_t> passumeMap;
  for (size_t i = 0, nasserts = assertions.size(); i < nasserts; i++)
  {
    Node a = assertions[i];
    iasserts.push_back(d_tproc.convert(a));
    // remember the assumption name
    passumeMap[a] = i;
  }
  d_assumpCounter = assertions.size();

  // [2] compute the proof letification
  Trace("lfsc-print-debug") << "; compute proof letification" << std::endl;
  std::vector<const ProofNode*> pletList;
  std::map<const ProofNode*, size_t> pletMap;
  computeProofLetification(pnBody, pletList, pletMap);

  // [3] compute the global term letification and declared symbols and types
  Trace("lfsc-print-debug")
      << "; compute global term letification and declared symbols" << std::endl;
  LetBinding lbind;
  for (const Node& ia : iasserts)
  {
    lbind.process(ia);
  }
  // We do a "dry-run" of proof printing here, using the LetBinding print
  // channel. This pass traverses the proof but does not print it, but instead
  // updates the let binding data structure for all nodes that appear anywhere
  // in the proof. It is also important for the term processor for collecting
  // symbols and types that are used in the proof.
  LfscPrintChannelPre lpcp(lbind);
  LetBinding emptyLetBind;
  std::map<const ProofNode*, size_t>::iterator itp;
  for (const ProofNode* p : pletList)
  {
    itp = pletMap.find(p);
    Assert(itp != pletMap.end());
    size_t pid = itp->second;
    pletMap.erase(p);
    printProofInternal(&lpcp, p, emptyLetBind, pletMap, passumeMap);
    pletMap[p] = pid;
  }
  // Print the body of the outermost scope
  printProofInternal(&lpcp, pnBody, emptyLetBind, pletMap, passumeMap);

  // [4] print declared sorts and symbols
  // [4a] user declare function symbols
  // Note that this is buffered into an output stream preambleSymDecl and then
  // printed after types. We require printing the declared symbols here so that
  // the set of collected declared types is complete at [4b].
  Trace("lfsc-print-debug") << "; print user symbols" << std::endl;
  std::stringstream preambleSymDecl;
  const std::unordered_set<Node>& syms = d_tproc.getDeclaredSymbols();
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    if (st.isDatatypeConstructor() || st.isDatatypeSelector()
        || st.isDatatypeTester() || st.isDatatypeUpdater()
        || definedSymbols.find(s) != definedSymbols.cend())
    {
      // Constructors, selector, testers, updaters are defined by the datatype.
      // Some definitions depend on declarations and other definitions. So, we
      // print them in order after declarations.
      continue;
    }
    Node si = d_tproc.convert(s);
    preambleSymDecl << "(define " << si << " (var "
                    << d_tproc.getOrAssignIndexForFVar(s) << " ";
    printType(preambleSymDecl, st);
    preambleSymDecl << "))" << std::endl;
  }
  for (const Node& def : definitions)
  {
    Node si = d_tproc.convert(def[0]);
    preambleSymDecl << "(define " << si << ' ';
    print(preambleSymDecl, def[1]);
    preambleSymDecl << ')' << std::endl;
  }
  // [4b] user declared sorts
  Trace("lfsc-print-debug") << "; print user sorts" << std::endl;
  std::stringstream preamble;
  std::unordered_set<TypeNode> sts;
  std::unordered_set<size_t> tupleArity;
  // get the types from the term processor, which has seen all terms occurring
  // in the proof at this point
  // The for loop below may add elements to the set of declared types, so we
  // copy the set to ensure that the for loop iterators do not become outdated.
  const std::unordered_set<TypeNode> types = d_tproc.getDeclaredTypes();
  for (const TypeNode& st : types)
  {
    // note that we must get all "component types" of a type, so that
    // e.g. U is printed as a sort declaration when we have type (Array U Int).
    ensureTypeDefinitionPrinted(preamble, st, sts, tupleArity);
  }
  // print datatype definitions for the above sorts
  for (const TypeNode& stc : sts)
  {
    if (!stc.isDatatype() || stc.getKind() == PARAMETRIC_DATATYPE)
    {
      // skip the instance of a parametric datatype
      continue;
    }
    const DType& dt = stc.getDType();
    preamble << "; DATATYPE " << dt.getName() << std::endl;
    NodeManager* nm = NodeManager::currentNM();
    for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      const DTypeConstructor& cons = dt[i];
      std::string cname = d_tproc.getNameForUserNameOf(cons.getConstructor());
      Node cc = nm->mkRawSymbol(cname, stc);
      // print constructor/tester
      preamble << "(declare " << cc << " term)" << std::endl;
      for (size_t j = 0, nargs = cons.getNumArgs(); j < nargs; j++)
      {
        const DTypeSelector& arg = cons[j];
        // print selector
        std::string sname = d_tproc.getNameForUserNameOf(arg.getSelector());
        Node sc = nm->mkRawSymbol(sname, stc);
        preamble << "(declare " << sc << " term)" << std::endl;
      }
    }
    // testers and updaters are instances of parametric symbols
    // shared selectors are instance of parametric symbol "sel"
    preamble << "; END DATATYPE " << std::endl;
  }
  // [4c] user declared function symbols
  preamble << preambleSymDecl.str();

  // [5] print warnings
  for (PfRule r : d_trustWarned)
  {
    out << "; WARNING: adding trust step for " << r << std::endl;
  }

  // [6] print the DSL rewrite rule declarations
  // TODO cvc5-projects #285.

  // [7] print the check command and term lets
  out << preamble.str();
  out << "(check" << std::endl;
  cparen << ")";
  // print the term let list
  printLetList(out, cparen, lbind);

  Trace("lfsc-print-debug") << "; print asserts" << std::endl;
  // [8] print the assertions, with letification
  // the assumption identifier mapping
  for (size_t i = 0, nasserts = iasserts.size(); i < nasserts; i++)
  {
    Node ia = iasserts[i];
    out << "(# ";
    LfscPrintChannelOut::printAssumeId(out, i);
    out << " (holds ";
    printInternal(out, ia, lbind);
    out << ")" << std::endl;
    cparen << ")";
  }

  Trace("lfsc-print-debug") << "; print annotation" << std::endl;
  // [9] print the annotation
  out << "(: (holds false)" << std::endl;
  cparen << ")";

  Trace("lfsc-print-debug") << "; print proof body" << std::endl;
  // [10] print the proof body
  Assert(pn->getRule() == PfRule::SCOPE);
  // the outermost scope can be ignored (it is the scope of the assertions,
  // which are already printed above).
  LfscPrintChannelOut lout(out);
  printProofLetify(&lout, pnBody, lbind, pletList, pletMap, passumeMap);

  // [11] print closing parantheses
  out << cparen.str() << std::endl;
}

void LfscPrinter::ensureTypeDefinitionPrinted(
    std::ostream& os,
    TypeNode tn,
    std::unordered_set<TypeNode>& processed,
    std::unordered_set<size_t>& tupleArityProcessed)
{
  // note that we must get all "component types" of a type, so that
  // e.g. U is printed as a sort declaration when we have type (Array U Int).
  std::unordered_set<TypeNode> ctypes;
  expr::getComponentTypes(tn, ctypes);

  for (const TypeNode& stc : ctypes)
  {
    printTypeDefinition(os, stc, processed, tupleArityProcessed);
  }
}

void LfscPrinter::printTypeDefinition(
    std::ostream& os,
    TypeNode tn,
    std::unordered_set<TypeNode>& processed,
    std::unordered_set<size_t>& tupleArityProcessed)
{
  if (processed.find(tn) != processed.end())
  {
    return;
  }
  processed.insert(tn);
  // print uninterpreted sorts and uninterpreted sort constructors here
  if (tn.getKind() == SORT_TYPE)
  {
    os << "(declare ";
    printType(os, tn);
    uint64_t arity = 0;
    if (tn.isUninterpretedSortConstructor())
    {
      arity = tn.getUninterpretedSortConstructorArity();
    }
    std::stringstream tcparen;
    for (uint64_t i = 0; i < arity; i++)
    {
      os << " (! s" << i << " sort";
      tcparen << ")";
    }
    os << " sort" << tcparen.str() << ")" << std::endl;
  }
  else if (tn.isDatatype())
  {
    if (tn.getKind() == PARAMETRIC_DATATYPE)
    {
      // skip the instance of a parametric datatype
      return;
    }
    const DType& dt = tn.getDType();
    if (dt.isTuple())
    {
      const DTypeConstructor& cons = dt[0];
      size_t arity = cons.getNumArgs();
      if (tupleArityProcessed.find(arity) == tupleArityProcessed.end())
      {
        tupleArityProcessed.insert(arity);
        os << "(declare Tuple";
        if (arity>0)
        {
          os << "_" << arity;
        }
        os << " ";
        std::stringstream tcparen;
        for (size_t j = 0, nargs = cons.getNumArgs(); j < nargs; j++)
        {
          os << "(! s" << j << " sort ";
          tcparen << ")";
        }
        os << "sort" << tcparen.str() << ")";
      }
      os << std::endl;
    }
    else
    {
      os << "(declare ";
      printType(os, tn);
      std::stringstream cdttparens;
      if (dt.isParametric())
      {
        std::vector<TypeNode> params = dt.getParameters();
        for (const TypeNode& p : params)
        {
          os << " (! " << p << " sort";
          cdttparens << ")";
        }
      }
      os << " sort)" << cdttparens.str() << std::endl;
    }
    // must also ensure the subfield types of the datatype are printed
    std::unordered_set<TypeNode> sftypes = dt.getSubfieldTypes();
    for (const TypeNode& sft : sftypes)
    {
      ensureTypeDefinitionPrinted(os, sft, processed, tupleArityProcessed);
    }
  }
  // all other sorts are builtin into the LFSC signature
}

void LfscPrinter::printProofLetify(
    LfscPrintChannel* out,
    const ProofNode* pn,
    const LetBinding& lbind,
    const std::vector<const ProofNode*>& pletList,
    std::map<const ProofNode*, size_t>& pletMap,
    std::map<Node, size_t>& passumeMap)
{
  // closing parentheses
  size_t cparen = 0;

  // define the let proofs
  if (!pletList.empty())
  {
    std::map<const ProofNode*, size_t>::iterator itp;
    for (const ProofNode* p : pletList)
    {
      itp = pletMap.find(p);
      Assert(itp != pletMap.end());
      size_t pid = itp->second;
      // print (plet _ _
      out->printOpenLfscRule(LfscRule::PLET);
      cparen++;
      out->printHole();
      out->printHole();
      out->printEndLine();
      // print the letified proof
      pletMap.erase(p);
      printProofInternal(out, p, lbind, pletMap, passumeMap);
      pletMap[p] = pid;
      // print the lambda (\ __pX
      out->printOpenLfscRule(LfscRule::LAMBDA);
      cparen++;
      out->printProofId(pid);
      out->printEndLine();
    }
    out->printEndLine();
  }

  // [2] print the proof body
  printProofInternal(out, pn, lbind, pletMap, passumeMap);

  // print the closing parenthesis
  out->printCloseRule(cparen);
}

void LfscPrinter::printProofInternal(
    LfscPrintChannel* out,
    const ProofNode* pn,
    const LetBinding& lbind,
    const std::map<const ProofNode*, size_t>& pletMap,
    std::map<Node, size_t>& passumeMap)
{
  // the stack
  std::vector<PExpr> visit;
  // whether we have to process children
  std::unordered_set<const ProofNode*> processingChildren;
  // helper iterators
  std::unordered_set<const ProofNode*>::iterator pit;
  std::map<const ProofNode*, size_t>::const_iterator pletIt;
  std::map<Node, size_t>::iterator passumeIt;
  Node curn;
  TypeNode curtn;
  const ProofNode* cur;
  visit.push_back(PExpr(pn));
  do
  {
    curn = visit.back().d_node;
    curtn = visit.back().d_typeNode;
    cur = visit.back().d_pnode;
    visit.pop_back();
    // case 1: printing a proof
    if (cur != nullptr)
    {
      PfRule r = cur->getRule();
      // maybe it is letified
      pletIt = pletMap.find(cur);
      if (pletIt != pletMap.end())
      {
        // a letified proof
        out->printProofId(pletIt->second);
        continue;
      }
      pit = processingChildren.find(cur);
      if (pit == processingChildren.end())
      {
        bool isLambda = false;
        if (r == PfRule::LFSC_RULE)
        {
          Assert(!cur->getArguments().empty());
          LfscRule lr = getLfscRule(cur->getArguments()[0]);
          isLambda = (lr == LfscRule::LAMBDA);
        }
        if (r == PfRule::ASSUME)
        {
          // an assumption, must have a name
          passumeIt = passumeMap.find(cur->getResult());
          Assert(passumeIt != passumeMap.end());
          out->printAssumeId(passumeIt->second);
        }
        else if (isLambda)
        {
          Assert(cur->getArguments().size() == 3);
          // lambdas are handled specially. We print in a self contained way
          // here.
          // allocate an assumption, if necessary
          size_t pid;
          Node assumption = cur->getArguments()[2];
          passumeIt = passumeMap.find(assumption);
          if (passumeIt == passumeMap.end())
          {
            pid = d_assumpCounter;
            d_assumpCounter++;
            passumeMap[assumption] = pid;
          }
          else
          {
            pid = passumeIt->second;
          }
          // make the node whose name is the assumption id, where notice that
          // the type of this node does not matter
          std::stringstream pidNodeName;
          LfscPrintChannelOut::printAssumeId(pidNodeName, pid);
          // must be an internal symbol so that it is not turned into (bvar ...)
          Node pidNode =
              d_tproc.mkInternalSymbol(pidNodeName.str(), d_boolType);
          // print "(\ "
          out->printOpenRule(cur);
          // print the identifier
          out->printNode(pidNode);
          // Print the body of the proof with a fresh proof letification. We can
          // keep the assumption map and the let binding (for terms).
          std::vector<const ProofNode*> pletListNested;
          std::map<const ProofNode*, size_t> pletMapNested;
          const ProofNode* curBody = cur->getChildren()[0].get();
          computeProofLetification(curBody, pletListNested, pletMapNested);
          printProofLetify(
              out, curBody, lbind, pletListNested, pletMapNested, passumeMap);
          // print ")"
          out->printCloseRule();
        }
        else
        {
          // assert that we should traverse cur when letifying
          Assert(d_lpltc.shouldTraverse(cur));
          // a normal rule application, compute the proof arguments, which
          // notice in the case of PI also may modify our passumeMap.
          std::vector<PExpr> args;
          if (computeProofArgs(cur, args))
          {
            processingChildren.insert(cur);
            // will revisit this proof node to close parentheses
            visit.push_back(PExpr(cur));
            std::reverse(args.begin(), args.end());
            visit.insert(visit.end(), args.begin(), args.end());
            // print the rule name
            out->printOpenRule(cur);
          }
          else
          {
            // could not print the rule, trust for now
            Node res = d_tproc.convert(cur->getResult());
            res = lbind.convert(res, "__t", true);
            out->printTrust(res, r);
            d_trustWarned.insert(r);
          }
        }
      }
      else
      {
        processingChildren.erase(cur);
        out->printCloseRule();
      }
    }
    // case 2: printing a node
    else if (!curn.isNull())
    {
      // it has already been converted to internal form, we letify it here
      Node curni = lbind.convert(curn, "__t", true);
      out->printNode(curni);
    }
    // case 3: printing a type node
    else if (!curtn.isNull())
    {
      out->printTypeNode(curtn);
    }
    // case 4: a hole
    else
    {
      out->printHole();
    }
  } while (!visit.empty());
}

bool LfscPrinter::computeProofArgs(const ProofNode* pn,
                                   std::vector<PExpr>& pargs)
{
  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
  std::vector<const ProofNode*> cs;
  for (const std::shared_ptr<ProofNode>& c : children)
  {
    cs.push_back(c.get());
  }
  PfRule r = pn->getRule();
  const std::vector<Node>& args = pn->getArguments();
  std::vector<Node> as;
  for (const Node& a : args)
  {
    Node ac = d_tproc.convert(a);
    Assert(!ac.isNull());
    as.push_back(ac);
  }
  // The proof expression stream, which packs the next expressions (proofs,
  // terms, sorts, LFSC datatypes) into a print-expression vector pargs. This
  // stream can be used via "pf << e" which appends an expression to the
  // vector maintained by this stream.
  PExprStream pf(pargs, d_tt, d_ff);
  // hole
  PExpr h;
  Trace("lfsc-print-debug2")
      << "Compute proof args " << r << " #children= " << cs.size()
      << " #args=" << as.size() << std::endl;
  switch (r)
  {
    // SAT
    case PfRule::RESOLUTION:
      pf << h << h << h << cs[0] << cs[1] << args[0].getConst<bool>() << as[1];
      break;
    case PfRule::REORDERING: pf << h << as[0] << cs[0]; break;
    case PfRule::FACTORING: pf << h << h << cs[0]; break;
    // Boolean
    case PfRule::SPLIT: pf << as[0]; break;
    case PfRule::NOT_NOT_ELIM: pf << h << cs[0]; break;
    case PfRule::CONTRA: pf << h << cs[0] << cs[1]; break;
    case PfRule::MODUS_PONENS:
    case PfRule::EQ_RESOLVE: pf << h << h << cs[0] << cs[1]; break;
    case PfRule::NOT_AND: pf << h << h << cs[0]; break;
    case PfRule::NOT_OR_ELIM:
    case PfRule::AND_ELIM: pf << h << h << args[0] << cs[0]; break;
    case PfRule::IMPLIES_ELIM:
    case PfRule::NOT_IMPLIES_ELIM1:
    case PfRule::NOT_IMPLIES_ELIM2:
    case PfRule::EQUIV_ELIM1:
    case PfRule::EQUIV_ELIM2:
    case PfRule::NOT_EQUIV_ELIM1:
    case PfRule::NOT_EQUIV_ELIM2:
    case PfRule::XOR_ELIM1:
    case PfRule::XOR_ELIM2:
    case PfRule::NOT_XOR_ELIM1:
    case PfRule::NOT_XOR_ELIM2: pf << h << h << cs[0]; break;
    case PfRule::ITE_ELIM1:
    case PfRule::ITE_ELIM2:
    case PfRule::NOT_ITE_ELIM1:
    case PfRule::NOT_ITE_ELIM2: pf << h << h << h << cs[0]; break;
    // CNF
    case PfRule::CNF_AND_POS:
    case PfRule::CNF_OR_NEG:
      // print second argument as a raw integer (mpz)
      pf << h << as[0] << args[1];
      break;
    case PfRule::CNF_AND_NEG: pf << h << as[0]; break;
    case PfRule::CNF_OR_POS:
      pf << as[0];
      break;
      break;
    case PfRule::CNF_IMPLIES_POS:
    case PfRule::CNF_IMPLIES_NEG1:
    case PfRule::CNF_IMPLIES_NEG2:
    case PfRule::CNF_EQUIV_POS1:
    case PfRule::CNF_EQUIV_POS2:
    case PfRule::CNF_EQUIV_NEG1:
    case PfRule::CNF_EQUIV_NEG2:
    case PfRule::CNF_XOR_POS1:
    case PfRule::CNF_XOR_POS2:
    case PfRule::CNF_XOR_NEG1:
    case PfRule::CNF_XOR_NEG2: pf << as[0][0] << as[0][1]; break;
    case PfRule::CNF_ITE_POS1:
    case PfRule::CNF_ITE_POS2:
    case PfRule::CNF_ITE_POS3:
    case PfRule::CNF_ITE_NEG1:
    case PfRule::CNF_ITE_NEG2:
    case PfRule::CNF_ITE_NEG3: pf << as[0][0] << as[0][1] << as[0][2]; break;
    // equality
    case PfRule::REFL: pf << as[0]; break;
    case PfRule::SYMM: pf << h << h << cs[0]; break;
    case PfRule::TRANS: pf << h << h << h << cs[0] << cs[1]; break;
    case PfRule::TRUE_INTRO:
    case PfRule::FALSE_INTRO:
    case PfRule::TRUE_ELIM:
    case PfRule::FALSE_ELIM: pf << h << cs[0]; break;
    // arithmetic
    case PfRule::ARITH_MULT_POS:
    case PfRule::ARITH_MULT_NEG:
    {
      pf << h << as[0] << as[1];
    }
    break;
    case PfRule::ARITH_TRICHOTOMY:
    {
      // should be robust to different orderings
      pf << h << h << h << cs[0] << cs[1];
    }
    break;
    case PfRule::INT_TIGHT_UB:
    case PfRule::INT_TIGHT_LB:
    {
      Node res = pn->getResult();
      Assert(res.getNumChildren() == 2);
      Assert(res[1].isConst());
      pf << h << h << d_tproc.convert(res[1]) << cs[0];
    }
    break;
    // strings
    case PfRule::STRING_LENGTH_POS:
      pf << as[0] << d_tproc.convertType(as[0].getType()) << h;
      break;
    case PfRule::STRING_LENGTH_NON_EMPTY: pf << h << h << cs[0]; break;
    case PfRule::RE_INTER: pf << h << h << h << cs[0] << cs[1]; break;
    case PfRule::CONCAT_EQ:
      pf << h << h << h << args[0].getConst<bool>()
         << d_tproc.convertType(children[0]->getResult()[0].getType()) << cs[0];
      break;
    case PfRule::CONCAT_UNIFY:
      pf << h << h << h << h << args[0].getConst<bool>()
         << d_tproc.convertType(children[0]->getResult()[0].getType()) << cs[0]
         << cs[1];
      break;
    case PfRule::CONCAT_CSPLIT:
      pf << h << h << h << h << args[0].getConst<bool>()
         << d_tproc.convertType(children[0]->getResult()[0].getType()) << cs[0]
         << cs[1];
      break;
    case PfRule::CONCAT_CONFLICT:
      pf << h << h << args[0].getConst<bool>()
         << d_tproc.convertType(children[0]->getResult()[0].getType()) << cs[0];
      break;
    case PfRule::RE_UNFOLD_POS:
      if (children[0]->getResult()[1].getKind() != REGEXP_CONCAT)
      {
        return false;
      }
      pf << h << h << h << cs[0];
      break;
    case PfRule::STRING_EAGER_REDUCTION:
    {
      Kind k = as[0].getKind();
      if (k == STRING_TO_CODE || k == STRING_CONTAINS || k == STRING_INDEXOF)
      {
        pf << h << as[0] << as[0][0].getType();
      }
      else
      {
        // not yet defined for other kinds
        return false;
      }
    }
    break;
    case PfRule::STRING_REDUCTION:
    {
      Kind k = as[0].getKind();
      if (k == STRING_SUBSTR || k == STRING_INDEXOF)
      {
        pf << h << as[0] << d_tproc.convertType(as[0][0].getType());
      }
      else
      {
        // not yet defined for other kinds
        return false;
      }
    }
    break;
    // quantifiers
    case PfRule::SKOLEM_INTRO:
    {
      pf << d_tproc.convert(SkolemManager::getUnpurifiedForm(args[0]));
    }
    break;
    // ---------- arguments of non-translated rules go here
    case PfRule::LFSC_RULE:
    {
      LfscRule lr = getLfscRule(args[0]);
      // lambda should be processed elsewhere
      Assert(lr != LfscRule::LAMBDA);
      // Note that `args` has 2 builtin arguments, thus the first real argument
      // begins at index 2
      switch (lr)
      {
        case LfscRule::DEFINITION: pf << as[1][0]; break;
        case LfscRule::SCOPE: pf << h << as[2] << cs[0]; break;
        case LfscRule::NEG_SYMM: pf << h << h << cs[0]; break;
        case LfscRule::CONG: pf << h << h << h << h << cs[0] << cs[1]; break;
        case LfscRule::AND_INTRO1: pf << h << cs[0]; break;
        case LfscRule::NOT_AND_REV: pf << h << h << cs[0]; break;
        case LfscRule::PROCESS_SCOPE: pf << h << h << as[2] << cs[0]; break;
        case LfscRule::AND_INTRO2: pf << h << h << cs[0] << cs[1]; break;
        case LfscRule::ARITH_SUM_UB: pf << h << h << h << cs[0] << cs[1]; break;
        case LfscRule::CONCAT_CONFLICT_DEQ:
          pf << h << h << h << h << as[2].getConst<bool>()
             << d_tproc.convertType(children[0]->getResult()[0].getType())
             << cs[0] << cs[1];
          break;
        default: return false; break;
      }
    }
    break;
    default:
    {
      return false;
      break;
    }
  }
  return true;
}

void LfscPrinter::computeProofLetification(
    const ProofNode* pn,
    std::vector<const ProofNode*>& pletList,
    std::map<const ProofNode*, size_t>& pletMap)
{
  // use callback to specify to stop at LAMBDA
  ProofLetify::computeProofLet(pn, pletList, pletMap, 2, &d_lpltc);
}

void LfscPrinter::print(std::ostream& out, Node n)
{
  Node ni = d_tproc.convert(n);
  printLetify(out, ni);
}

void LfscPrinter::printLetify(std::ostream& out, Node n)
{
  // closing parentheses
  std::stringstream cparen;

  LetBinding lbind;
  lbind.process(n);

  // [1] print the letification
  printLetList(out, cparen, lbind);

  // [2] print the body
  printInternal(out, n, lbind);

  out << cparen.str();
}

void LfscPrinter::printLetList(std::ostream& out,
                               std::ostream& cparen,
                               LetBinding& lbind)
{
  std::vector<Node> letList;
  lbind.letify(letList);
  std::map<Node, size_t>::const_iterator it;
  for (size_t i = 0, nlets = letList.size(); i < nlets; i++)
  {
    Node nl = letList[i];
    out << "(@ ";
    size_t id = lbind.getId(nl);
    Assert(id != 0);
    LfscPrintChannelOut::printId(out, id);
    out << " ";
    // remove, print, insert again
    printInternal(out, nl, lbind, false);
    out << std::endl;
    cparen << ")";
  }
}

void LfscPrinter::printInternal(std::ostream& out, Node n)
{
  LetBinding lbind;
  printInternal(out, n, lbind);
}
void LfscPrinter::printInternal(std::ostream& out,
                                Node n,
                                LetBinding& lbind,
                                bool letTop)
{
  Node nc = lbind.convert(n, "__t", letTop);
  LfscPrintChannelOut::printNodeInternal(out, nc);
}

void LfscPrinter::printType(std::ostream& out, TypeNode tn)
{
  TypeNode tni = d_tproc.convertType(tn);
  LfscPrintChannelOut::printTypeNodeInternal(out, tni);
}

}  // namespace proof
}  // namespace cvc5::internal
