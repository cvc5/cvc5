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

using namespace cvc5::kind;
using namespace cvc5::rewriter;

namespace cvc5 {
namespace proof {

LfscPrinter::LfscPrinter(LfscNodeConverter& ltp, rewriter::RewriteDb* rdb)
    : d_tproc(ltp), d_assumpCounter(0), d_rdb(rdb)
{
  NodeManager* nm = NodeManager::currentNM();
  d_boolType = nm->booleanType();
  // used for the `flag` type in LFSC
  d_tt = d_tproc.mkInternalSymbol("tt", d_boolType);
  d_ff = d_tproc.mkInternalSymbol("ff", d_boolType);
}

void LfscPrinter::print(std::ostream& out,
                        const std::vector<Node>& assertions,
                        const ProofNode* pn)
{
  Trace("lfsc-print-debug") << "; ORIGINAL PROOF: " << *pn << std::endl;
  Assert (!pn->getChildren().empty());
  // closing parentheses
  std::stringstream cparen;
  const ProofNode* pnBody = pn->getChildren()[0].get();

  // clear the rules we have warned about
  d_trustWarned.clear();

  Trace("lfsc-print-debug") << "; print declarations" << std::endl;
  // [1] compute and print the declarations
  std::unordered_set<Node> syms;
  std::unordered_set<TNode> visited;
  std::vector<Node> iasserts;
  std::map<Node, size_t> passumeMap;
  std::unordered_set<TypeNode> types;
  std::unordered_set<TNode> typeVisited;
  for (size_t i = 0, nasserts = assertions.size(); i < nasserts; i++)
  {
    Node a = assertions[i];
    expr::getSymbols(a, syms, visited);
    expr::getTypes(a, types, typeVisited);
    iasserts.push_back(d_tproc.convert(a));
    // remember the assumption name
    passumeMap[a] = i;
  }
  d_assumpCounter = assertions.size();
  Trace("lfsc-print-debug") << "; print sorts" << std::endl;
  // [1a] user declared sorts
  std::stringstream preamble;
  std::unordered_set<TypeNode> sts;
  std::unordered_set<size_t> tupleArity;
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
        preamble << "(declare ";
        printType(preamble, stc);
        preamble << " sort)" << std::endl;
      }
      else if (stc.isDatatype())
      {
        const DType& dt = stc.getDType();
        if (stc.getKind() == PARAMETRIC_DATATYPE)
        {
          // skip the instance of a parametric datatype
          continue;
        }
        preamble << "; DATATYPE " << dt.getName() << std::endl;
        if (dt.isTuple())
        {
          const DTypeConstructor& cons = dt[0];
          size_t arity = cons.getNumArgs();
          if (tupleArity.find(arity) == tupleArity.end())
          {
            tupleArity.insert(arity);
            preamble << "(declare Tuple_" << arity << " ";
            std::stringstream tcparen;
            for (size_t j = 0, nargs = cons.getNumArgs(); j < nargs; j++)
            {
              preamble << "(! s" << j << " sort ";
              tcparen << ")";
            }
            preamble << "sort" << tcparen.str() << ")";
          }
          preamble << std::endl;
        }
        else
        {
          preamble << "(declare ";
          printType(preamble, stc);
          std::stringstream cdttparens;
          if (dt.isParametric())
          {
            std::vector<TypeNode> params = dt.getParameters();
            for (const TypeNode& tn : params)
            {
              preamble << " (! " << tn << " sort";
              cdttparens << ")";
            }
          }
          preamble << " sort)" << cdttparens.str() << std::endl;
        }
        for (size_t i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
        {
          const DTypeConstructor& cons = dt[i];
          std::stringstream sscons;
          sscons << d_tproc.convert(cons.getConstructor());
          std::string cname =
              LfscNodeConverter::getNameForUserName(sscons.str());
          // print construct/tester
          preamble << "(declare " << cname << " term)" << std::endl;
          for (size_t j = 0, nargs = cons.getNumArgs(); j < nargs; j++)
          {
            const DTypeSelector& arg = cons[j];
            // print selector
            Node si = d_tproc.convert(arg.getSelector());
            std::stringstream sns;
            sns << si;
            std::string sname =
                LfscNodeConverter::getNameForUserName(sns.str());
            preamble << "(declare " << sname << " term)" << std::endl;
          }
        }
        // testers and updaters are instances of parametric symbols
        // shared selectors are instance of parametric symbol "sel"
        preamble << "; END DATATYPE " << std::endl;
      }
      // all other sorts are builtin into the LFSC signature
    }
  }
  Trace("lfsc-print-debug") << "; print user symbols" << std::endl;
  // [1b] user declare function symbols
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    if (st.isConstructor() || st.isSelector() || st.isTester()
        || st.isUpdater())
    {
      // constructors, selector, testers, updaters are defined by the datatype
      continue;
    }
    Node si = d_tproc.convert(s);
    preamble << "(define " << si << " (var "
             << d_tproc.getOrAssignIndexForVar(s) << " ";
    printType(preamble, st);
    preamble << "))" << std::endl;
  }

  Trace("lfsc-print-debug") << "; compute proof letification" << std::endl;
  // [2] compute the proof letification
  std::vector<const ProofNode*> pletList;
  std::map<const ProofNode*, size_t> pletMap;
  computeProofLetification(pnBody, pletList, pletMap);

  Trace("lfsc-print-debug") << "; compute term lets" << std::endl;
  // compute the term lets
  LetBinding lbind;
  for (const Node& ia : iasserts)
  {
    lbind.process(ia);
  }
  // We do a "dry-run" of proof printing here, using the LetBinding print
  // channel. This pass traverses the proof but does not print it, but instead
  // updates the let binding data structure for all nodes that appear anywhere
  // in the proof.
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

  // [3] print warnings
  for (PfRule r : d_trustWarned)
  {
    out << "; WARNING: adding trust step for " << r << std::endl;
  }

  // [4] print the DSL rewrite rule declarations
  const std::unordered_set<DslPfRule>& dslrs = lpcp.getDslRewrites();
  for (DslPfRule dslr : dslrs)
  {
    // also computes the format for the rule
    printDslRule(out, dslr, d_dslFormat[dslr]);
  }

  // [5] print the check command and term lets
  out << preamble.str();
  out << "(check" << std::endl;
  cparen << ")";
  // print the term let list
  printLetList(out, cparen, lbind);

  Trace("lfsc-print-debug") << "; print asserts" << std::endl;
  // [6] print the assertions, with letification
  // the assumption identifier mapping
  for (size_t i = 0, nasserts = iasserts.size(); i < nasserts; i++)
  {
    Node ia = iasserts[i];
    out << "(% ";
    LfscPrintChannelOut::printAssumeId(out, i);
    out << " (holds ";
    printInternal(out, ia, lbind);
    out << ")" << std::endl;
    cparen << ")";
  }

  Trace("lfsc-print-debug") << "; print annotation" << std::endl;
  // [7] print the annotation
  out << "(: (holds false)" << std::endl;
  cparen << ")";

  Trace("lfsc-print-debug") << "; print proof body" << std::endl;
  // [8] print the proof body
  Assert(pn->getRule() == PfRule::SCOPE);
  // the outermost scope can be ignored (it is the scope of the assertions,
  // which are already printed above).
  LfscPrintChannelOut lout(out);
  printProofLetify(&lout, pnBody, lbind, pletList, pletMap, passumeMap);

  out << cparen.str() << std::endl;
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
      // debugging
      /*
      if (Trace.isOn("lfsc-print-debug"))
      {
        out << "; proves " << p->getResult();
      }
      */
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
        else if (r == PfRule::ENCODE_PRED_TRANSFORM)
        {
          // just add child
          visit.push_back(PExpr(cur->getChildren()[0].get()));
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
            if (d_trustWarned.find(r) == d_trustWarned.end())
            {
              d_trustWarned.insert(r);
            }
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
    // strings
    case PfRule::STRING_LENGTH_POS: pf << as[0]; break;
    case PfRule::STRING_LENGTH_NON_EMPTY: pf << h << cs[0]; break;
    case PfRule::RE_INTER: pf << h << h << h << cs[0] << cs[1]; break;
    case PfRule::CONCAT_EQ:
      pf << h << h << h << args[0].getConst<bool>() << cs[0];
      break;
    case PfRule::CONCAT_UNIFY:
      pf << h << h << h << h << args[0].getConst<bool>() << cs[0] << cs[1];
      break;
    case PfRule::CONCAT_CSPLIT:
      pf << h << h << h << h << args[0].getConst<bool>() << cs[0] << cs[1];
      break;
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
        pf << h << as[0] << as[0][0].getType();
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
      pf << h << d_tproc.convert(SkolemManager::getOriginalForm(args[0]));
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
        case LfscRule::SCOPE: pf << h << as[2] << cs[0]; break;
        case LfscRule::NEG_SYMM: pf << h << h << cs[0]; break;
        case LfscRule::CONG: pf << h << h << h << h << cs[0] << cs[1]; break;
        case LfscRule::AND_INTRO1: pf << h << cs[0]; break;
        case LfscRule::NOT_AND_REV: pf << h << h << cs[0]; break;
        case LfscRule::PROCESS_SCOPE: pf << h << h << as[2] << cs[0]; break;
        case LfscRule::AND_INTRO2: pf << h << h << cs[0] << cs[1]; break;
        case LfscRule::ARITH_SUM_UB: pf << h << h << h << cs[0] << cs[1]; break;
        default: return false; break;
      }
    }
    break;
    case PfRule::DSL_REWRITE:
    {
      DslPfRule di = DslPfRule::FAIL;
      if (!rewriter::getDslPfRule(args[0], di))
      {
        Assert(false);
      }
      Trace("lfsc-print-debug2") << "Printing dsl rule " << di << std::endl;
      const rewriter::RewriteProofRule& rpr = d_rdb->getRule(di);
      const std::vector<Node>& varList = rpr.getVarList();
      Assert(as.size() == varList.size() + 1);
      // print holes/terms based on whether variables are explicit
      for (size_t i = 1, nargs = as.size(); i < nargs; i++)
      {
        Node v = varList[i - 1];
        if (rpr.isExplicitVar(v))
        {
          // If the variable is a list variable, we must convert its value to
          // the proper term. This is based on its context.
          if (as[i].getKind() == SEXPR)
          {
            Assert(args[i].getKind() == SEXPR);
            NodeManager* nm = NodeManager::currentNM();
            Kind k = rpr.getListContext(v);
            // notice we use d_tproc.getNullTerminator and not
            // expr::getNullTerminator here, which has subtle differences
            // e.g. re.empty vs (str.to_re "").
            Node null = d_tproc.getNullTerminator(k, v.getType());
            Node t;
            if (as[i].getNumChildren() == 1)
            {
              // Singleton list uses null terminator. We first construct an
              // original term and convert it.
              Node tt = nm->mkNode(k, args[i][0], null);
              tt = d_tproc.convert(tt);
              // Since conversion adds a null terminator, we have that
              // tt is of the form (f t (f null null)). We reconstruct
              // the proper term (f t null) below.
              Assert(tt.getNumChildren() == 2);
              Assert(tt[1].getNumChildren() == 2);
              std::vector<Node> tchildren;
              if (tt.getMetaKind() == metakind::PARAMETERIZED)
              {
                tchildren.push_back(tt.getOperator());
              }
              tchildren.push_back(tt[0]);
              tchildren.push_back(tt[1][0]);
              t = nm->mkNode(tt.getKind(), tchildren);
            }
            else
            {
              if (k == UNDEFINED_KIND)
              {
                Unhandled() << "Unknown context for list variable " << v
                            << " in rule " << di;
              }
              if (as[i].getNumChildren() == 0)
              {
                t = null;
              }
              else
              {
                // re-convert it
                std::vector<Node> vec(args[i].begin(), args[i].end());
                t = nm->mkNode(k, vec);
              }
              t = d_tproc.convert(t);
            }
            pf << t;
          }
          else
          {
            pf << as[i];
          }
        }
        else
        {
          pf << h;
        }
      }
      // print child proofs, which is based on the format computed for the rule
      size_t ccounter = 0;
      std::map<rewriter::DslPfRule, std::vector<Node>>::iterator itf =
          d_dslFormat.find(di);
      if (itf == d_dslFormat.end())
      {
        // We may not have computed the format yet, e.g. if we are printing
        // via the pre print channel. In this case, just print all the children.
        for (const ProofNode* c : cs)
        {
          pf << c;
        }
      }
      else
      {
        for (const Node& f : itf->second)
        {
          if (f.isNull())
          {
            // this position is a hole
            pf << h;
            continue;
          }
          Assert(ccounter < cs.size());
          pf << cs[ccounter];
          ccounter++;
        }
        Assert(ccounter == cs.size());
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

void LfscPrinter::printDslRule(std::ostream& out,
                               DslPfRule id,
                               std::vector<Node>& format)
{
  const rewriter::RewriteProofRule& rpr = d_rdb->getRule(id);
  const std::vector<Node>& varList = rpr.getVarList();
  const std::vector<Node>& uvarList = rpr.getUserVarList();
  const std::vector<Node>& conds = rpr.getConditions();
  Node conc = rpr.getConclusion();

  std::stringstream oscs;
  std::stringstream odecl;

  std::stringstream rparen;
  odecl << "(declare ";
  LfscPrintChannelOut::printDslProofRuleId(odecl, id);
  std::vector<Node> vlsubs;
  // streams for printing the computation of term in side conditions or
  // list semantics substitutions
  std::stringstream argList;
  std::stringstream argListTerms;
  // the list variables
  std::unordered_set<Node> listVars;
  argList << "(";
  // use the names from the user variable list (uvarList)
  for (const Node& v : uvarList)
  {
    std::stringstream sss;
    sss << v;
    Node s = d_tproc.mkInternalSymbol(sss.str(), v.getType());
    odecl << " (! " << sss.str() << " term";
    argList << "(" << sss.str() << " term)";
    argListTerms << " " << sss.str();
    rparen << ")";
    vlsubs.push_back(s);
    // remember if v was a list variable, we must convert these in side
    // condition printing below
    if (expr::isListVar(v))
    {
      listVars.insert(s);
    }
  }
  argList << ")";
  // print conditions
  size_t termCount = 0;
  size_t scCount = 0;
  // print conditions, then conclusion
  // TODO: incorporate other side conditions
  for (size_t i = 0, nconds = conds.size(); i <= nconds; i++)
  {
    bool isConclusion = i == nconds;
    Node term = isConclusion ? conc : conds[i];
    Node sterm = term.substitute(
        varList.begin(), varList.end(), vlsubs.begin(), vlsubs.end());
    if (expr::hasListVar(term))
    {
      Assert(!listVars.empty());
      scCount++;
      std::stringstream scName;
      scName << "dsl.sc." << scCount << "." << id;
      // generate the side condition
      oscs << "(program " << scName.str() << " " << argList.str() << " term"
           << std::endl;
      // body must be converted to incorporate list semantics for substitutions
      // first traversal applies nary_elim to required n-ary applications
      LfscListScNodeConverter llsncp(d_tproc, listVars, true);
      Node tscp;
      if (isConclusion)
      {
        Assert(sterm.getKind() == EQUAL);
        // optimization: don't need nary_elim for heads
        tscp = llsncp.convert(sterm[1]);
        tscp = sterm[0].eqNode(tscp);
      }
      else
      {
        tscp = llsncp.convert(sterm);
      }
      // second traversal converts to LFSC form
      Node t = d_tproc.convert(tscp);
      // third traversal applies nary_concat where list variables are used
      LfscListScNodeConverter llsnc(d_tproc, listVars, false);
      Node tsc = llsnc.convert(t);
      oscs << "  ";
      printInternal(oscs, tsc);
      oscs << ")" << std::endl;
      termCount++;
      // introduce a term computed by side condition
      odecl << " (! _t" << termCount << " term";
      rparen << ")";
      format.push_back(Node::null());
      // side condition, which is an implicit argument
      odecl << " (! _s" << scCount << " (^ (" << scName.str();
      rparen << ")";
      // arguments to side condition
      odecl << argListTerms.str() << ") ";
      // matches condition
      odecl << "_t" << termCount << ")";
      if (!isConclusion)
      {
        // the child proof
        odecl << " (! _u" << i;
        rparen << ")";
        format.push_back(term);
      }
      odecl << " (holds _t" << termCount << ")";
      continue;
    }
    // ordinary condition/conclusion, print the term directly
    if (!isConclusion)
    {
      odecl << " (! _u" << i;
      rparen << ")";
      format.push_back(term);
    }
    odecl << " (holds ";
    Node t = d_tproc.convert(sterm);
    printInternal(odecl, t);
    odecl << ")";
  }
  odecl << rparen.str() << std::endl;
  // print the side conditions
  out << oscs.str();
  // print the rule declaration
  out << odecl.str();
}

}  // namespace proof
}  // namespace cvc5
