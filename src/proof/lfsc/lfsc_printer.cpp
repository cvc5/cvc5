/*********************                                                        */
/*! \file lfsc_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lfsc proof nodes
 **/

#include "proof/lfsc/lfsc_printer.h"

#include "expr/node_algorithm.h"
#include "proof/lfsc/lfsc_print_channel.h"
#include "proof/proof_letify.h"
#include "expr/skolem_manager.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace proof {

LfscPrinter::LfscPrinter(LfscTermProcessor& ltp) : d_tproc(ltp)
{
  NodeManager* nm = NodeManager::currentNM();
  // used for the `flag` type in LFSC
  d_tt = d_tproc.mkInternalSymbol("tt", nm->booleanType());
  d_ff = d_tproc.mkInternalSymbol("ff", nm->booleanType());
}

void LfscPrinter::print(std::ostream& out,
                        const std::vector<Node>& assertions,
                        const ProofNode* pn)
{
  Trace("lfsc-print-debug") << "; ORIGINAL PROOF: " << *pn << std::endl;
  // closing parentheses
  std::stringstream cparen;
  const ProofNode* pnBody = pn->getChildren()[0].get();

  // [1] compute and print the declarations
  std::unordered_set<Node, NodeHashFunction> syms;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<Node> iasserts;
  std::map<Node, size_t> passumeMap;
  for (size_t i = 0, nasserts = assertions.size(); i < nasserts; i++)
  {
    Node a = assertions[i];
    expr::getSymbols(a, syms, visited);
    iasserts.push_back(d_tproc.convert(a));
    // remember the assumption name
    passumeMap[a] = i;
  }
  // [1a] user declared sorts
  std::unordered_set<TypeNode, TypeNodeHashFunction> sts;
  for (const Node& s : syms)
  {
    TypeNode st = s.getType();
    if (st.isSort() && sts.find(st) == sts.end())
    {
      sts.insert(st);
      out << "(declare " << st << " sort)" << std::endl;
    }
  }
  // [1b] user declare function symbols
  for (const Node& s : syms)
  {
    out << "(define " << s << " (var " << d_tproc.getOrAssignIndexForVar(s)
        << " ";
    print(out, s.getType());
    out << "))" << std::endl;
  }

  // [2] compute the proof letification
  std::vector<const ProofNode*> pletList;
  std::map<const ProofNode*, size_t> pletMap;
  ProofLetify::computeProofLet(pnBody, pletList, pletMap);

  // [3] print the check command and term lets
  out << "(check" << std::endl;
  cparen << ")";
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
  LfscPrintChannelLetifyNode lpcln(lbind);
  LetBinding emptyLetBind;
  std::map<const ProofNode*, size_t>::iterator itp;
  for (const ProofNode* p : pletList)
  {
    itp = pletMap.find(p);
    Assert(itp != pletMap.end());
    size_t pid = itp->second;
    pletMap.erase(p);
    printProofInternal(&lpcln, p, emptyLetBind, pletMap, passumeMap);
    pletMap[p] = pid;
  }
  // Print the body of the outermost scope
  printProofInternal(&lpcln, pnBody, emptyLetBind, pletMap, passumeMap);
  Trace("lfsc-print-debug2")
      << "node count let " << lpcln.d_nodeCount << std::endl;
  Trace("lfsc-print-debug2")
      << "trust count let " << lpcln.d_trustCount << std::endl;
  // print the term let list
  printLetList(out, cparen, lbind);

  // [4] print the assertions, with letification
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

  // [5] print the annotation
  out << "(: (holds false)" << std::endl;
  cparen << ")";

  // [6] print the proof body
  Assert(pn->getRule() == PfRule::SCOPE);
  // the outermost scope can be ignored (it is the scope of the assertions,
  // which are already printed above).
  printProofLetify(out, pnBody, lbind, pletList, pletMap, passumeMap);

  out << cparen.str() << std::endl;
}

void LfscPrinter::printProofLetify(
    std::ostream& out,
    const ProofNode* pn,
    const LetBinding& lbind,
    const std::vector<const ProofNode*>& pletList,
    std::map<const ProofNode*, size_t>& pletMap,
    std::map<Node, size_t>& passumeMap)
{
  LfscPrintChannelOut lout(out);

  // closing parentheses
  std::stringstream cparen;

  // define the let proofs
  if (!pletList.empty())
  {
    out << "; Let proofs:" << std::endl;
    std::map<const ProofNode*, size_t>::iterator itp;
    for (const ProofNode* p : pletList)
    {
      itp = pletMap.find(p);
      Assert(itp != pletMap.end());
      size_t pid = itp->second;
      out << "(plet _ _ ";
      pletMap.erase(p);
      printProofInternal(&lout, p, lbind, pletMap, passumeMap);
      pletMap[p] = pid;
      out << " (\\ ";
      LfscPrintChannelOut::printProofId(out, pid);
      // debugging
      if (Trace.isOn("lfsc-print-debug"))
      {
        out << "; proves " << p->getResult();
      }
      out << std::endl;
      cparen << "))";
    }
    out << std::endl;
  }

  // [2] print the proof body
  printProofInternal(&lout, pn, lbind, pletMap, passumeMap);
  Trace("lfsc-print-debug2")
      << "node count print " << lout.d_nodeCount << std::endl;
  Trace("lfsc-print-debug2")
      << "trust count print " << lout.d_trustCount << std::endl;

  out << cparen.str() << std::endl;
}

void LfscPrinter::printProofInternal(
    LfscPrintChannel* out,
    const ProofNode* pn,
    const LetBinding& lbind,
    const std::map<const ProofNode*, size_t>& pletMap,
    std::map<Node, size_t>& passumeMap)
{
  std::unordered_set<const ProofNode*> noBind;
  std::unordered_set<const ProofNode*>::iterator itnb;
  // the stack
  std::vector<PExpr> visit;
  // whether we have process children
  std::map<const ProofNode*, bool> processedChildren;
  // helper iterators
  std::map<const ProofNode*, bool>::iterator pit;
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
      pit = processedChildren.find(cur);
      if (pit == processedChildren.end())
      {
        // maybe it is letified
        pletIt = pletMap.find(cur);
        if (pletIt != pletMap.end())
        {
          // a letified proof
          out->printProofId(pletIt->second);
        }
        else if (r == PfRule::ASSUME)
        {
          // an assumption, must have a name
          passumeIt = passumeMap.find(cur->getResult());
          Assert(passumeIt != passumeMap.end());
          out->printAssumeId(passumeIt->second);
        }
        else
        {
          // a normal rule application, compute the proof arguments, which
          // notice in the case of PI also may modify our passumeMap.
          std::vector<PExpr> args;
          if (computeProofArgs(cur, args, passumeMap, noBind))
          {
            processedChildren[cur] = false;
            // will revisit this proof node to close parentheses
            visit.push_back(PExpr(cur));
            std::reverse(args.begin(), args.end());
            visit.insert(visit.end(), args.begin(), args.end());
            // print the rule name
            out->printOpenRule(cur);
          }
          else
          {
            processedChildren[cur] = true;
            // could not print the rule, trust for now
            Node res = d_tproc.convert(cur->getResult());
            res = lbind.convert(res, "__t", true);
            out->printTrust(res, r);
            if (d_trustWarned.find(r) == d_trustWarned.end())
            {
              d_trustWarned.insert(r);
              Trace("lfsc-print-warn")
                  << "; WARNING: adding trust step for " << r << std::endl;
            }
          }
        }
      }
      else if (!pit->second)
      {
        processedChildren[cur] = true;
        out->printCloseRule();
        if (r == PfRule::LFSC_RULE)
        {
          const std::vector<Node>& cargs = cur->getArguments();
          Assert(!cargs.empty());
          LfscRule lr = getLfscRule(cargs[0]);
          if (lr == LfscRule::LAMBDA)
          {
            itnb = noBind.find(cur);
            if (itnb == noBind.end())
            {
              Assert(cargs.size() == 3);
              // Remove argument from assumption binding, only if it was bound
              // by this call. This is not the case if the assumption is
              // shadowing.
              Assert(passumeMap.find(cargs[2]) != passumeMap.end());
              passumeMap.erase(cargs[2]);
            }
            else
            {
              noBind.erase(cur);
            }
          }
        }
      }
      else
      {
        // this would imply that our proof was not properly letified?
        Assert(false) << "already processed children";
      }
    }
    // case 2: printing a node
    else if (!curn.isNull())
    {
      // it has already been converted to internal form
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
                                   std::vector<PExpr>& pargs,
                                   std::map<Node, size_t>& passumeMap,
                                   std::unordered_set<const ProofNode*>& noBind)
{
  const std::vector<std::shared_ptr<ProofNode>>& children = pn->getChildren();
  std::vector<const ProofNode*> cs;
  for (const std::shared_ptr<ProofNode>& c : children)
  {
    cs.push_back(c.get());
  }
  NodeManager* nm = NodeManager::currentNM();
  PfRule r = pn->getRule();
  const std::vector<Node>& args = pn->getArguments();
  std::vector<Node> as;
  for (const Node& a : args)
  {
    Node ac = d_tproc.convert(a);
    Assert(!ac.isNull());
    as.push_back(ac);
  }
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
    case PfRule::CONTRA: pf << h << cs[0] << cs[1]; break;
    case PfRule::MODUS_PONENS:
    case PfRule::EQ_RESOLVE: pf << h << h << cs[0] << cs[1]; break;
    case PfRule::NOT_AND: pf << h << h << cs[0]; break;
    // case PfRule::NOT_OR_ELIM: pf << h << h <<
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
    // strings
    case PfRule::STRING_LENGTH_POS: pf << as[0]; break;
    case PfRule::RE_INTER: pf << h << h << h << cs[0] << cs[1]; break;
    /*
    case PfRule::RE_UNFOLD_POS: 
      Trace("ajr-temp") << "; String RE_UNFOLD_POS internal : " << d_tproc.convert(pn->getResult()) << std::endl;
      pf << h << h << h << cs[0]; 
      break; 
    case PfRule::STRING_REDUCTION:
    {
      Node res = pn->getResult();
      Trace("ajr-temp") << "String reduction " << res << std::endl;
      Trace("ajr-temp") << "String reduction internal : " << d_tproc.convert(res) << std::endl;
      Assert (res.getKind()==AND);
      Node resw = res[res.getNumChildren()-1];
      Assert (resw.getKind()==EQUAL);
      Node k = resw[1];
      Assert (k.getKind()==SKOLEM);
      Node w = SkolemManager::getOriginalForm(k);
      Trace("ajr-temp") << "Witness " << w << std::endl;
      Assert (w.getKind()==WITNESS);
      Node v = w[0][0];
      TypeNode vti = d_tproc.convertType(v.getType());
      Node n = nm->mkConst(Rational(d_tproc.getOrAssignIndexForVar(v)));
      pf << h << n << vti << as[0];
    }
      break;
      */
    // quantifiers
    //case PfRule::SKOLEM_INTRO: pf << as[0]; break;
    // ---------- arguments of non-translated rules go here
    case PfRule::LFSC_RULE:
    {
      LfscRule lr = getLfscRule(args[0]);
      // Note that `args` has 2 builtin arguments, thus the first real argument
      // begins at index 2
      switch (lr)
      {
        case LfscRule::LAMBDA:
        {
          // allocate an assumption, if necessary
          size_t pid;
          std::map<Node, size_t>::iterator itp = passumeMap.find(args[2]);
          if (itp == passumeMap.end())
          {
            pid = passumeMap.size();
            passumeMap[args[2]] = pid;
          }
          else
          {
            // mark that it did *not* bind its assumption
            noBind.insert(pn);
            pid = itp->second;
          }
          // make the node whose name is the assumption id, where notice that
          // the type of this node does not matter
          std::stringstream pidNodeName;
          LfscPrintChannelOut::printAssumeId(pidNodeName, pid);
          // must be an internal symbol so that it is not turned into (bvar ...)
          Node pidNode =
              d_tproc.mkInternalSymbol(pidNodeName.str(), nm->booleanType());
          pf << pidNode << cs[0];
        }
        break;
        case LfscRule::SCOPE: pf << h << as[2] << cs[0]; break;
        case LfscRule::NEG_SYMM: pf << h << h << cs[0]; break;
        case LfscRule::CONG: pf << h << h << h << h << cs[0] << cs[1]; break;
        case LfscRule::AND_INTRO1: pf << h << cs[0]; break;
        case LfscRule::AND_ELIM1:
        case LfscRule::AND_ELIM2:
        case LfscRule::NOT_AND_REV: pf << h << h << cs[0]; break;
        case LfscRule::AND_INTRO2: pf << h << h << cs[0] << cs[1]; break;
        // ---------- arguments of translated rules go here
        default: return false; break;
      }
      break;
    }
    default:
    {
      return false;
      break;
    }
  }
  return true;
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

void LfscPrinter::printInternal(std::ostream& out,
                                Node n,
                                LetBinding& lbind,
                                bool letTop)
{
  // TODO: smt2 printer, dag thresh 0 print?
  Node nc = lbind.convert(n, "__t", letTop);
  out << nc;
}

void LfscPrinter::print(std::ostream& out, TypeNode tn)
{
  TypeNode tni = d_tproc.convertType(tn);
  printInternal(out, tni);
}

void LfscPrinter::printInternal(std::ostream& out, TypeNode tn)
{
  // (internal) types are always printed as-is
  // TODO: smt2 printer
  out << tn;
}

}  // namespace proof
}  // namespace CVC4
