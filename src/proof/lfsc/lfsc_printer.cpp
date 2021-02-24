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
#include "expr/proof_checker.h"
#include "proof/proof_letify.h"

namespace CVC4 {
namespace proof {

const char* toString(LfscRule id)
{
  switch (id)
  {
    case LfscRule::SYMM: return "symm";
    case LfscRule::NEG_SYMM: return "neg_symm";
    case LfscRule::CONG: return "cong";
    case LfscRule::TRANS: return "trans";
    case LfscRule::CNF_AND_POS_1: return "cnf_and_pos_1";
    case LfscRule::CNF_AND_POS_2: return "cnf_and_pos_2";
    default: return "?";
  }
}
std::ostream& operator<<(std::ostream& out, LfscRule id)
{
  out << toString(id);
  return out;
}

LfscPrinter::LfscPrinter() {}

void LfscPrinter::print(std::ostream& out,
                        const std::vector<Node>& assertions,
                        const ProofNode* pn)
{
  Trace("lfsc-print-debug") << "; ORIGINAL PROOF: " << *pn << std::endl;
  // closing parentheses
  std::stringstream cparen;

  // [1] compute and print the declarations
  std::unordered_set<Node, NodeHashFunction> syms;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<Node> iasserts;
  for (const Node& a : assertions)
  {
    expr::getSymbols(a, syms, visited);
    iasserts.push_back(d_tproc.convert(a));
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
  uint32_t vidCounter = 0;
  for (const Node& s : syms)
  {
    out << "(define " << s << " (var " << vidCounter << " ";
    print(out, s.getType());
    out << "))" << std::endl;
    vidCounter++;
  }

  // [2] print the check command and term lets
  out << "(check" << std::endl;
  cparen << ")";
  // compute the term lets
  LetBinding lbind;
  for (const Node& ia : iasserts)
  {
    lbind.process(ia);
  }
  // print the let list
  printLetList(out, cparen, lbind);

  // [3] print the assertions, with letification
  // the assumption identifier mapping
  std::map<Node, uint32_t> passumeMap;
  for (size_t i = 0, nasserts = iasserts.size(); i < nasserts; i++)
  {
    Node ia = iasserts[i];
    out << "(% ";
    printAssumeId(out, i);
    out << " (holds ";
    printInternal(out, ia, lbind);
    out << ")" << std::endl;
    cparen << ")";
    // remember the assumption name
    passumeMap[assertions[i]] = i;
  }

  // [4] print the annotation
  out << "(: (holds false)" << std::endl;
  cparen << ")";

  // [5] print the proof body
  Assert(pn->getRule() == PfRule::SCOPE);
  // the outermost scope can be ignored (it is the scope of the assertions,
  // which are already printed above).
  printProofLetify(out, pn->getChildren()[0].get(), lbind, passumeMap);

  out << cparen.str();
}

void LfscPrinter::print(std::ostream& out, const ProofNode* pn)
{
  // TODO: compute term lets across all terms in the proof?
  LetBinding lbind;
  // empty passume map
  std::map<Node, uint32_t> passumeMap;
  printProofLetify(out, pn, lbind, passumeMap);
}

void LfscPrinter::printProofLetify(std::ostream& out,
                                   const ProofNode* pn,
                                   LetBinding& lbind,
                                   std::map<Node, uint32_t>& passumeMap)
{
  // closing parentheses
  std::stringstream cparen;

  // [1] compute and print the proof lets
  std::vector<const ProofNode*> pletList;
  std::map<const ProofNode*, uint32_t> pletMap;
  ProofLetify::computeProofLet(pn, pletList, pletMap);
  // define the let proofs
  if (!pletList.empty())
  {
    out << "; Let proofs:" << std::endl;
    std::map<const ProofNode*, uint32_t>::iterator itp;
    for (const ProofNode* p : pletList)
    {
      itp = pletMap.find(p);
      Assert(itp != pletMap.end());
      uint32_t pid = itp->second;
      out << "(plet _ _ ";
      pletMap.erase(p);
      printProofInternal(out, p, lbind, pletMap, passumeMap);
      pletMap[p] = pid;
      out << " (\\ ";
      printProofId(out, pid);
      out << std::endl;
      cparen << "))";
    }
    out << std::endl;
  }

  // [2] print the proof body
  printProofInternal(out, pn, lbind, pletMap, passumeMap);

  out << cparen.str() << std::endl;
}

void LfscPrinter::printProofInternal(
    std::ostream& out,
    const ProofNode* pn,
    LetBinding& lbind,
    std::map<const ProofNode*, uint32_t>& pletMap,
    std::map<Node, uint32_t>& passumeMap)
{
  // the stack
  std::vector<PExpr> visit;
  // whether we have process children
  std::map<const ProofNode*, bool> processedChildren;
  // helper iterators
  std::map<const ProofNode*, bool>::iterator pit;
  std::map<const ProofNode*, uint32_t>::iterator pletIt;
  std::map<Node, uint32_t>::iterator passumeIt;
  Node curn;
  const ProofNode* cur;
  visit.push_back(PExpr(pn));
  do
  {
    curn = visit.back().d_node;
    cur = visit.back().d_pnode;
    visit.pop_back();
    // case 1: printing a proof
    if (cur != nullptr)
    {
      pit = processedChildren.find(cur);
      if (pit == processedChildren.end())
      {
        // maybe it is letified
        pletIt = pletMap.find(cur);
        if (pletIt != pletMap.end())
        {
          // a letified proof
          out << " ";
          printProofId(out, pletIt->second);
        }
        //        else if (cur->getRule() == PfRule::SCOPE)
        // introduce a?
        else if (cur->getRule() == PfRule::ASSUME)
        {
          // an assumption, must have a name
          passumeIt = passumeMap.find(cur->getResult());
          Assert(passumeIt != passumeMap.end());
          out << " ";
          printAssumeId(out, passumeIt->second);
        }
        else
        {
          // a normal rule application, compute the proof arguments
          std::vector<PExpr> args;

          if (computeProofArgs(cur, args))
          {
            processedChildren[cur] = false;
            // will revisit this proof node to close parentheses
            visit.push_back(PExpr(cur));
            std::reverse(args.begin(), args.end());
            visit.insert(visit.end(), args.begin(), args.end());
            // print the rule name
            out << std::endl << "(";
            printRule(out, cur);
          }
          else
          {
            processedChildren[cur] = true;
            // could not print the rule, trust for now
            out << std::endl << "(trust ";
            Node ni = d_tproc.convert(cur->getResult());
            printInternal(out, ni, lbind);
            out << ") ; from " << cur->getRule() << std::endl;
          }
        }
      }
      else if (!pit->second)
      {
        processedChildren[cur] = true;
        out << ")";
      }
    }
    // case 2: printing a node
    else if (!curn.isNull())
    {
      out << " ";
      // must convert to internal
      Node curni = d_tproc.convert(curn);
      printInternal(out, curni, lbind);
    }
    // case 3: a hole
    else
    {
      out << " _ ";
    }
  } while (!visit.empty());
  out << std::endl;
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
  const std::vector<Node>& as = pn->getArguments();
  PExprStream pf(pargs);
  // hole
  PExpr h;
  Trace("lfsc-print-debug2") << "Compute proof args " << r << " #children= " << cs.size() << " #args=" << as.size() << std::endl;
  switch (r)
  {
    case PfRule::REFL: pf << as[0]; break;
    case PfRule::TRUE_INTRO:
    case PfRule::FALSE_INTRO:
    case PfRule::TRUE_ELIM:
    case PfRule::FALSE_ELIM: pf << h << cs[0]; break;
    case PfRule::CONTRA: pf << h << cs[0] << cs[1]; break;
    case PfRule::EQ_RESOLVE: pf << h << h << cs[0] << cs[1]; break;
    case PfRule::RESOLUTION:
      pf << h << h << h << cs[0] << cs[1] << as[0].getConst<bool>() << as[1];
      break;
    case PfRule::REORDERING:
      pf << h << as[0] << cs[0];
      break;
    // ---------- arguments of non-translated rules go here
    case PfRule::LFSC_RULE:
    {
      LfscRule lr = getLfscRule(as[0]);
      switch (lr)
      {
        case LfscRule::SYMM: pf << h << cs[0]; break;
        case LfscRule::NEG_SYMM: pf << h << cs[0]; break;
        case LfscRule::TRANS: pf << h << h << h << cs[0] << cs[1]; break;
        case LfscRule::CONG: pf << h << h << h << h << cs[0] << cs[1]; break;
        case LfscRule::CNF_AND_POS_1:
        case LfscRule::CNF_AND_POS_2: pf << h << h << cs[0]; break;
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
  std::map<Node, uint32_t>::const_iterator it;
  for (size_t i = 0, nlets = letList.size(); i < nlets; i++)
  {
    Node nl = letList[i];
    out << "(@ ";
    uint32_t id = lbind.getId(nl);
    Assert(id != 0);
    printId(out, id);
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

bool getLfscRule(Node n, LfscRule& lr)
{
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    lr = static_cast<LfscRule>(id);
    return true;
  }
  return false;
}

LfscRule getLfscRule(Node n)
{
  LfscRule lr = LfscRule::UNKNOWN;
  getLfscRule(n, lr);
  return lr;
}

void LfscPrinter::printRule(std::ostream& out, const ProofNode* pn)
{
  if (pn->getRule() == PfRule::LFSC_RULE)
  {
    const std::vector<Node>& args = pn->getArguments();
    out << getLfscRule(args[0]);
    return;
  }
  // Otherwise, convert to lower case
  std::stringstream ss;
  ss << pn->getRule();
  std::string rname = ss.str();
  std::transform(
      rname.begin(), rname.end(), rname.begin(), [](unsigned char c) {
        return std::tolower(c);
      });
  out << rname;
}

void LfscPrinter::printId(std::ostream& out, uint32_t id)
{
  out << "__t" << id;
}

void LfscPrinter::printProofId(std::ostream& out, uint32_t id)
{
  out << "__p" << id;
}

void LfscPrinter::printAssumeId(std::ostream& out, uint32_t id)
{
  out << "__a" << id;
}

Node mkLfscRuleNode(LfscRule r)
{
  return NodeManager::currentNM()->mkConst(Rational(static_cast<uint32_t>(r)));
}

}  // namespace proof
}  // namespace CVC4
