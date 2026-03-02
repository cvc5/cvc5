/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Print channels for ALF proofs.
 */

#include "proof/alf/alf_print_channel.h"

#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "printer/printer.h"
#include "proof/trust_id.h"
#include "rewriter/rewrite_db.h"

namespace cvc5::internal {
namespace proof {

AlfPrintChannel::AlfPrintChannel() {}

AlfPrintChannel::~AlfPrintChannel() {}

AlfPrintChannelOut::AlfPrintChannelOut(std::ostream& out,
                                       const LetBinding* lbind,
                                       bool trackWarn)
    : d_out(out),
      d_lbind(lbind),
      d_trackWarn(trackWarn)
{
}

void AlfPrintChannelOut::printNode(TNode n)
{
  d_out << " ";
  printNodeInternal(d_out, n);
}

void AlfPrintChannelOut::printTypeNode(TypeNode tn)
{
  d_out << " ";
  printTypeNodeInternal(d_out, tn);
}

void AlfPrintChannelOut::printAssume(TNode n, size_t i, bool isPush)
{
  Assert(!n.isNull());
  d_out << "(" << (isPush ? "assume-push" : "assume") << " @p" << i;
  printNode(n);
  d_out << ")" << std::endl;
}

void AlfPrintChannelOut::printStep(const std::string& rname,
                                   TNode n,
                                   size_t i,
                                   const std::vector<size_t>& premises,
                                   const std::vector<Node>& args,
                                   bool isPop)
{
  printStepInternal(rname, n, i, premises, args, isPop, false);
}
void AlfPrintChannelOut::printStepInternal(const std::string& rname,
                                           TNode n,
                                           size_t i,
                                           const std::vector<size_t>& premises,
                                           const std::vector<Node>& args,
                                           bool isPop,
                                           bool reqPremises)
{
  d_out << "(" << (isPop ? "step-pop" : "step") << " @p" << i;
  if (!n.isNull())
  {
    d_out << " ";
    printNodeInternal(d_out, n);
  }
  d_out << " :rule " << rname;
  bool firstTime = true;
  // if reqPremises is true, we print even if empty
  if (!premises.empty() || reqPremises)
  {
    d_out << " :premises (";
    for (size_t p : premises)
    {
      if (firstTime)
      {
        firstTime = false;
      }
      else
      {
        d_out << " ";
      }
      d_out << "@p" << p;
    }
    d_out << ")";
  }
  if (!args.empty())
  {
    d_out << " :args (";
    firstTime = true;
    for (const Node& a : args)
    {
      if (firstTime)
      {
        firstTime = false;
      }
      else
      {
        d_out << " ";
      }
      printNodeInternal(d_out, a);
    }
    d_out << ")";
  }
  d_out << ")" << std::endl;
}

void AlfPrintChannelOut::printTrustStep(ProofRule r,
                                        TNode n,
                                        size_t i,
                                        const std::vector<size_t>& premises,
                                        const std::vector<Node>& args,
                                        TNode nc)
{
  Assert(!nc.isNull());
  if (d_trackWarn)
  {
    if (d_warnedRules.find(r) == d_warnedRules.end())
    {
      d_out << "; WARNING: add trust step for " << r << std::endl;
      d_warnedRules.insert(r);
    }
  }
  d_out << "; trust " << r;
  if (r == ProofRule::DSL_REWRITE)
  {
    ProofRewriteRule di;
    if (rewriter::getRewriteRule(args[0], di))
    {
      d_out << " " << di;
    }
  }
  else if (r == ProofRule::THEORY_REWRITE)
  {
    ProofRewriteRule di;
    if (rewriter::getRewriteRule(args[0], di))
    {
      d_out << " " << di;
    }
  }
  else if (r == ProofRule::TRUST)
  {
    TrustId tid;
    if (getTrustId(args[0], tid))
    {
      d_out << " " << tid;
    }
  }
  d_out << std::endl;
  // trust takes a premise-list which must be specified even if empty
  printStepInternal("trust", n, i, premises, {nc}, false, true);
}

void AlfPrintChannelOut::printNodeInternal(std::ostream& out, Node n)
{
  if (d_lbind)
  {
    // use the toStream with custom letification method
    Printer::getPrinter(out)->toStream(out, n, d_lbind, true);
  }
  else
  {
    // just use default print
    Printer::getPrinter(out)->toStream(out, n);
  }
}

void AlfPrintChannelOut::printTypeNodeInternal(std::ostream& out, TypeNode tn)
{
  tn.toStream(out);
}

AlfPrintChannelPre::AlfPrintChannelPre(LetBinding* lbind) : d_lbind(lbind) {}

void AlfPrintChannelPre::printNode(TNode n)
{
  if (d_lbind)
  {
    d_lbind->process(n);
  }
}

void AlfPrintChannelPre::printTypeNode(CVC5_UNUSED TypeNode tn)
{
  // current do nothing
}

void AlfPrintChannelPre::printAssume(TNode n,
                                     CVC5_UNUSED size_t i,
                                     CVC5_UNUSED bool isPush)
{
  processInternal(n);
}

void AlfPrintChannelPre::printStep(
    CVC5_UNUSED const std::string& rname,
    TNode n,
    CVC5_UNUSED size_t i,
    CVC5_UNUSED const std::vector<size_t>& premises,
    const std::vector<Node>& args,
    CVC5_UNUSED bool isPop)
{
  if (!n.isNull())
  {
    processInternal(n);
  }
  for (const Node& a : args)
  {
    processInternal(a);
  }
}

void AlfPrintChannelPre::printTrustStep(
    CVC5_UNUSED ProofRule r,
    CVC5_UNUSED TNode n,
    CVC5_UNUSED size_t i,
    CVC5_UNUSED const std::vector<size_t>& premises,
    CVC5_UNUSED const std::vector<Node>& args,
    TNode nc)
{
  Assert(!nc.isNull());
  processInternal(nc);
}

void AlfPrintChannelPre::processInternal(const Node& n)
{
  if (d_lbind)
  {
    d_lbind->process(n);
  }
  d_keep.insert(n);  // probably not necessary
}

CpcLogosLeanChannelOut::CpcLogosLeanChannelOut(std::ostream& out,
                                               const LetBinding* lbind)
    : AlfPrintChannelOut(out, lbind, false)
{
  // TODO: automate?
  d_premiseList["arith_sum_ub"] = true;
  d_premiseList["arith_mult_abs_comparison"] = true;
  d_premiseList["chain_resolution"] = true;
  d_premiseList["chain_m_resolution"] = true;
  d_premiseList["and_intro"] = true;
  d_premiseList["re_concat"] = true;
  d_premiseList["trans"] = true;
  d_premiseList["cong"] = true;
  d_premiseList["nary_cong"] = true;
  d_premiseList["pairwise_cong"] = true;
  d_premiseList["ho_cong"] = true;
  d_stackSize = 0;
}

void CpcLogosLeanChannelOut::printNode(TNode n)
{
  d_out << " ";
  printNodeInternal(d_out, n);
}

void CpcLogosLeanChannelOut::printTypeNode(TypeNode tn)
{
  d_out << " ";
  printTypeNodeInternal(d_out, tn);
}

void CpcLogosLeanChannelOut::printAssume(TNode n, size_t i, bool isPush)
{
  Assert(!n.isNull());
  if (isPush)
  {
    d_cmdList << "(CCmdList.cons (CCmd.assume_push ";
    printNodeInternal(d_cmdList, n);
    d_cmdList << ")" << std::endl;
    d_cmdListEnd << ")";
    d_stackPush.push_back(d_stackSize);
  }
  else
  {
    d_assumeList << "(Term.Apply (Term.Apply Term.and ";
    printNodeInternal(d_assumeList, n);
    d_assumeList << ")" << std::endl;
    d_assumeListEnd << ")";
  }
  d_stackId[i] = d_stackSize;
  d_stackSize++;
}

void CpcLogosLeanChannelOut::printStep(const std::string& rname,
                                       TNode n,
                                       size_t i,
                                       const std::vector<size_t>& premises,
                                       const std::vector<Node>& args,
                                       bool isPop)
{
  d_cmdList << "(CCmdList.cons (CCmd." << rname;
  for (const Node& a : args)
  {
    d_cmdList << " ";
    printNodeInternal(d_cmdList, a);
  }
  // get the premise indices in terms of depth on the stack
  std::vector<size_t> pindices;
  std::map<size_t, size_t>::iterator its;
  for (size_t p : premises)
  {
    its = d_stackId.find(p);
    if (its!=d_stackId.end())
    {
      Assert (d_stackSize>its->second);
      pindices.push_back(d_stackSize-its->second-1);
    }
    else
    {
      std::stringstream ss;
      ss << "Failed to find proof identifier " << p << " to " << rname;
      InternalError() << ss.str();
    }
  }
  // determine if premise list, if so, package as list
  if (d_premiseList.find(rname) != d_premiseList.end())
  {
    std::string ret = "CIndexList.nil";
    for (size_t j = 0, npremises = pindices.size(); j < npremises; j++)
    {
      std::stringstream retNext;
      retNext << "(CIndexList.cons (Term.Numeral " << pindices[j] << ") " << ret << ")";
      ret = retNext.str();
    }
    d_cmdList << " " << ret;
  }
  else
  {
    // otherwise, premises are arguments
    for (size_t j = 0, npremises = pindices.size(); j < npremises; j++)
    {
      d_cmdList << " (Term.Numeral " << pindices[j] << ")";
    }
  }
  d_cmdList << ")" << std::endl;
  d_cmdListEnd << ")";
  // if step-pop, revert stack size
  if (isPop)
  {
    Assert (!d_stackPush.empty());
    d_stackSize = d_stackPush.back();
    d_stackPush.pop_back();
  }
  d_stackId[i] = d_stackSize;
  d_stackSize++;
  // print a command to check proven if given
  if (!n.isNull())
  {
    d_cmdList << "(CCmdList.cons (CCmd.check_proven ";
    printNodeInternal(d_cmdList, n);
    d_cmdList << ")" << std::endl;
    d_cmdListEnd << ")";
  }
}

void CpcLogosLeanChannelOut::printTrustStep(ProofRule r,
                                            TNode n,
                                            size_t i,
                                            const std::vector<size_t>& premises,
                                            const std::vector<Node>& args,
                                            TNode nc)
{
  std::stringstream ss;
  ss << "The proof was incomplete, due to rule " << r;
  InternalError() << ss.str();
}

void CpcLogosLeanChannelOut::finalize()
{
  d_out << "(__eo_checker_is_refutation" << std::endl;
  d_out << d_assumeList.str();
  d_out << "(Term.Boolean true)" << d_assumeListEnd.str() << std::endl;
  d_out << d_cmdList.str();
  d_out << "CCmdList.nil" << d_cmdListEnd.str() << std::endl;
  d_out << ")" << std::endl;
}

}  // namespace proof
}  // namespace cvc5::internal
