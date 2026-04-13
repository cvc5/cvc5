/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Print channels for Eunoia proofs.
 */

#include "proof/eo/eo_print_channel.h"

#include <sstream>

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "printer/printer.h"
#include "proof/trust_id.h"
#include "rewriter/rewrite_db.h"
#include "proof/alf/logos_node_converter.h"

namespace cvc5::internal {
namespace proof {

EoPrintChannel::EoPrintChannel() {}

EoPrintChannel::~EoPrintChannel() {}

EoPrintChannelOut::EoPrintChannelOut(std::ostream& out,
                                       const LetBinding* lbind,
                                       bool trackWarn)
    : d_out(out),
      d_lbind(lbind),
      d_trackWarn(trackWarn)
{
}

void EoPrintChannelOut::printNode(TNode n)
{
  d_out << " ";
  printNodeInternal(d_out, n);
}

void EoPrintChannelOut::printTypeNode(TypeNode tn)
{
  d_out << " ";
  printTypeNodeInternal(d_out, tn);
}

void EoPrintChannelOut::printAssume(TNode n, size_t i, bool isPush)
{
  Assert(!n.isNull());
  d_out << "(" << (isPush ? "assume-push" : "assume") << " @p" << i;
  printNode(n);
  d_out << ")" << std::endl;
}

void EoPrintChannelOut::printStep(const std::string& rname,
                                  TNode n,
                                  size_t i,
                                  const std::vector<size_t>& premises,
                                  const std::vector<Node>& args,
                                  bool isPop)
{
  printStepInternal(rname, n, i, premises, args, isPop, false);
}
void EoPrintChannelOut::printStepInternal(const std::string& rname,
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

void EoPrintChannelOut::printTrustStep(ProofRule r,
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

void EoPrintChannelOut::printNodeInternal(std::ostream& out, Node n)
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

void EoPrintChannelOut::printTypeNodeInternal(std::ostream& out, TypeNode tn)
{
  tn.toStream(out);
}

EoPrintChannelPre::EoPrintChannelPre(LetBinding* lbind) : d_lbind(lbind) {}

void EoPrintChannelPre::printNode(TNode n)
{
  if (d_lbind)
  {
    d_lbind->process(n);
  }
}

void EoPrintChannelPre::printTypeNode(CVC5_UNUSED TypeNode tn)
{
  // current do nothing
}

void EoPrintChannelPre::printAssume(TNode n,
                                    CVC5_UNUSED size_t i,
                                    CVC5_UNUSED bool isPush)
{
  processInternal(n);
}

void EoPrintChannelPre::printStep(
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

void EoPrintChannelPre::printTrustStep(
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

void EoPrintChannelPre::processInternal(const Node& n)
{
  if (d_lbind)
  {
    d_lbind->process(n);
  }
  d_keep.insert(n);  // probably not necessary
}

CpcLogosChannelOut::CpcLogosChannelOut(std::ostream& out,
                                       const LetBinding* lbind)
    : AlfPrintChannelOut(out, lbind, false)
{
  d_stackSize = 0;
  d_stateId = 0;
  d_stateDef << "def s0 : CState := logos_init_state" << std::endl;
}

void CpcLogosChannelOut::printAssume(TNode n, size_t i, bool isPush)
{
  Assert(!n.isNull());
  d_stateId++;
  if (isPush)
  {
    d_stackPush.push_back(d_stackSize);
    d_stateDef << "def s" << d_stateId << " : CState := (logos_invoke_cmd s";
    d_stateDef << (d_stateId - 1) << " (CCmd.assume_push ";
    printNodeInternal(d_stateDef, n);
    d_stateDef <<  "))" << std::endl;
  }
  else
  {
    d_stateDef << "def s" << d_stateId
               << " : CState := (logos_invoke_assume s" << (d_stateId - 1) << " ";
    printNodeInternal(d_stateDef, n);
    d_stateDef << ")" << std::endl;
  }
  d_stackId[i] = d_stackSize;
  d_stackSize++;
}

void CpcLogosChannelOut::printStep(const std::string& rname,
                                   TNode n,
                                   size_t i,
                                   const std::vector<size_t>& premises,
                                   const std::vector<Node>& args,
                                   bool isPop)
{
  // must convert - to _ from RARE rule names.
  std::string rnameUse = LogosNodeConverter::replace_all(rname, "-", "_");
  d_stateId++;
  d_stateDef << "def s" << d_stateId << " : CState := (logos_invoke_cmd s"
             << (d_stateId - 1);
  d_stateDef << " (CCmd.step" << (isPop ? "_pop" : "") <<  " CRule." << rnameUse;
  // get the premise indices in terms of depth on the stack
  std::vector<size_t> pindices;
  std::map<size_t, size_t>::iterator its;
  for (size_t p : premises)
  {
    its = d_stackId.find(p);
    if (its != d_stackId.end())
    {
      Assert(d_stackSize > its->second);
      pindices.push_back(d_stackSize - its->second - 1);
    }
    else
    {
      std::stringstream ss;
      ss << "Failed to find proof identifier " << p << " to " << rname;
      InternalError() << ss.str();
    }
  }
  // always package as list
  // determine if premise list, if so, package as list
  std::string ret = "CIndexList.nil";
  for (size_t j = 0, npremises = pindices.size(); j < npremises; j++)
  {
    size_t jj = (npremises - 1) - j;
    std::stringstream retNext;
    retNext << "(CIndexList.cons " << pindices[jj] << " " << ret << ")";
    ret = retNext.str();
  }
  std::string aret = "CArgList.nil";
  for (size_t j = 0, nargs = args.size(); j < nargs; j++)
  {
    size_t jj = (nargs - 1) - j;
    Node a = args[jj];
    std::stringstream anext;
    anext << "(CArgList.cons ";
    printNodeInternal(anext, a);
    anext << " " << aret << ")";
    aret = anext.str();
  }
  d_stateDef << " " << aret << " " << ret;
  d_stateDef << "))" << std::endl;
  // if step-pop, revert stack size
  if (isPop)
  {
    Assert(!d_stackPush.empty());
    d_stackSize = d_stackPush.back();
    d_stackPush.pop_back();
  }
  d_stackId[i] = d_stackSize;
  d_stackSize++;
  // print a command to check proven if given
  if (!n.isNull())
  {
    d_stateId++;
    d_stateDef << "def s" << d_stateId << ": CState := (logos_invoke_cmd s"
               << (d_stateId - 1);
    d_stateDef << " (CCmd.check_proven ";
    printNodeInternal(d_stateDef, n);
    d_stateDef << "))" << std::endl;
  }
}

void CpcLogosChannelOut::printTrustStep(ProofRule r,
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

void CpcLogosChannelOut::finalize()
{
  d_out << d_stateDef.str();
  d_out << "#eval!" << std::endl;
  d_out << "(logos_state_is_refutation s" << d_stateId << ")" << std::endl;
}

}  // namespace proof
}  // namespace cvc5::internal
