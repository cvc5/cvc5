/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
                                       const std::string& tprefix,
                                       bool trackWarn)
    : d_out(out),
      d_lbind(lbind),
      d_termLetPrefix(tprefix),
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

void AlfPrintChannelPre::printTypeNode(TypeNode tn)
{
  // current do nothing
}

void AlfPrintChannelPre::printAssume(TNode n, size_t i, bool isPush)
{
  processInternal(n);
}

void AlfPrintChannelPre::printStep(const std::string& rname,
                                   TNode n,
                                   size_t i,
                                   const std::vector<size_t>& premises,
                                   const std::vector<Node>& args,
                                   bool isPop)
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

void AlfPrintChannelPre::printTrustStep(ProofRule r,
                                        TNode n,
                                        size_t i,
                                        const std::vector<size_t>& premises,
                                        const std::vector<Node>& args,
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

}  // namespace proof
}  // namespace cvc5::internal
