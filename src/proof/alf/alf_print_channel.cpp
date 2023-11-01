/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "printer/printer.h"
#include "proof/alf/alf_proof_rule.h"

namespace cvc5::internal {
namespace proof {

AlfPrintChannelOut::AlfPrintChannelOut(std::ostream& out,
                                       const LetBinding& lbind,
                                       const std::string& tprefix)
    : d_out(out), d_lbind(lbind), d_termLetPrefix(tprefix)
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
  d_out << "(" << (isPop ? "step-pop" : "step") << " @p" << i;
  if (!n.isNull())
  {
    printNode(n);
  }
  d_out << " :rule " << rname;
  bool firstTime = true;
  if (!premises.empty())
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

void AlfPrintChannelOut::printTrustStep(ProofRule r, TNode n, size_t i, TNode nc)
{
  Assert(!nc.isNull());
  if (d_warnedRules.find(r) == d_warnedRules.end())
  {
    d_out << "; WARNING: add trust step for " << r << std::endl;
    d_warnedRules.insert(r);
  }
  d_out << "; trust " << r << std::endl;
  printStep("trust", n, i, {}, {nc}, false);
}

void AlfPrintChannelOut::printNodeInternal(std::ostream& out, Node n)
{
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  // use the toStream with custom letification method
  Printer::getPrinter(out)->toStream(out, n, &d_lbind);
}

void AlfPrintChannelOut::printTypeNodeInternal(std::ostream& out, TypeNode tn)
{
  options::ioutils::applyOutputLanguage(out, Language::LANG_SMTLIB_V2_6);
  tn.toStream(out);
}

AlfPrintChannelPre::AlfPrintChannelPre(LetBinding& lbind) : d_lbind(lbind) {}

void AlfPrintChannelPre::printNode(TNode n) { d_lbind.process(n); }

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

void AlfPrintChannelPre::printTrustStep(ProofRule r, TNode n, size_t i, TNode nc)
{
  Assert(!nc.isNull());
  processInternal(nc);
}

void AlfPrintChannelPre::processInternal(const Node& n)
{
  d_lbind.process(n);
  d_keep.insert(n);  // probably not necessary
  expr::getVariables(n, d_vars, d_varsVisited);
}

const std::unordered_set<TNode>& AlfPrintChannelPre::getVariables() const
{
  return d_vars;
}

}  // namespace proof
}  // namespace cvc5::internal
