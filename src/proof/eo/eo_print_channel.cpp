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

namespace cvc5::internal {
namespace proof {

EoPrintChannel::EoPrintChannel() {}

EoPrintChannel::~EoPrintChannel() {}

EoPrintChannelOut::EoPrintChannelOut(std::ostream& out,
                                     const LetBinding* lbind,
                                     const std::string& tprefix,
                                     bool trackWarn)
    : d_out(out),
      d_lbind(lbind),
      d_termLetPrefix(tprefix),
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

/**
 * Returns a Eunoia rule name to emit for a given TrustId, or the empty
 * string if no specific rule is registered. A rule is considered
 * "registered" when there is a corresponding `(declare-rule <name> ...)`
 * in the Eunoia signatures so that the external eo checker can validate
 * the step (typically as a `:sorry` axiom). Steps emitted under a
 * registered name are not flagged with `; WARNING: add trust step for
 * TRUST`, since the printer is no longer falling back to the generic
 * catch-all `trust` rule for them.
 */
static std::string trustIdRuleName(TrustId tid)
{
  switch (tid)
  {
    case TrustId::ARITH_LIA_STAR_NONNEGATIVE:
      return "arith_lia_star_nonnegative";
    case TrustId::ARITH_LIA_STAR_CONTAINS_REDUCE:
      return "arith_lia_star_contains_reduce";
    default: return std::string();
  }
}

void EoPrintChannelOut::printTrustStep(ProofRule r,
                                       TNode n,
                                       size_t i,
                                       const std::vector<size_t>& premises,
                                       const std::vector<Node>& args,
                                       TNode nc)
{
  Assert(!nc.isNull());
  // If this is a TRUST step with a known TrustId, emit it under the
  // TrustId-specific Eunoia rule and skip the generic "trust" warning
  // and `; trust ...` comment.
  if (r == ProofRule::TRUST)
  {
    TrustId tid;
    if (getTrustId(args[0], tid))
    {
      std::string rname = trustIdRuleName(tid);
      if (!rname.empty())
      {
        // Mirror the shape of the generic `trust` rule: one :args entry
        // carrying the conclusion, and the (possibly empty) premise list.
        printStepInternal(rname, n, i, premises, {nc}, false, true);
        return;
      }
    }
  }
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

}  // namespace proof
}  // namespace cvc5::internal
