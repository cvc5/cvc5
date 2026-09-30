/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Print channel for Logos proofs.
 */

#include "proof/eo/logos_print_channel.h"

#include "printer/printer.h"
#include "proof/eo/logos_node_converter.h"

namespace cvc5::internal {
namespace proof {

CpcLogosChannelOut::CpcLogosChannelOut(std::ostream& out,
                                       const LetBinding* lbind)
    : EoPrintChannelOut(out, lbind, false)
{
  d_stackSize = 0;
  d_stateId = 0;
  // the preamble is printed eagerly, since it must precede everything else
  // that is printed to the output stream, including the term letification.
  getOStream() << "import Cpc.Native" << std::endl;
  getOStream() << "open Eo" << std::endl;
  d_stateDef << "def s0 : LogosState := logos_init_state" << std::endl;
}

void CpcLogosChannelOut::printTermLet(const LetBinding& lbind, TNode n)
{
  std::ostream& out = getOStream();
  out << "def " << lbind.getPrefix() << lbind.getId(n);
  out << " := ";
  // the top-most term is the one we are defining, so it is not letified
  Printer::getPrinter(out)->toStream(out, n, &lbind, false);
  out << std::endl;
}

void CpcLogosChannelOut::printAssume(TNode n, size_t i, bool isPush)
{
  Assert(!n.isNull());
  d_stateId++;
  if (isPush)
  {
    d_stackPush.push_back(d_stackSize);
    d_stateDef << "def s" << d_stateId
               << " : LogosState := (logos_invoke_cmd s";
    d_stateDef << (d_stateId - 1) << " (CCmd.assume_push ";
    printNodeInternal(d_stateDef, n);
    d_stateDef << "))" << std::endl;
  }
  else
  {
    d_stateDef << "def s" << d_stateId
               << " : LogosState := (logos_invoke_assume s" << (d_stateId - 1)
               << " ";
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
  d_stateDef << "def s" << d_stateId << " : LogosState := (logos_invoke_cmd s"
             << (d_stateId - 1);
  d_stateDef << " (CCmd.step" << (isPop ? "_pop" : "") << " CRule." << rnameUse;
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
    d_stateDef << "def s" << d_stateId << ": LogosState := (logos_invoke_cmd s"
               << (d_stateId - 1);
    d_stateDef << " (CCmd.check_proven ";
    printNodeInternal(d_stateDef, n);
    d_stateDef << "))" << std::endl;
  }
}

void CpcLogosChannelOut::printTrustStep(
    ProofRule r,
    CVC5_UNUSED TNode n,
    CVC5_UNUSED size_t i,
    CVC5_UNUSED const std::vector<size_t>& premises,
    CVC5_UNUSED const std::vector<Node>& args,
    CVC5_UNUSED TNode nc)
{
  std::stringstream ss;
  ss << "The proof was incomplete, due to rule " << r;
  InternalError() << ss.str();
}

void CpcLogosChannelOut::finalize()
{
  std::ostream& out = getOStream();
  out << d_stateDef.str();
  out << "#eval!" << std::endl;
  out << "(logos_state_is_refutation s" << d_stateId << ")" << std::endl;
}

}  // namespace proof
}  // namespace cvc5::internal
