/*********************                                                        */
/*! \file lfsc_print_channel.cpp
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

#include "proof/lfsc/lfsc_print_channel.h"

#include <sstream>

#include "proof/lfsc/lfsc_util.h"

namespace cvc5 {
namespace proof {

LfscPrintChannelOut::LfscPrintChannelOut(std::ostream& out) : d_out(out) {}
void LfscPrintChannelOut::printNode(TNode n)
{
  d_nodeCount++;
  d_out << " " << n;
}

void LfscPrintChannelOut::printTypeNode(TypeNode tn) { d_out << " " << tn; }

void LfscPrintChannelOut::printHole() { d_out << " _ "; }
void LfscPrintChannelOut::printTrust(TNode res, PfRule src)
{
  d_trustCount++;
  d_out << std::endl << "(trust " << res << ") ; from " << src << std::endl;
}

void LfscPrintChannelOut::printOpenRule(const ProofNode* pn)
{
  d_out << std::endl << "(";
  printRule(d_out, pn);
}

void LfscPrintChannelOut::printOpenLfscRule(LfscRule lr)
{
  d_out << std::endl << "(" << lr;
}

void LfscPrintChannelOut::printCloseRule(size_t nparen)
{
  for (size_t i = 0; i < nparen; i++)
  {
    d_out << ")";
  }
}

void LfscPrintChannelOut::printProofId(size_t id)
{
  d_out << " ";
  printProofId(d_out, id);
}
void LfscPrintChannelOut::printAssumeId(size_t id)
{
  d_out << " ";
  printAssumeId(d_out, id);
}

void LfscPrintChannelOut::printEndLine() { d_out << std::endl; }

void LfscPrintChannelOut::printRule(std::ostream& out, const ProofNode* pn)
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

void LfscPrintChannelOut::printId(std::ostream& out, size_t id)
{
  out << "__t" << id;
}

void LfscPrintChannelOut::printProofId(std::ostream& out, size_t id)
{
  out << "__p" << id;
}

void LfscPrintChannelOut::printAssumeId(std::ostream& out, size_t id)
{
  out << "__a" << id;
}

LfscPrintChannelLetifyNode::LfscPrintChannelLetifyNode(LetBinding& lbind)
    : d_lbind(lbind)
{
}

void LfscPrintChannelLetifyNode::printNode(TNode n)
{
  d_nodeCount++;
  d_lbind.process(n);
}
void LfscPrintChannelLetifyNode::printTrust(TNode res, PfRule src)
{
  d_trustCount++;
  d_lbind.process(res);
}

}  // namespace proof
}  // namespace cvc5
