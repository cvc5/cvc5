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
 * Print channels for LFSC proofs.
 */

#include "proof/lfsc/lfsc_print_channel.h"

#include <sstream>

#include "proof/lfsc/lfsc_util.h"

namespace cvc5::internal {
namespace proof {

LfscPrintChannelOut::LfscPrintChannelOut(std::ostream& out) : d_out(out) {}
void LfscPrintChannelOut::printNode(TNode n)
{
  d_out << " ";
  printNodeInternal(d_out, n);
}

void LfscPrintChannelOut::printTypeNode(TypeNode tn)
{
  d_out << " ";
  printTypeNodeInternal(d_out, tn);
}

void LfscPrintChannelOut::printHole() { d_out << " _ "; }
void LfscPrintChannelOut::printTrust(TNode res, PfRule src)
{
  d_out << std::endl << "(trust ";
  printNodeInternal(d_out, res);
  d_out << ") ; from " << src << std::endl;
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

void LfscPrintChannelOut::printNodeInternal(std::ostream& out, Node n)
{
  // due to use of special names in the node converter, we must clean symbols
  std::stringstream ss;
  options::ioutils::applyOutputLang(ss, Language::LANG_SMTLIB_V2_6);
  n.toStream(ss, -1, 0);
  std::string s = ss.str();
  cleanSymbols(s);
  out << s;
}

void LfscPrintChannelOut::printTypeNodeInternal(std::ostream& out, TypeNode tn)
{
  // due to use of special names in the node converter, we must clean symbols
  std::stringstream ss;
  options::ioutils::applyOutputLang(ss, Language::LANG_SMTLIB_V2_6);
  tn.toStream(ss);
  std::string s = ss.str();
  cleanSymbols(s);
  out << s;
}

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

void LfscPrintChannelOut::cleanSymbols(std::string& s)
{
  size_t start_pos = 0;
  while ((start_pos = s.find("(_ ", start_pos)) != std::string::npos)
  {
    s.replace(start_pos, 3, "(");
    start_pos += 1;
  }
  start_pos = 0;
  while ((start_pos = s.find("__LFSC_TMP", start_pos)) != std::string::npos)
  {
    s.replace(start_pos, 10, "");
  }
}

LfscPrintChannelPre::LfscPrintChannelPre(LetBinding& lbind) : d_lbind(lbind) {}

void LfscPrintChannelPre::printNode(TNode n) { d_lbind.process(n); }
void LfscPrintChannelPre::printTrust(TNode res, PfRule src)
{
  d_lbind.process(res);
}

void LfscPrintChannelPre::printOpenRule(const ProofNode* pn)
{

}

}  // namespace proof
}  // namespace cvc5::internal
