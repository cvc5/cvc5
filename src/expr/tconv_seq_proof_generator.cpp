/*********************                                                        */
/*! \file tconv_seq_proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term conversion sequence proof generator utility
 **/

#include "expr/tconv_seq_proof_generator.h"

namespace CVC4 {

TConvSeqProofGenerator::TConvSeqProofGenerator(
    ProofNodeManager* pnm,
    const std::vector<ProofGenerator*>& ts,
    context::Context* c,
    std::string name)
    : d_pnm(pnm), d_converted(c), d_name(name)
{
  d_tconvs.insert(d_tconvs.end(), ts.begin(), ts.end());
  AlwaysAssert (!d_tconvs.empty()) << "TConvSeqProofGenerator::TConvSeqProofGenerator: expecting non-empty sequence";
}

TConvSeqProofGenerator::~TConvSeqProofGenerator() {}

void TConvSeqProofGenerator::registerConvertedTerm(Node t, Node s, size_t index)
{
  if (t == s)
  {
    // no need
    return;
  }
  std::pair<Node, size_t> key = std::pair<Node, size_t>(t, index);
  d_converted[key] = s;
}

std::shared_ptr<ProofNode> TConvSeqProofGenerator::getProofFor(Node f)
{
  Trace("tconv-seq-pf-gen")
      << "TConvSeqProofGenerator::getProofFor: " << identify() << ": " << f
      << std::endl;
  return getSubsequenceProofFor(f, 0, d_tconvs.size()-1);
}

std::shared_ptr<ProofNode> TConvSeqProofGenerator::getSubsequenceProofFor(Node f, size_t start, size_t end)
{
  Assert (end<d_tconvs.size());
  if (f.getKind() != kind::EQUAL)
  {
    std::stringstream serr;
    serr << "TConvSeqProofGenerator::getProofFor: " << identify()
         << ": fail, non-equality " << f;
    Unhandled() << serr.str();
    Trace("tconv-seq-pf-gen") << serr.str() << std::endl;
    return nullptr;
  }
  // start with the left hand side of the equality
  Node curr = f[0];
  // proofs forming transitivity chain
  std::vector<std::shared_ptr<ProofNode>> transChildren;
  std::pair<Node, size_t> currKey;
  NodeIndexNodeMap::iterator itc;
  // convert the term in sequence
  for (size_t i = start; i <= end; i++)
  {
    currKey = std::pair<Node, size_t>(curr, i);
    itc = d_converted.find(currKey);
    // if we provided a conversion at this index
    if (itc != d_converted.end())
    {
      Node next = (*itc).second;
      Trace("tconv-seq-pf-gen") << "...convert to " << next << std::endl;
      Node eq = curr.eqNode(next);
      std::shared_ptr<ProofNode> pf = d_tconvs[i]->getProofFor(eq);
      transChildren.push_back(pf);
      curr = next;
    }
  }
  // should end up with the right hand side of the equality
  if (curr != f[1])
  {
    // unexpected
    std::stringstream serr;
    serr << "TConvSeqProofGenerator::getProofFor: " << identify()
         << ": failed, mismatch (see -t tconv-seq-pf-gen-debug for details)"
         << std::endl;
    serr << "                    source: " << f[0] << std::endl;
    serr << "expected after conversions: " << f[1] << std::endl;
    serr << "  actual after conversions: " << curr << std::endl;

    if (Trace.isOn("tconv-seq-pf-gen-debug"))
    {
      Trace("tconv-pf-gen-debug")
          << "Printing conversion steps..." << std::endl;
      serr << "Conversions: " << std::endl;
      for (NodeIndexNodeMap::const_iterator it = d_converted.begin();
           it != d_converted.end();
           ++it)
      {
        serr << "(" << (*it).first.first << ", " << (*it).first.second
             << ") -> " << (*it).second << std::endl;
      }
    }
    Unhandled() << serr.str();
    return nullptr;
  }
  // otherwise, make transitivity
  return d_pnm->mkTrans(transChildren, f);
}

std::string TConvSeqProofGenerator::identify() const { return d_name; }


TConvSubSeqGenerator::TConvSubSeqGenerator(TConvSeqProofGenerator* tref, size_t start, size_t end, 
                        std::string name) : d_tref(tref), d_start(start), d_end(end), d_name(name)
{
  
}

std::shared_ptr<ProofNode> TConvSubSeqGenerator::getProofFor(Node f)
{
  return d_tref->getSubsequenceProofFor(f, d_start, d_end);
}
std::string TConvSubSeqGenerator::identify() const { return d_name; }

}  // namespace CVC4
