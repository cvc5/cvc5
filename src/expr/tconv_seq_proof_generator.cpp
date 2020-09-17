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
                    const std::vector<TConvProofGenerator*>& ts,
                    context::Context* c,
                    std::string name) : ProofGenerator(name), d_converted(c)
{
  d_tconvs.insert(d_tconvs.end(), ts.begin(), ts.end());
}

TConvSeqProofGenerator::~TConvSeqProofGenerator()
{
}

void TConvSeqProofGenerator::registerConvertedTerm(Node t,
                    Node s,
                    size_t index)
{
}

std::shared_ptr<ProofNode> TConvSeqProofGenerator::getProofFor(Node f)
{
  return nullptr;
}

std::string TConvSeqProofGenerator::identify() const
{
  return d_name;
}

}  // namespace CVC4
