/*********************                                                        */
/*! \file proof_step_buffer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof constructor
 **/

#include "expr/proof_step_buffer.h"

#include "expr/proof_skolem_cache.h"
#include "options/strings_options.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"

using namespace CVC4::kind;

namespace CVC4 {

ProofStepBuffer::ProofStepBuffer(ProofChecker* pc) : d_checker(pc)
{
  Assert(d_checker != nullptr)
      << "ProofStepBuffer::ProofStepBuffer: no proof checker.";
}

Node ProofStepBuffer::tryStep(PfRule id,
                              const std::vector<Node>& children,
                              const std::vector<Node>& args,
                              Node expected)
{
  Node res =
      d_checker->checkDebug(id, children, args, expected, "pf-step-buffer");
  if (!res.isNull())
  {
    // add proof step
    d_steps.push_back(
        std::pair<Node, ProofStep>(res, ProofStep(id, children, args)));
  }
  return res;
}

bool ProofStepBuffer::addTo(CDProof* pf)
{
  // add each of the steps
  for (const std::pair<Node, ProofStep>& ps : d_steps)
  {
    if (!pf->addStep(ps.first, ps.second))
    {
      return false;
    }
  }
  return true;
}

void ProofStepBuffer::clear() { d_steps.clear(); }

}  // namespace CVC4
