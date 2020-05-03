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

ProofStepBuffer::ProofStepBuffer(CDProof * pf) : d_proof(pf), d_checker(pf->getManager()->getChecker())
{
  Assert(d_checker!=nullptr) << "ProofStepBuffer::ProofStepBuffer: no proof checker in the underlying CDProof object.";
}

Node ProofStepBuffer::tryStep(PfRule id, const std::vector<Node>& children, const std::vector<Node>& args,
             Node expected)
{
  Node res = d_checker->check(id, children, args);
  if (!res.isNull())
  {
    if (expected.isNull() || expected==res)
    {
      // add proof step
      d_steps.push_back(std::pair<Node,ProofStep>(res,ProofStep(id, children, args)));
    }
    else
    {
      // did not match provided expected value
      res = Node::null();
    }
  }
  return res;
}

void ProofStepBuffer::finalize()
{
  // add each of the steps
  for (const std::pair<Node,ProofStep>& ps : d_steps)
  {
    d_proof->addStep(ps.first,ps.second);
  }
}

}  // namespace CVC4
