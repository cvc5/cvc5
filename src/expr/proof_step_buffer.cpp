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
 ** \brief Implementation of proof step and proof step buffer utilities.
 **/

#include "expr/proof_step_buffer.h"

using namespace CVC4::kind;

namespace CVC4 {

ProofStep::ProofStep() : d_rule(PfRule::UNKNOWN) {}
ProofStep::ProofStep(PfRule r,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args)
    : d_rule(r), d_children(children), d_args(args)
{
}
std::ostream& operator<<(std::ostream& out, ProofStep step)
{
  out << "(step " << step.d_rule;
  for (const Node& c : step.d_children)
  {
    out << " " << c;
  }
  if (!step.d_args.empty())
  {
    out << " :args";
    for (const Node& a : step.d_args)
    {
      out << " " << a;
    }
  }
  out << ")";
  return out;
}

ProofStepBuffer::ProofStepBuffer(ProofChecker* pc) : d_checker(pc) {}

Node ProofStepBuffer::tryStep(PfRule id,
                              const std::vector<Node>& children,
                              const std::vector<Node>& args,
                              Node expected)
{
  if (d_checker == nullptr)
  {
    Assert(false) << "ProofStepBuffer::ProofStepBuffer: no proof checker.";
    return Node::null();
  }
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

void ProofStepBuffer::addStep(PfRule id,
                              const std::vector<Node>& children,
                              const std::vector<Node>& args,
                              Node expected)
{
  d_steps.push_back(
      std::pair<Node, ProofStep>(expected, ProofStep(id, children, args)));
}

void ProofStepBuffer::addSteps(ProofStepBuffer& psb)
{
  const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
  for (const std::pair<Node, ProofStep>& step : steps)
  {
    addStep(step.second.d_rule,
            step.second.d_children,
            step.second.d_args,
            step.first);
  }
}

void ProofStepBuffer::popStep()
{
  Assert(!d_steps.empty());
  if (!d_steps.empty())
  {
    d_steps.pop_back();
  }
}

size_t ProofStepBuffer::getNumSteps() const { return d_steps.size(); }

const std::vector<std::pair<Node, ProofStep>>& ProofStepBuffer::getSteps() const
{
  return d_steps;
}

void ProofStepBuffer::clear() { d_steps.clear(); }

}  // namespace CVC4
