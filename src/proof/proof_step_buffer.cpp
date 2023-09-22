/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof step and proof step buffer utilities.
 */

#include "proof/proof_step_buffer.h"

#include "proof/proof.h"
#include "proof/proof_checker.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

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

ProofStepBuffer::ProofStepBuffer(ProofChecker* pc,
                                 bool ensureUnique,
                                 bool autoSym)
    : d_autoSym(autoSym), d_checker(pc), d_ensureUnique(ensureUnique)
{
}

Node ProofStepBuffer::tryStep(PfRule id,
                              const std::vector<Node>& children,
                              const std::vector<Node>& args,
                              Node expected)
{
  bool added;
  return tryStep(added, id, children, args, expected);
}

Node ProofStepBuffer::tryStep(bool& added,
                              PfRule id,
                              const std::vector<Node>& children,
                              const std::vector<Node>& args,
                              Node expected)
{
  if (d_checker == nullptr)
  {
    added = false;
    Assert(false) << "ProofStepBuffer::ProofStepBuffer: no proof checker.";
    return Node::null();
  }
  Node res =
      d_checker->checkDebug(id, children, args, expected, "pf-step-buffer");
  if (!res.isNull())
  {
    // add proof step
    added = addStep(id, children, args, res);
  }
  else
  {
    added = false;
  }
  return res;
}

bool ProofStepBuffer::addStep(PfRule id,
                              const std::vector<Node>& children,
                              const std::vector<Node>& args,
                              Node expected)
{
  if (d_ensureUnique)
  {
    if (d_allSteps.find(expected) != d_allSteps.end())
    {
      Trace("psb-debug") << "Discard " << expected << " from " << id
                         << std::endl;
      return false;
    }
    d_allSteps.insert(expected);
    // if we are automatically considering symmetry, we also add the symmetric
    // fact here
    if (d_autoSym)
    {
      Node sexpected = CDProof::getSymmFact(expected);
      if (!sexpected.isNull())
      {
        d_allSteps.insert(sexpected);
      }
    }
    Trace("psb-debug") << "Add " << expected << " from " << id << std::endl;
  }
  d_steps.push_back(
      std::pair<Node, ProofStep>(expected, ProofStep(id, children, args)));
  return true;
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
    if (d_ensureUnique)
    {
      d_allSteps.erase(d_steps.back().first);
    }
    d_steps.pop_back();
  }
}

size_t ProofStepBuffer::getNumSteps() const { return d_steps.size(); }

const std::vector<std::pair<Node, ProofStep>>& ProofStepBuffer::getSteps() const
{
  return d_steps;
}

void ProofStepBuffer::clear()
{
  d_steps.clear();
  d_allSteps.clear();
}

}  // namespace cvc5::internal
