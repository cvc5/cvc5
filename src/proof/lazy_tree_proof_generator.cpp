/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the lazy tree proof generator class.
 */

#include "proof/lazy_tree_proof_generator.h"

#include <iostream>

#include "expr/node.h"
#include "proof/proof_generator.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"

namespace cvc5 {

LazyTreeProofGenerator::LazyTreeProofGenerator(ProofNodeManager* pnm,
                                               const std::string& name)
    : d_pnm(pnm), d_name(name)
{
  d_stack.emplace_back(&d_proof);
}
void LazyTreeProofGenerator::openChild()
{
  detail::TreeProofNode& pn = getCurrent();
  pn.d_children.emplace_back();
  d_stack.emplace_back(&pn.d_children.back());
}
void LazyTreeProofGenerator::closeChild()
{
  Assert(getCurrent().d_rule != PfRule::UNKNOWN);
  d_stack.pop_back();
}
detail::TreeProofNode& LazyTreeProofGenerator::getCurrent()
{
  Assert(!d_stack.empty()) << "Proof construction has already been finished.";
  return *d_stack.back();
}
void LazyTreeProofGenerator::setCurrent(PfRule rule,
                                        const std::vector<Node>& premise,
                                        std::vector<Node> args,
                                        Node proven)
{
  detail::TreeProofNode& pn = getCurrent();
  pn.d_rule = rule;
  pn.d_premise = premise;
  pn.d_args = args;
  pn.d_proven = proven;
}
std::shared_ptr<ProofNode> LazyTreeProofGenerator::getProof() const
{
  // Check cache
  if (d_cached) return d_cached;
  Assert(d_stack.empty()) << "Proof construction has not yet been finished.";
  std::vector<std::shared_ptr<ProofNode>> scope;
  d_cached = getProof(scope, d_proof);
  return d_cached;
}

std::shared_ptr<ProofNode> LazyTreeProofGenerator::getProofFor(Node f)
{
  Assert(hasProofFor(f));
  return getProof();
}

bool LazyTreeProofGenerator::hasProofFor(Node f)
{
  return f == getProof()->getResult();
}

std::shared_ptr<ProofNode> LazyTreeProofGenerator::getProof(
    std::vector<std::shared_ptr<ProofNode>>& scope,
    const detail::TreeProofNode& pn) const
{
  // Store scope size to reset scope afterwards
  std::size_t before = scope.size();
  std::vector<std::shared_ptr<ProofNode>> children;
  if (pn.d_rule == PfRule::SCOPE)
  {
    // Extend scope for all but the root node
    if (&pn != &d_proof)
    {
      for (const auto& a : pn.d_args)
      {
        scope.emplace_back(d_pnm->mkAssume(a));
      }
    }
  }
  else
  {
    // Initialize the children with the scope
    children = scope;
  }
  for (auto& c : pn.d_children)
  {
    // Recurse into tree
    children.emplace_back(getProof(scope, c));
  }
  for (const auto& p : pn.d_premise)
  {
    // Add premises as assumptions
    children.emplace_back(d_pnm->mkAssume(p));
  }
  // Reset scope
  scope.resize(before);
  return d_pnm->mkNode(pn.d_rule, children, pn.d_args);
}

void LazyTreeProofGenerator::print(std::ostream& os,
                                   const std::string& prefix,
                                   const detail::TreeProofNode& pn) const
{
  os << prefix << pn.d_rule << ": ";
  container_to_stream(os, pn.d_premise);
  os << " ==> " << pn.d_proven << std::endl;
  if (!pn.d_args.empty())
  {
    os << prefix << ":args ";
    container_to_stream(os, pn.d_args);
    std::cout << std::endl;
  }
  for (const auto& c : pn.d_children)
  {
    print(os, prefix + '\t', c);
  }
}

std::ostream& operator<<(std::ostream& os, const LazyTreeProofGenerator& ltpg)
{
  ltpg.print(os, "", ltpg.d_proof);
  return os;
}

}  // namespace cvc5
