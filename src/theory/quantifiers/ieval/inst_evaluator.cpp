/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inst evaluator class.
 */

#include "theory/quantifiers/ieval/inst_evaluator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstEvaluator::InstEvaluator(TermRegistry& tr, bool doCanonize)
    : d_context(), d_treg(tr), d_doCanonize(doCanonize)
{
}

void InstEvaluator::watch(Node q)
{
  Assert(q.getKind() == kind::FORALL);
  watch(q, q[1]);
}

void InstEvaluator::watch(Node q, Node body)
{
  Assert(q.getKind() == kind::FORALL);
}

bool InstEvaluator::push(TNode v, TNode s, std::vector<Node>& assignedQuants)
{
  d_context.push();
}

void InstEvaluator::pop() { d_context.pop(); }

std::vector<Node> InstEvaluator::getInstantiationFor(Node q) {}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
