/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference information utility.
 */

#include "theory/bags/infer_info.h"

#include "theory/bags/inference_manager.h"
#include "theory/inference_manager_buffered.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

InferInfo::InferInfo(InferenceManagerBuffered* im, InferenceId id)
    : TheoryInference(id), d_im(im)
{
}

TrustNode InferInfo::processLemma(LemmaProperty& p)
{
  Node lemma = getLemma();

  Trace("bags::InferInfo::process") << (*this) << std::endl;
  d_im->addPendingLemma(lemma, getId());
  return TrustNode::mkTrustLemma(lemma, nullptr);
}

Node InferInfo::getLemma() const
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> nodes;
  Node premises = nm->mkAnd(d_premises);
  Node lemma = nm->mkNode(kind::IMPLIES, premises, d_conclusion);
  nodes.push_back(lemma);
  // send lemmas corresponding to the skolems introduced
  for (const auto& pair : d_skolems)
  {
    Node n = pair.first.eqNode(pair.second);
    nodes.push_back(n);
  }
  if (nodes.size() == 1)
  {
    return lemma;
  }
  return nm->mkNode(kind::AND, nodes);
}

bool InferInfo::isTrivial() const
{
  Assert(!d_conclusion.isNull());
  return d_conclusion.isConst() && d_conclusion.getConst<bool>();
}

bool InferInfo::isConflict() const
{
  Assert(!d_conclusion.isNull());
  return d_conclusion.isConst() && !d_conclusion.getConst<bool>();
}

bool InferInfo::isFact() const
{
  Assert(!d_conclusion.isNull());
  TNode atom =
      d_conclusion.getKind() == kind::NOT ? d_conclusion[0] : d_conclusion;
  return !atom.isConst() && atom.getKind() != kind::OR;
}

std::ostream& operator<<(std::ostream& out, const InferInfo& ii)
{
  out << "(infer ;id " << std::endl << ii.getId() << std::endl;
  out << ";conclusion " << std::endl << ii.d_conclusion << std::endl;
  if (!ii.d_premises.empty())
  {
    out << " ;premise" << std::endl << ii.d_premises << std::endl;
  }
  out << ";skolems " << ii.d_skolems << std::endl;
  out << ")";
  return out;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
