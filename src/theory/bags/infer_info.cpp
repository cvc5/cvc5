/*********************                                                        */
/*! \file infer_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference information utility.
 **/

#include "theory/bags/infer_info.h"

#include "theory/bags/inference_manager.h"

namespace CVC4 {
namespace theory {
namespace bags {

const char* toString(Inference i)
{
  switch (i)
  {
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Inference i)
{
  out << toString(i);
  return out;
}

InferInfo::InferInfo() : d_id(Inference::NONE) {}

bool InferInfo::process(TheoryInferenceManager* im, bool asLemma)
{
  Node lemma = d_conclusion;
  if (d_premises.size() >= 2)
  {
    Node andNode = NodeManager::currentNM()->mkNode(kind::AND, d_premises);
    lemma = andNode.impNode(lemma);
  }
  else if (d_premises.size() == 1)
  {
    lemma = d_premises[0].impNode(lemma);
  }
  if (asLemma)
  {
    TrustNode trustedLemma = TrustNode::mkTrustLemma(lemma, nullptr);
    return im->trustedLemma(trustedLemma);
  }
  Unreachable();
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

Node InferInfo::getPremises() const
{
  // d_noExplain is a subset of d_ant
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkAnd(d_premises);
}

std::ostream& operator<<(std::ostream& out, const InferInfo& ii)
{
  out << "(infer " << ii.d_id << " " << ii.d_conclusion << std::endl;
  if (!ii.d_premises.empty())
  {
    out << " :premise (" << ii.d_premises << ")" << std::endl;
  }

  out << ")";
  return out;
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
