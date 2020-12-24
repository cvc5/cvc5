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

InferInfo::InferInfo() : d_im(nullptr), d_id(Inference::NONE) {}

bool InferInfo::process(TheoryInferenceManager* im, bool asLemma)
{
  Node lemma = d_conc;
  if (d_ant.size() >= 2)
  {
    Node andNode = NodeManager::currentNM()->mkNode(kind::AND, d_ant);
    lemma = andNode.impNode(lemma);
  }
  else if (d_ant.size() == 1)
  {
    lemma = d_ant[0].impNode(lemma);
  }
  if (asLemma)
  {
    TrustNode trustedLemma = TrustNode::mkTrustLemma(lemma, nullptr);
    return d_im->trustedLemma(trustedLemma);
  }
  Unreachable();
}

bool InferInfo::isTrivial() const
{
  Assert(!d_conc.isNull());
  return d_conc.isConst() && d_conc.getConst<bool>();
}

bool InferInfo::isConflict() const
{
  Assert(!d_conc.isNull());
  return d_conc.isConst() && !d_conc.getConst<bool>();
}

bool InferInfo::isFact() const
{
  Assert(!d_conc.isNull());
  TNode atom = d_conc.getKind() == kind::NOT ? d_conc[0] : d_conc;
  return !atom.isConst() && atom.getKind() != kind::OR;
}

Node InferInfo::getAntecedent() const
{
  // d_noExplain is a subset of d_ant
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkAnd(d_ant);
}

std::ostream& operator<<(std::ostream& out, const InferInfo& ii)
{
  out << "(infer " << ii.d_id << " " << ii.d_conc;
  if (!ii.d_ant.empty())
  {
    out << " :ant (" << ii.d_ant << ")";
  }

  out << ")";
  return out;
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
