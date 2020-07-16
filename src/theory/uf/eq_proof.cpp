/*********************                                                        */
/*! \file eq_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a proof as produced by the equality engine.
 **
 **/

#include "theory/uf/eq_proof.h"

#include "expr/proof.h"

namespace CVC4 {
namespace theory {
namespace eq {

void EqProof::debug_print(const char* c,
                          unsigned tb,
                          PrettyPrinter* prettyPrinter) const
{
  std::stringstream ss;
  debug_print(ss, tb, prettyPrinter);
  Debug(c) << ss.str();
}

void EqProof::debug_print(std::ostream& os,
                          unsigned tb,
                          PrettyPrinter* prettyPrinter) const
{
  for (unsigned i = 0; i < tb; i++)
  {
    os << "  ";
  }

  if (prettyPrinter)
  {
    os << prettyPrinter->printTag(d_id);
  }
  else
  {
    os << static_cast<MergeReasonType>(d_id);
  }
  os << "(";
  if (d_children.empty() && d_node.isNull())
  {
    os << ")";
    return;
  }
  if (!d_node.isNull())
  {
    os << std::endl;
    for (unsigned i = 0; i < tb + 1; ++i)
    {
      os << "  ";
    }
    os << d_node << (!d_children.empty() ? "," : "");
  }
  unsigned size = d_children.size();
  for (unsigned i = 0; i < size; ++i)
  {
    os << std::endl;
    d_children[i]->debug_print(os, tb + 1, prettyPrinter);
    if (i < size - 1)
    {
      for (unsigned j = 0; j < tb + 1; ++j)
      {
        os << "  ";
      }
      os << ",";
    }
  }
  if (size > 0)
  {
    for (unsigned i = 0; i < tb; ++i)
    {
      os << "  ";
    }
  }
  os << ")" << std::endl;
}

void EqProof::cleanReflPremises(std::vector<Node>& premises) const {}

bool EqProof::expandTransitivityForDisequalities(
    Node conclusion,
    std::vector<Node>& premises,
    CDProof* p,
    std::unordered_set<Node, NodeHashFunction>& assumptions) const
{
  return false;
}

bool EqProof::buildTransitivityChain(Node conclusion,
                                     std::vector<Node>& premises) const
{
  return false;
}

void EqProof::reduceNestedCongruence(
    unsigned i,
    Node conclusion,
    std::vector<std::vector<Node>>& transitivityMatrix,
    CDProof* p,
    std::unordered_map<Node, Node, NodeHashFunction>& visited,
    std::unordered_set<Node, NodeHashFunction>& assumptions,
    bool isNary) const
{
}

Node EqProof::addToProof(CDProof* p) const { return Node::null(); }

Node EqProof::addToProof(
    CDProof* p,
    std::unordered_map<Node, Node, NodeHashFunction>& visited,
    std::unordered_set<Node, NodeHashFunction>& assumptions) const
{
  return Node::null();
}

}  // namespace eq
}  // Namespace theory
}  // Namespace CVC4
