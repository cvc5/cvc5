/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of utilities for the non-linear solver.
 */

#include "theory/arith/nl/nl_lemma_utils.h"

#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/nonlinear_extension.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

TrustNode NlLemma::processLemma(LemmaProperty& p)
{
  if (d_nlext != nullptr)
  {
    d_nlext->processSideEffect(*this);
  }
  return SimpleTheoryLemma::processLemma(p);
}

std::ostream& operator<<(std::ostream& out, NlLemma& n)
{
  out << n.d_node;
  return out;
}

bool SortNlModel::operator()(Node i, Node j)
{
  int cv = d_nlm->compare(i, j, d_isConcrete, d_isAbsolute);
  if (cv == 0)
  {
    return i < j;
  }
  return d_reverse_order ? cv < 0 : cv > 0;
}

bool SortNonlinearDegree::operator()(Node i, Node j)
{
  unsigned i_count = getDegree(i);
  unsigned j_count = getDegree(j);
  return i_count == j_count ? (i < j) : (i_count < j_count ? true : false);
}

unsigned SortNonlinearDegree::getDegree(Node n) const
{
  std::map<Node, unsigned>::const_iterator it = d_mdegree.find(n);
  Assert(it != d_mdegree.end());
  return it->second;
}

Node ArgTrie::add(Node d, const std::vector<Node>& args)
{
  ArgTrie* at = this;
  for (const Node& a : args)
  {
    at = &(at->d_children[a]);
  }
  if (at->d_data.isNull())
  {
    at->d_data = d;
  }
  return at->d_data;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
