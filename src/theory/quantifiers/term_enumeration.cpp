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
 * Implementation of term enumeration utility.
 */

#include "theory/quantifiers/term_enumeration.h"

#include "theory/quantifiers/quant_bound_inference.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TermEnumeration::TermEnumeration(QuantifiersBoundInference* qbi) : d_qbi(qbi) {}

Node TermEnumeration::getEnumerateTerm(TypeNode tn, unsigned index)
{
  Trace("term-db-enum") << "Get enumerate term " << tn << " " << index
                        << std::endl;
  std::unordered_map<TypeNode, size_t>::iterator it = d_typ_enum_map.find(tn);
  size_t teIndex;
  if (it == d_typ_enum_map.end())
  {
    teIndex = d_typ_enum.size();
    d_typ_enum_map[tn] = teIndex;
    d_typ_enum.push_back(TypeEnumerator(tn));
  }
  else
  {
    teIndex = it->second;
  }
  while (index >= d_enum_terms[tn].size())
  {
    if (d_typ_enum[teIndex].isFinished())
    {
      return Node::null();
    }
    d_enum_terms[tn].push_back(*d_typ_enum[teIndex]);
    ++d_typ_enum[teIndex];
  }
  return d_enum_terms[tn][index];
}

bool TermEnumeration::getDomain(TypeNode tn, std::vector<Node>& dom)
{
  if (!d_qbi || !d_qbi->mayComplete(tn))
  {
    return false;
  }
  Node curre;
  unsigned counter = 0;
  do
  {
    curre = getEnumerateTerm(tn, counter);
    counter++;
    if (!curre.isNull())
    {
      dom.push_back(curre);
    }
  } while (!curre.isNull());
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
