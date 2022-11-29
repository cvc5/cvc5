/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion
 */

#include "proof/alethe/alethe_node_converter.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"

namespace cvc5::internal {
namespace proof {

AletheNodeConverter::AletheNodeConverter() {}

Node AletheNodeConverter::preConvert(Node n)
{
  Kind k = n.getKind();
  if (k == kind::SKOLEM || k == kind::BOOLEAN_TERM_VARIABLE)
  {
    Trace("alethe-conv") << "AletheNodeConverter: [PRE] handling skolem " << n
                         << "\n";
    Node wi = SkolemManager::getWitnessForm(n);
    // true skolem with witness form, just convert that
    if (!wi.isNull())
    {
      Trace("alethe-conv") << "AletheNodeConverter: ..skolem " << n
                           << " has witness form " << wi << "\n";
      return wi;
    }
    // purification skolem, so we simply retrieve its original form and convert
    // that
    Node oi = SkolemManager::getOriginalForm(n);
    AlwaysAssert(!oi.isNull());
    Trace("alethe-conv")
        << "AletheNodeConverter: ..pre-convert to original form " << oi << "\n";
    return oi;
  }
  return n;
}

Node AletheNodeConverter::postConvertUntyped(Node orig,
                                             const std::vector<Node>& terms,
                                             bool termsChanged)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = orig.getKind();
  AlwaysAssert(k != kind::SKOLEM && k != kind::BOOLEAN_TERM_VARIABLE);
  switch (k)
  {
    // case kind::SKOLEM:
    // case kind::BOOLEAN_TERM_VARIABLE:
    // {
    //   Trace("alethe-conv") << "AletheNodeConverter: ..handling skolem " << orig
    //                        << "\n";
    //   Node wi = SkolemManager::getWitnessForm(orig);
    //   // retrieve the conversion of the witness/original form and use that
    //   // for the conversion of orig
    //   return wi.isNull() ? d_cache[SkolemManager::getOriginalForm(orig)]
    //                      : d_cache[wi];
    // }
    case kind::FORALL:
    {
      // remove patterns, if any
      return terms.size() == 3
                 ? nm->mkNode(kind::FORALL, terms[0], terms[1])
                 : Node(orig);
    }
    // we must make it to be printed with "choice", so as an SEXPR with that
    // internal symbol as the "head"
    case kind::WITNESS:
    {
      std::vector<Node> newTerms{mkInternalSymbol("choice")};
      newTerms.insert(newTerms.end(), terms.begin(), terms.end());
      return nm->mkNode(kind::SEXPR, newTerms);
    }
    default:
    {
      return termsChanged ? nm->mkNode(k, terms) : Node(orig);
    }
  }
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name)
{
  std::unordered_map<std::string, Node>::iterator it = d_symbolsMap.find(name);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node sym = nm->mkBoundVar(name, nm->sExprType());
  d_symbolsMap[name] = sym;
  return sym;
}

}  // namespace proof
}  // namespace cvc5::internal
