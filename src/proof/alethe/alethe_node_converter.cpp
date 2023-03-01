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

Node AletheNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  switch (k)
  {
    case kind::SKOLEM:
    case kind::BOOLEAN_TERM_VARIABLE:
    {
      Trace("alethe-conv") << "AletheNodeConverter: handling skolem " << n
                           << "\n";
      Node wi = SkolemManager::getOriginalForm(n);
      Trace("alethe-conv") << "AletheNodeConverter: ..original: " << wi << "\n";
      if (wi == n)
      {
        // if it is not a purification skolem, maybe it has a witness skolem
        wi = SkolemManager::getWitnessForm(n);
      }
      // skolem with witness form, just convert that
      if (!wi.isNull())
      {
        Trace("alethe-conv") << "AletheNodeConverter: ..skolem " << n
                             << " has witness form " << wi << "\n";
        return convert(wi);
      }
      // either random skolem or one with a predefined function. In the former
      // we break, in latter we recover the semantics via the witness form
      // correspoding to the function
      SkolemManager* sm = nm->getSkolemManager();
      SkolemFunId sfi = SkolemFunId::NONE;
      Node cacheVal;
      if (!sm->isSkolemFunction(n, sfi, cacheVal) || sfi == SkolemFunId::NONE)
      {
        Unreachable() << "Fresh Skolem not allowed\n";
      }
      Trace("alethe-conv") << "AletheNodeConverter: ..skolem is fun " << sfi
                           << ", with cache " << cacheVal << "\n";
      if (sfi != SkolemFunId::ARRAY_DEQ_DIFF)
      {
        Unreachable() << "Unsupported Skolem fun " << sfi << "\n";
      }
      // create the witness term (witness ((x T)) ())

      Node v = nm->mkBoundVar(n.getType());
      // the cache for this skolem must be an sexpr with the two arrays
      Node def =
          nm->mkNode(kind::IMPLIES,
                     cacheVal[0].eqNode(cacheVal[1]).notNode(),
                     nm->mkNode(kind::SELECT, cacheVal[0], v)
                         .eqNode(nm->mkNode(kind::SELECT, cacheVal[1], v))
                         .notNode());
      wi = nm->mkNode(kind::WITNESS, nm->mkNode(kind::BOUND_VAR_LIST, v), def);
      Trace("alethe-conv") << "Built " << wi << "\n";
      return convert(wi);
    }
    case kind::FORALL:
    {
      // remove patterns, if any
      return n.getNumChildren() == 3 ? nm->mkNode(kind::FORALL, n[0], n[1]) : n;
    }
    // we must make it to be printed with "choice", so we create an operator
    // with that name and the correct type and do a function application
    case kind::WITNESS:
    {
      std::vector<TypeNode> childrenTypes;
      for (const Node& c : n)
      {
        childrenTypes.push_back(c.getType());
      }
      TypeNode fType = nm->mkFunctionType(childrenTypes, n.getType());
      Node choiceOp = mkInternalSymbol("choice", fType);
      return nm->mkNode(kind::APPLY_UF, choiceOp, n[0], n[1]);
    }
    default:
    {
      return n;
    }
  }
  return n;
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name)
{
  return mkInternalSymbol(name, NodeManager::currentNM()->sExprType());
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name, TypeNode tn)
{
  std::pair<TypeNode, std::string> key(tn, name);
  std::map<std::pair<TypeNode, std::string>, Node>::iterator it =
      d_symbolsMap.find(key);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node sym = nm->mkBoundVar(name, tn);
  d_symbolsMap[key] = sym;
  return sym;
}

}  // namespace proof
}  // namespace cvc5::internal
