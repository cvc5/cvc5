/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion to remove subtyping
 */

#include "proof/alethe/alethe_nosubtype_node_converter.h"

namespace cvc5 {
namespace proof {

Node AletheNoSubtypeNodeConverter::postConvert(Node n)
{
  if (n.getKind() == kind::APPLY_UF)
  {
    NodeManager* nm = NodeManager::currentNM();
    TypeNode tn = n.getOperator().getType();
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    // if any of the argument types is real, in case the argument of that
    // position is an integer constant we must turn it into a real constant
    // look at all args, if any is an integer constant, transform it
    bool childChanged = false;
    std::vector<Node> children;
    for (size_t i = 0, size = n.getNumChildren(); i < size; ++i)
    {
      if (!argTypes[i].isReal() || argTypes[i].isInteger() || !n[i].isConst()
          || !n[i].getType().isInteger())
      {
        children.push_back(n[i]);
        continue;
      }
      Trace("alethe-proof-subtyping")
          << "\t\t..arg " << i << " is integer constant " << n[i]
          << " in real position.\n";
      childChanged = true;
      children.push_back(nm->mkNode(kind::CAST_TO_REAL, n[i]));
    }
    if (childChanged)
    {
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.insert(children.begin(), n.getOperator());
      }
      return nm->mkNode(n.getKind(), children);
    }
  }
  return n;
}

}  // namespace proof
}  // namespace cvc5
