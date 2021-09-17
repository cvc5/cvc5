/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes into Alethe proof nodes
 */

#include "proof/alethe/alethe_post_processor.h"

#include "expr/node_algorithm.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "util/rational.h"

namespace cvc5 {

namespace proof {

// This function removes all attributes contained in a given list of attributes
// from a Node res while only recursively updating the node further if
// continueRemoval is true.
static Node removeAttributes(Node res,
                             const std::vector<Kind>& attributes,
                             bool (*continueRemoval)(Node))
{
  if (res.getNumChildren() != 0)
  {
    std::vector<Node> new_children;
    if (res.hasOperator())
    {
      new_children.push_back(res.getOperator());
    }
    for (Node r : res)
    {
      if (std::find(attributes.begin(), attributes.end(), r.getKind())
          == attributes.end())
      {
        new_children.push_back(
            proof::removeAttributes(r, attributes, continueRemoval));
      }
    }
    return NodeManager::currentNM()->mkNode(res.getKind(), new_children);
  }
  return res;
}

}  // namespace proof

}  // namespace cvc5
