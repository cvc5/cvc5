/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for relations.
 */

#ifndef SRC_THEORY_SETS_RELS_UTILS_H_
#define SRC_THEORY_SETS_RELS_UTILS_H_

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace sets {

class RelsUtils
{
 public:
  // Assumption: the input rel_mem contains all constant pairs
  static std::set<Node> computeTC(std::set<Node> rel_mem, Node rel);

  static void computeTC(Node rel,
                        std::set<Node>& rel_mem,
                        Node fst,
                        Node snd,
                        std::set<Node>& traversed,
                        std::set<Node>& tc_rel_mem);

  static Node constructPair(Node rel, Node a, Node b);
};
}  // namespace sets
}  // namespace theory
}  // namespace cvc5

#endif
