/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of non-closed node conversion
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__EXPR__NON_CLOSED_NODE_CONVERTER_H
#define CVC5__PROOF__EXPR__NON_CLOSED_NODE_CONVERTER_H

#include "expr/node.h"
#include "expr/node_converter.h"
#include "expr/type_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

/**
 * This converts a node into one that can be given as an ordinary input
 * to theory solvers.
 *
 * Note this converter is necessary since models for certain types e.g.
 * uninterpreted sorts, codatatypes, arrays, involve terms that cannot be
 * re-asserted to the solver as input.
 *
 * Other types may conditionally use model values that are also illegal in
 * inputs e.g.:
 * - Real algebraic numbers (RAN) for the reals,
 * - Witness terms for strings (for strings of excessive length).
 */
class NonClosedNodeConverter : protected EnvObj, public NodeConverter
{
 public:
  NonClosedNodeConverter(Env& env);
  ~NonClosedNodeConverter();
  /** convert node n as described above during post-order traversal */
  Node postConvert(Node n) override;
  /** Get the purification skolems introduced */
  const std::vector<Node>& getSkolems() const;
  /** Is this node "closed", i.e. able to be re-asserted in a normal input? */
  static bool isClosed(Env& env, const Node& n);

 private:
  /** Get the non-closed kinds, based on the options */
  static void getNonClosedKinds(
      const Env& env, std::unordered_set<Kind, kind::KindHashFunction>& ncks);
  /** Kinds that cannot appear in queries */
  std::unordered_set<Kind, kind::KindHashFunction> d_nonClosedKinds;
  /** The skolems we introduced */
  std::vector<Node> d_purifySkolems;
};

}  // namespace cvc5::internal

#endif
