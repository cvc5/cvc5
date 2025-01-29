/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of separation logic rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SEP__THEORY_SEP_REWRITER_H
#define CVC5__THEORY__SEP__THEORY_SEP_REWRITER_H

#include "theory/theory_rewriter.h"
#include "theory/type_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace sep {

class TheorySepRewriter : public TheoryRewriter
{
 public:
  TheorySepRewriter(NodeManager* nm);
  RewriteResponse postRewrite(TNode node) override;
  RewriteResponse preRewrite(TNode node) override
  {
    Trace("sep-prerewrite") << "Sep::preRewrite returning " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

 private:
  /**
   * Get the children of a SEP_STAR application, partition children based on
   * whether they are spatial.
   * @param n The node to inspect
   * @param s_children The spatial children of n
   * @param ns_children The non-spatial children of n
   */
  void getStarChildren(Node n,
                       std::vector<Node>& s_children,
                       std::vector<Node>& ns_children) const;
  /**
   * Get the children of an AND application, partition children based on whether
   * they are spatial.
   * @param n The node to inspect
   * @param s_children The spatial children of n
   * @param ns_children The non-spatial children of n
   */
  void getAndChildren(Node n,
                      std::vector<Node>& s_children,
                      std::vector<Node>& ns_children) const;
  /**
   * @param n The node to inspect
   * @param visited A cache for the nodes we have visited already
   * @return true if n is a spatial term.
   */
  bool isSpatial(Node n, std::map<Node, bool>& visited) const;
}; /* class TheorySepRewriter */

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SEP__THEORY_SEP_REWRITER_H */
