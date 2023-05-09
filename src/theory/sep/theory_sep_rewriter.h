/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  RewriteResponse postRewrite(TNode node) override;
  RewriteResponse preRewrite(TNode node) override
  {
    Trace("sep-prerewrite") << "Sep::preRewrite returning " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

 private:
  static void getStarChildren(Node n,
                              std::vector<Node>& s_children,
                              std::vector<Node>& ns_children);
  static void getAndChildren(Node n,
                             std::vector<Node>& s_children,
                             std::vector<Node>& ns_children);
  static bool isSpatial(Node n, std::map<Node, bool>& visited);
}; /* class TheorySepRewriter */

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SEP__THEORY_SEP_REWRITER_H */
