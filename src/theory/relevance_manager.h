/*********************                                                        */
/*! \file relevance_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Relevance manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__RELEVANCE_MANAGER__H
#define CVC4__THEORY__RELEVANCE_MANAGER__H

#include <unordered_map>
#include <unordered_set>

#include "context/cdlist.h"
#include "expr/node.h"
#include "theory/valuation.h"

namespace CVC4 {
namespace theory {

/**
 * This class manages queries related to relevance of asserted literals.
 *
 * It stores the input assertions and can be asked if an asserted literal is
 * critical to satisfying the input assertions.
 */
class RelevanceManager
{
  typedef context::CDList<Node> NodeList;

 public:
  RelevanceManager(context::UserContext* userContext, Valuation val);
  /** Notify (preprocessed) assertions. */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);
  /** reset round */
  void resetRound();
  /** is relevant? */
  bool isRelevant(Node lit);

 private:
  /** compute relevance */
  void computeRelevance();
  /** justify */
  int justify(TNode n,
              std::unordered_map<TNode, int, TNodeHashFunction>& cache);
  /** the valuation object */
  Valuation d_val;
  /** The input assertions */
  NodeList d_input;
  /** the set of lterails that are sufficient for justifying the input. */
  std::unordered_set<TNode, TNodeHashFunction> d_rset;
  /*** have we computed relevance this round? */
  bool d_computed;
  /** did we succeed? */
  bool d_success;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__RELEVANCE_MANAGER__H */
