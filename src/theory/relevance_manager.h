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

#include "context/cdlist.h"
#include "expr/node.h"

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
  RelevanceManager(context::UserContext* userContext);
  /** compute relevance */
  void computeRelevance();
  /** is relevant? */
  bool isRelevant(Node lit);
 private:
  /** The input assertions */
  NodeList d_input;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__RELEVANCE_MANAGER__H */
