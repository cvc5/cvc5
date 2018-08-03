/*********************                                                        */
/*! \file expr_miner.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief expr_miner
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__EXPRESSION_MINER_H
#define __CVC4__THEORY__QUANTIFIERS__EXPRESSION_MINER_H

#include <map>
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class ExprMiner
{
 protected:
  /**
   * Cache of skolems for each free variable that appears in a synthesis check
   * (for --sygus-rr-synth-check).
   */
  std::map<Node, Node> d_fv_to_skolem;
  /** convert */
  Node convertToSkolem(Node n);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS__EXPRESSION_MINER_H */
