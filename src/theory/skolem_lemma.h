/*********************                                                        */
/*! \file skolem_lemma.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The skolem lemma utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SKOLEM_LEMMA_H
#define CVC4__THEORY__SKOLEM_LEMMA_H

#include "expr/node.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace theory {

class SkolemLemma
{
public:
  SkolemLemma(TrustNode lem, Node k) : d_lemma(lem), d_skolem(k) {}
  /** The lemma, a trust node of kind LEMMA */
  TrustNode d_lemma;
  /** The skolem associated with that lemma */
  Node d_skolem;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SKOLEM_LEMMA_H */
