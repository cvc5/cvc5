/*********************                                                        */
/*! \file lemma_output_channel.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Mechanism for communication about new lemmas
 **
 ** This file defines an interface for use by the theory and propositional
 ** engines to communicate new lemmas to the "outside world".
 **/

#include "cvc4_public.h"

#ifndef CVC4__LEMMA_OUTPUT_CHANNEL_H
#define CVC4__LEMMA_OUTPUT_CHANNEL_H

#include "expr/expr.h"

namespace CVC4 {

/**
 * This interface describes a mechanism for the propositional and theory
 * engines to communicate with the "outside world" about new lemmas being
 * discovered.
 */
class CVC4_PUBLIC LemmaOutputChannel {
public:
 virtual ~LemmaOutputChannel() {}

 /**
  * Notifies this output channel that there's a new lemma.
  * The lemma may or may not be in CNF.
  */
 virtual void notifyNewLemma(Expr lemma) = 0;
};/* class LemmaOutputChannel */

}/* CVC4 namespace */

#endif /* CVC4__LEMMA_OUTPUT_CHANNEL_H */
