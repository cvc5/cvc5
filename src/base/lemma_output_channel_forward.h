/*********************                                                        */
/*! \file lemma_output_channel_forward.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Forward declaration of the LemmaOutputChannel
 **
 ** This forward declaration of LemmaOutputChannel is needed for the option
 ** lemmaOutputChannel (defined in smt_options) can be a LemmaInputChannel*
 ** without including expr.h.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__LEMMA_OUTPUT_CHANNEL_FORWARD_H
#define __CVC4__LEMMA_OUTPUT_CHANNEL_FORWARD_H

namespace CVC4 {

/**
 * This interface describes a mechanism for the propositional and theory
 * engines to communicate with the "outside world" about new lemmas being
 * discovered.
 */
class CVC4_PUBLIC LemmaOutputChannel;

}/* CVC4 namespace */

#endif /* __CVC4__LEMMA_OUTPUT_CHANNEL_FORWARD_H */
