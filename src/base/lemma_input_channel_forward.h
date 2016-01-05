/*********************                                                        */
/*! \file lemma_input_channel_forward.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Forward declaration of LemmaInputChannel.
 **
 ** This forward declaration of LemmaInputChannel is needed for the option
 ** lemmaInputChannel (defined in smt_options) can be a LemmaInputChannel*
 ** without including expr.h.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__LEMMA_INPUT_CHANNEL_FORWARD_H
#define __CVC4__LEMMA_INPUT_CHANNEL_FORWARD_H

namespace CVC4 {

class CVC4_PUBLIC LemmaInputChannel;

}/* CVC4 namespace */

#endif /* __CVC4__LEMMA_INPUT_CHANNEL_FORWARD_H */
