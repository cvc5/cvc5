/*********************                                                        */
/*! \file lemma_input_channel.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__LEMMA_INPUT_CHANNEL_H
#define __CVC4__LEMMA_INPUT_CHANNEL_H

#include "expr/expr.h"

namespace CVC4 {

class CVC4_PUBLIC LemmaInputChannel {
public:
  virtual ~LemmaInputChannel() throw() { }

  virtual bool hasNewLemma() = 0;
  virtual Expr getNewLemma() = 0;

};/* class LemmaOutputChannel */

}/* CVC4 namespace */

#endif /* __CVC4__LEMMA_INPUT_CHANNEL_H */
