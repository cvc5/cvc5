/*********************                                                        */
/*! \file lemma.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Strings lemma utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__LEMMA_H
#define CVC4__THEORY__STRINGS__LEMMA_H

#include "theory/strings/infer_info.h"
#include "theory/inference_manager_buffered.h"

namespace CVC4 {
namespace theory {
namespace strings {

class StringsLemma : public Lemma
{
public:
  StringsLemma(const InferInfo& ii) : d_ii(ii){}
  ~StringsLemma(){}
  
  /** Process with inference manager im */
  bool process(InferenceManager * im);
  /** The inference info */
  InferInfo d_ii;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__LEMMA_H */
