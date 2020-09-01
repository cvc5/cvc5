/*********************                                                        */
/*! \file strings_inference.h
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

#ifndef CVC4__THEORY__STRINGS__STRINGS_INFERENCE_H
#define CVC4__THEORY__STRINGS__STRINGS_INFERENCE_H

#include "theory/strings/infer_info.h"
#include "theory/theory_inference.h"

namespace CVC4 {
namespace theory {
namespace strings {

class StringsInference : public TheoryInference
{
 public:
  StringsInference(const InferInfo& ii) : d_ii(ii) {}
  ~StringsInference() {}

  /** Process with inference manager im */
  bool process(InferenceManager* im);
  /** The inference info */
  InferInfo d_ii;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__STRINGS_INFERENCE_H */
