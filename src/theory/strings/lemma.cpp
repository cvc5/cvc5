/*********************                                                        */
/*! \file lemma.cpp
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

#include "theory/strings/lemma.h"

namespace CVC4 {
namespace theory {
namespace strings {

StringsLemma::StringsLemma(const InferInfo& ii) : d_ii(ii){}

bool StringsLemma::process(InferenceManager * im)
{
  
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
