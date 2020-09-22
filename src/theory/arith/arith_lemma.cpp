/*********************                                                        */
/*! \file arith_lemma.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ArithLemma class, derived from Lemma.
 **/

#include "theory/arith/arith_lemma.h"

namespace CVC4 {
namespace theory {
namespace arith {

std::ostream& operator<<(std::ostream& out, const ArithLemma& al)
{
  return out << al.d_node;
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4
