/*********************                                                        */
/*! \file proof_step.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof step
 **/

#include "expr/proof_step.h"

namespace CVC4 {

const char* toString(ProofStep id)
{
  switch (id)
  {
    //================================================= Core rules
    case ProofStep::ASSUME: return "ASSUME";
    //================================================= Unknown rule
    case ProofStep::UNKNOWN: return "UNKNOWN";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, ProofStep id)
{
  out << toString(id);
  return out;
}

}  // namespace CVC4
