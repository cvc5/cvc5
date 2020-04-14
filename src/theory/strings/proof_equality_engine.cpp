/*********************                                                        */
/*! \file proof_equality_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of strings proof manager
 **/

#include "theory/strings/proof_equality_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

StringsProofEqEngine::StringsProofEqEngine(context::Context* c,
                                           eq::EqualityEngine& ee,
                                           ProofNodeManager* pnm)
    : eq::ProofEqEngine(c, ee, pnm)
{
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
