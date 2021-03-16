/*********************                                                        */
/*! \file im_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inst match generator base class
 **/

#include "theory/quantifiers/ematching/im_generator.h"

#include "theory/quantifiers/ematching/trigger.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace inst {

IMGenerator::IMGenerator(Trigger* tparent)
    : d_tparent(tparent), d_qstate(tparent->d_qstate)
{
}

bool IMGenerator::sendInstantiation(InstMatch& m, InferenceId id)
{
  return d_tparent->sendInstantiation(m, id);
}

QuantifiersEngine* IMGenerator::getQuantifiersEngine()
{
  return d_tparent->d_quantEngine;
}


}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
