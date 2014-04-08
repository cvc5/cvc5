/*********************                                                        */
/*! \file scrutinize.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2013-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Check consistency of internal data structures.
 **
 ** Some checks are very low-level with respect to TheorySetsPrivate
 ** implementation, and hence might become outdated pretty quickly.
 **/

#pragma once

#include "theory/sets/theory_sets_private.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsScrutinize {
  TheorySetsPrivate* d_theory;
public:
  TheorySetsScrutinize(TheorySetsPrivate* theory): d_theory(theory) {
    Debug("sets") << "[sets] scrunitize enabled" << std::endl;
  }
  void postCheckInvariants() const {
    Debug("sets-scrutinize") << "[sets-scrutinize] postCheckInvariants()" << std::endl;
    
    // assume not in conflict, and complete:
    // - try building model
    // - check it
  }
};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

