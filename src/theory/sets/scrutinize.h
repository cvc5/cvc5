/*********************                                                        */
/*! \file scrutinize.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Check consistency of internal data structures.
 **
 ** Some checks are very low-level with respect to TheorySetsPrivate
 ** implementation, and hence might become outdated pretty quickly.
 **/

#pragma once

#include <boost/foreach.hpp>

#include "theory/sets/theory_sets.h"
#include "theory/sets/theory_sets_private.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsScrutinize {
  /* we don't want to accidentally modify theory data */
  const TheorySetsPrivate* d_theory;
public:
  TheorySetsScrutinize(TheorySetsPrivate* theory): d_theory(theory) {
    Debug("sets") << "[sets] scrunitize enabled" << std::endl;
  }
  void postCheckInvariants() const {
    Debug("sets-scrutinize") << "[sets-scrutinize] postCheckInvariants()" << std::endl;

    // assume not in conflict, and complete:
    // - try building model
    // - check it

    TheorySetsPrivate::SettermElementsMap settermElementsMap;
    TNode true_atom = NodeManager::currentNM()->mkConst<bool>(true);
    std::set<Node> terms;
    (d_theory->d_external).computeRelevantTerms(terms);
    for(eq::EqClassIterator it_eqclasses(true_atom, &d_theory->d_equalityEngine);
        ! it_eqclasses.isFinished() ; ++it_eqclasses) {
      TNode n = (*it_eqclasses);
      if(n.getKind() == kind::MEMBER) {
        Assert(d_theory->d_equalityEngine.areEqual(n, true_atom));
        TNode x = d_theory->d_equalityEngine.getRepresentative(n[0]);
        TNode S = d_theory->d_equalityEngine.getRepresentative(n[1]);
        settermElementsMap[S].insert(x);
      }
    }
    bool checkPassed = true;
    BOOST_FOREACH(TNode term, terms) {
      if( term.getType().isSet() ) {
        checkPassed &= d_theory->checkModel(settermElementsMap, term);
      }
    }
    if(Debug.isOn("sets-checkmodel-ignore")) {
      Debug("sets-checkmodel-ignore") << "[sets-checkmodel-ignore] checkPassed value was " << checkPassed << std::endl;
    } else {
      Assert( checkPassed,
              "THEORY_SETS check-model failed. Run with -d sets-model for details." );
    }
  }
};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

