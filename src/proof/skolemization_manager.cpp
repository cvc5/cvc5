/*********************                                                        */
/*! \file skolemization_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

 **/

#include "proof/skolemization_manager.h"

namespace CVC4 {

void SkolemizationManager::registerSkolem(Node disequality, Node skolem) {
  Debug("pf::pm") << "SkolemizationManager: registerSkolem: disequality = " << disequality << ", skolem = " << skolem << std::endl;

  if (isSkolem(skolem)) {
    Assert(d_skolemToDisequality[skolem] == disequality);
    return;
  }

  d_disequalityToSkolem[disequality] = skolem;
  d_skolemToDisequality[skolem] = disequality;
}

bool SkolemizationManager::hasSkolem(Node disequality) {
  return (d_disequalityToSkolem.find(disequality) != d_disequalityToSkolem.end());
}

Node SkolemizationManager::getSkolem(Node disequality) {
  Debug("pf::pm") << "SkolemizationManager: getSkolem( ";
  Assert (d_disequalityToSkolem.find(disequality) != d_disequalityToSkolem.end());
  Debug("pf::pm") << disequality << " ) = " << d_disequalityToSkolem[disequality] << std::endl;
  return d_disequalityToSkolem[disequality];
}

Node SkolemizationManager::getDisequality(Node skolem) {
  Assert (d_skolemToDisequality.find(skolem) != d_skolemToDisequality.end());
  return d_skolemToDisequality[skolem];
}

bool SkolemizationManager::isSkolem(Node skolem) {
  return (d_skolemToDisequality.find(skolem) != d_skolemToDisequality.end());
}

void SkolemizationManager::clear() {
  Debug("pf::pm") << "SkolemizationManager: clear" << std::endl;
  d_disequalityToSkolem.clear();
  d_skolemToDisequality.clear();
}

std::unordered_map<Node, Node, NodeHashFunction>::const_iterator SkolemizationManager::begin() {
  return d_disequalityToSkolem.begin();
}

std::unordered_map<Node, Node, NodeHashFunction>::const_iterator SkolemizationManager::end() {
  return d_disequalityToSkolem.end();
}

} /* CVC4  namespace */
