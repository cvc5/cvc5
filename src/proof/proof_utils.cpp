/*********************                                                        */
/*! \file proof_utils.cpp
** \verbatim
** Original author: Liana Hadarean
** Major contributors: none
** Minor contributors (to current version): none
** This file is part of the CVC4 project.
** Copyright (c) 2009-2014  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief [[ Add one-line brief description here ]]
**
** [[ Add lengthier description here ]]
** \todo document this file
**/

#include "proof/proof_utils.h"
#include "theory/theory.h"

using namespace CVC4;
using namespace CVC4::utils;

void CVC4::utils::collectAtoms(TNode node, NodeSet& seen) {
  if (seen.find(node) != seen.end())
    return;
  if (theory::Theory::theoryOf(node) != theory::THEORY_BOOL || node.isVar()) {
      seen.insert(node);
      return;
  }
  
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    collectAtoms(node[i], seen);
  }
}
