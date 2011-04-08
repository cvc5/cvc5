/*********************                                                        */
/*! \file trans_closure.cpp
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The transitive closure module implementation
 **
 ** Implementation file for TransitiveClosure class.
 **/


#include "util/trans_closure.h"


using namespace std;


namespace CVC4 {


TransitiveClosure::~TransitiveClosure() {
  unsigned i;
  for (i = 0; i < adjMatrix.size(); ++i) {
    adjMatrix[i]->deleteSelf();
  }
}


bool TransitiveClosure::addEdge(unsigned i, unsigned j)
{
  if (adjMatrix.size() > j && adjMatrix[j]->read(i)) {
    return false;
  }
  while (i >= adjMatrix.size()) {
    adjMatrix.push_back(new (true) CDBV(d_context));
  }
  adjMatrix[i]->write(j);
  unsigned k;
  for (k = 0; k < adjMatrix.size(); ++k) {
    if (adjMatrix[k]->read(i)) {
      adjMatrix[k]->write(j);
      adjMatrix[k]->merge(adjMatrix[j]);
    }
  }
  return true;
}


}/* CVC4 namespace */
