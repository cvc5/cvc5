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
#include "util/Assert.h"


using namespace std;


namespace CVC4 {


TransitiveClosure::~TransitiveClosure() {
  unsigned i;
  for (i = 0; i < adjMatrix.size(); ++i) {
    if (adjMatrix[i]) {
      adjMatrix[i]->deleteSelf();
    }
  }
}


bool TransitiveClosure::addEdge(unsigned i, unsigned j)
{
  // Check for loops
  Assert(i != j, "Cannot add self-loop");
  if (adjMatrix.size() > j && adjMatrix[j] != NULL && adjMatrix[j]->read(i)) {
    return true;
  }

  // Grow matrix if necessary
  unsigned maxSize = ((i > j) ? i : j) + 1;
  while (maxSize > adjMatrix.size()) {
    adjMatrix.push_back(NULL);
  }

  // Add edge from i to j and everything j can reach
  if (adjMatrix[i] == NULL) {
    adjMatrix[i] = new (true) CDBV(d_context);
  }
  adjMatrix[i]->write(j);
  if (adjMatrix[j] != NULL) {
    adjMatrix[i]->merge(adjMatrix[j]);
  }

  // Add edges from everything that can reach i to j and everything that j can reach
  unsigned k;
  for (k = 0; k < adjMatrix.size(); ++k) {
    if (adjMatrix[k] != NULL && adjMatrix[k]->read(i)) {
      adjMatrix[k]->write(j);
      if (adjMatrix[j] != NULL) {
        adjMatrix[k]->merge(adjMatrix[j]);
      }
    }
  }

  return false;
}


void TransitiveClosure::debugPrintMatrix()
{
  unsigned i,j;
  for (i = 0; i < adjMatrix.size(); ++i) {
    for (j = 0; j < adjMatrix.size(); ++j) {
      if (adjMatrix[i] != NULL && adjMatrix[i]->read(j)) {
        cout << "1 ";
      }
      else cout << "0 ";
    }
    cout << endl;
  }      
}

unsigned TransitiveClosureNode::d_counter = 0;

unsigned TransitiveClosureNode::getId( Node i ){
  std::map< Node, unsigned >::iterator it = nodeMap.find( i );
  if( it==nodeMap.end() ){
    nodeMap[i] = d_counter;
    d_counter++;
    return d_counter-1;
  }
  return it->second;
}


}/* CVC4 namespace */
