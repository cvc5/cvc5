/*********************                                                        */
/*! \file trans_closure.cpp
 ** \verbatim
 ** Original author: Clark Barrett
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The transitive closure module implementation
 **
 ** Implementation file for TransitiveClosure class.
 **/


#include "util/trans_closure.h"
#include "util/cvc4_assert.h"


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

bool TransitiveClosure::isConnected(unsigned i, unsigned j)
{
  if( i>=adjMatrix.size() || j>adjMatrix.size() ){
    return false;
  }else{
    return adjMatrix[i] != NULL && adjMatrix[i]->read(j);
  }
}

void TransitiveClosure::debugPrintMatrix()
{
  unsigned i,j;
  for (i = 0; i < adjMatrix.size(); ++i) {
    for (j = 0; j < adjMatrix.size(); ++j) {
      if (adjMatrix[i] != NULL && adjMatrix[i]->read(j)) {
        Debug("trans-closure") << "1 ";
      }
      else Debug("trans-closure") << "0 ";
    }
    Debug("trans-closure") << endl;
  }      
}

unsigned TransitiveClosureNode::getId( Node i ){
  context::CDHashMap< Node, unsigned, NodeHashFunction >::iterator it = nodeMap.find( i );
  if( it==nodeMap.end() ){
    unsigned c = d_counter.get();
    nodeMap[i] = c;
    d_counter.set( c + 1 );
    return c;
  }
  return (*it).second;
}

void TransitiveClosureNode::debugPrint(){
  for( int i=0; i<(int)currEdges.size(); i++ ){
    Debug("trans-closure") << "currEdges[ " << i << " ] = " 
                           << currEdges[i].first << " -> " << currEdges[i].second;
    Debug("trans-closure") << std::endl;
  }
}


}/* CVC4 namespace */
