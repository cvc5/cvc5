/*********************                                                        */
/** theory_uf.cpp
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/


#include "theory/uf/theory_uf.h"
#include "theory/uf/ecdata.h"
#include "expr/kind.h"

using namespace CVC4;
using namespace theory;
using namespace context;


/* Temporaries to facilitate compiling. */
enum TmpEnum {EC};
void setAttribute(Node n, TmpEnum te, ECData * ec){}
ECData* getAttribute(Node n, TmpEnum te) { return NULL; }
Node getOperator(Node x) { return Node::null(); }


void TheoryUF::setup(const Node& n){
  ECData * ecN = new (true) ECData(d_context, n);

  //TODO Make sure attribute manager owns the pointer
  setAttribute(n, EC, ecN);

  if(n.getKind() == APPLY){
    for(Node::iterator cIter = n.begin(); cIter != n.end(); ++cIter){
      Node child = *cIter;
      
      ECData * ecChild = getAttribute(child, EC);
      ecChild = ccFind(ecChild);

      ecChild->addPredecessor(n, d_context);
    }
  }
}

bool TheoryUF::equiv(Node x, Node y){
  if(x.getNumChildren() != y.getNumChildren())
    return false;

  if(getOperator(x) != getOperator(y))
    return false;

  Node::iterator xIter = x.begin();
  Node::iterator yIter = y.begin();

  while(xIter != x.end()){
    
    if(ccFind(getAttribute(*xIter, EC)) !=
       ccFind(getAttribute(*yIter, EC)))
      return false;

    ++xIter;
    ++yIter;
  }
  return true;
}

ECData* TheoryUF::ccFind(ECData * x){
  if( x->getFind() == x)
    return x;
  else{
    return ccFind(x->getFind());
  }
}

void TheoryUF::ccUnion(ECData* ecX, ECData* ecY){
  ECData* nslave;
  ECData* nmaster;

  if(ecX->getWatchListSize() <= ecY->getWatchListSize()){
    nslave = ecX;
    nmaster = ecY;
  }else{
    nslave = ecY;
    nmaster = ecX;
  }

  nslave->setFind(nmaster);

  for(Link* Px = nmaster->getFirst(); Px != NULL; Px = Px->next ){
    for(Link* Py = nslave->getFirst(); Py != NULL; Py = Py->next ){
      if(equiv(Px->data,Py->data)){
        d_pending.push_back((Px->data).eqNode(Py->data));
      }
    }
  }

  ECData::takeOverDescendantWatchList(nslave, nmaster);
}

//TODO make parameters soft references
void TheoryUF::merge(){
  do{
    Node assertion = d_pending[d_currentPendingIdx];
    d_currentPendingIdx = d_currentPendingIdx + 1;
    
    Node x = assertion[0];
    Node y = assertion[1];
    
    ECData* ecX = ccFind(getAttribute(x, EC));
    ECData* ecY = ccFind(getAttribute(y, EC));
    
    if(ecX == ecY)
      continue;
    
    ccUnion(ecX, ecY);
  }while( d_currentPendingIdx < d_pending.size() );
}

void TheoryUF::check(OutputChannel& out, Effort level){
  while(!done()){
    Node assertion = get();
    

    switch(assertion.getKind()){
    case EQUAL:
      d_pending.push_back(assertion);
      merge();
      break;
    case NOT:
      d_disequality.push_back(assertion[0]);
      break;
    default:
      Unreachable();
    }
  }
  if(fullEffort(level)){
    for(CDList<Node>::const_iterator diseqIter = d_disequality.begin();
        diseqIter != d_disequality.end();
        ++diseqIter){
      
      if(ccFind(getAttribute((*diseqIter)[0], EC)) ==
         ccFind(getAttribute((*diseqIter)[1], EC))){
        out.conflict(*diseqIter, true);
      }
    }
  }
}
