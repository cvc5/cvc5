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


Node getOperator(Node x) { return Node::null(); }



TheoryUF::TheoryUF(Context* c) :
  Theory(c), d_pending(c), d_currentPendingIdx(c,0), d_disequality(c)
{}

TheoryUF::~TheoryUF(){}

void TheoryUF::registerTerm(TNode n){

  ECData* ecN;

  if(n.hasAttribute(ECAttr(),&ecN)){
    /* registerTerm(n) is only called when a node has not been seen in the
     * current context.  ECAttr() is not a context-dependent attribute.
     * When n.hasAttribute(ECAttr(),...) is true on a registerTerm(n) call,
     * then it must be the case that this attribute was created in a previous
     * and no longer valid context. Because of this we have to reregister the
     * predecessors lists.
     * Also we do not have to worry about duplicates because all of the Link*
     * setup before are removed when the context n was setup in was popped out
     * of. All we are going to do here are sanity checks.*/

    /*
     * Consider the following chain of events:
     * 1) registerTerm(n) is called on node n where n : f(m) in context level X,
     * 2) A new ECData is created on the heap, ecN,
     * 3) n is added to the predessecor list of m in context level X,
     * 4) We pop out of X,
     * 5) n is removed from the predessecor list of m because this is context
     *    dependent, the Link* will be destroyed and pointers to the Link
     *    structs in the ECData objects will be updated.
     * 6) registerTerm(n) is called on node n in context level Y,
     * 7) If n.hasAttribute(ECAttr(), &ecN), then ecN is still around,
     *    but the predecessor list is not
     *
     * The above assumes that the code is working correctly.
     */
    Assert(ecN->getFirst() == NULL,
           "Equivalence class data exists for the node being registered.  "
           "Expected getFirst() == NULL.  "
           "This data is either already in use or was not properly maintained "
           "during backtracking");
    /*Assert(ecN->getLast() == NULL,
           "Equivalence class data exists for the node being registered.  "
           "Expected getLast() == NULL.  "
           "This data is either already in use or was not properly maintained "
           "during backtracking.");*/
    Assert(ecN->isClassRep(),
           "Equivalence class data exists for the node being registered.  "
           "Expected isClassRep() to be true.  "
           "This data is either already in use or was not properly maintained "
           "during backtracking");
    Assert(ecN->getWatchListSize() == 0,
           "Equivalence class data exists for the node being registered.  "
           "Expected getWatchListSize() == 0.  "
           "This data is either already in use or was not properly maintained "
           "during backtracking");
  }else{
    ecN = new (true) ECData(d_context, n);
    n.setAttribute(ECAttr(), ecN);
  }

  if(n.getKind() == APPLY){
    for(TNode::iterator cIter = n.begin(); cIter != n.end(); ++cIter){
      TNode child = *cIter;

      ECData* ecChild = child.getAttribute(ECAttr());
      ecChild = ccFind(ecChild);

      for(Link* Px = ecChild->getFirst(); Px != NULL; Px = Px->next ){
        if(equiv(n, Px->data)){
          d_pending.push_back(n.eqNode(Px->data));
        }
      }

      ecChild->addPredecessor(n, d_context);
    }
  }

}

bool TheoryUF::sameCongruenceClass(TNode x, TNode y){
  return
    ccFind(x.getAttribute(ECAttr())) ==
    ccFind(y.getAttribute(ECAttr()));
}

bool TheoryUF::equiv(Node x, Node y){
  if(x.getNumChildren() != y.getNumChildren())
    return false;

  if(getOperator(x) != getOperator(y))
    return false;

  Node::iterator xIter = x.begin();
  Node::iterator yIter = y.begin();

  while(xIter != x.end()){

    if(!sameCongruenceClass(*xIter, *yIter)){
      return false;
    }

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
    TNode assertion = d_pending[d_currentPendingIdx];
    d_currentPendingIdx = d_currentPendingIdx + 1;

    TNode x = assertion[0];
    TNode y = assertion[1];

    ECData* ecX = ccFind(x.getAttribute(ECAttr()));
    ECData* ecY = ccFind(y.getAttribute(ECAttr()));
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

  //Make sure all outstanding merges are completed.
  if(d_currentPendingIdx < d_pending.size()){
    merge();
  }

  if(fullEffort(level)){
    for(CDList<Node>::const_iterator diseqIter = d_disequality.begin();
        diseqIter != d_disequality.end();
        ++diseqIter){

      TNode left  = (*diseqIter)[0];
      TNode right = (*diseqIter)[1];
      if(sameCongruenceClass(left, right)){
        out.conflict(*diseqIter, true);
      }
    }
  }
}
