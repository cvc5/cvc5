/*********************                                                        */
/*! \file nary_builder.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "smt_util/nary_builder.h"

#include "expr/metakind.h"

using namespace std;

namespace CVC4 {
namespace util {

Node NaryBuilder::mkAssoc(Kind kind, const std::vector<Node>& children){
  if(children.size() == 0){
    return zeroArity(kind);
  }else if(children.size() == 1){
    return children[0];
  }else{
    const unsigned int max = kind::metakind::getUpperBoundForKind(kind);
    const unsigned int min = kind::metakind::getLowerBoundForKind(kind);

    Assert(min <= children.size());

    unsigned int numChildren = children.size();
    NodeManager* nm = NodeManager::currentNM();
    if( numChildren <= max ) {
      return nm->mkNode(kind,children);
    }

    typedef std::vector<Node>::const_iterator const_iterator;
    const_iterator it = children.begin() ;
    const_iterator end = children.end() ;

    /* The new top-level children and the children of each sub node */
    std::vector<Node> newChildren;
    std::vector<Node> subChildren;

    while( it != end && numChildren > max ) {
      /* Grab the next max children and make a node for them. */
      for(const_iterator next = it + max; it != next; ++it, --numChildren ) {
        subChildren.push_back(*it);
      }
      Node subNode = nm->mkNode(kind,subChildren);
      newChildren.push_back(subNode);
      subChildren.clear();
    }

    /* If there's children left, "top off" the Expr. */
    if(numChildren > 0) {
      /* If the leftovers are too few, just copy them into newChildren;
       * otherwise make a new sub-node  */
      if(numChildren < min) {
        for(; it != end; ++it) {
          newChildren.push_back(*it);
        }
      } else {
        for(; it != end; ++it) {
          subChildren.push_back(*it);
        }
        Node subNode = nm->mkNode(kind, subChildren);
        newChildren.push_back(subNode);
      }
    }

    /* It's inconceivable we could have enough children for this to fail
     * (more than 2^32, in most cases?). */
    AlwaysAssert(newChildren.size() <= max)
        << "Too many new children in mkAssociative";

    /* It would be really weird if this happened (it would require
     * min > 2, for one thing), but let's make sure. */
    AlwaysAssert(newChildren.size() >= min)
        << "Too few new children in mkAssociative";

    return nm->mkNode(kind,newChildren);
  }
}

Node NaryBuilder::zeroArity(Kind k){
  using namespace kind;
  NodeManager* nm = NodeManager::currentNM();
  switch(k){
  case AND:
    return nm->mkConst(true);
  case OR:
    return nm->mkConst(false);
  case PLUS:
    return nm->mkConst(Rational(0));
  case MULT:
    return nm->mkConst(Rational(1));
  default:
    return Node::null();
  }
}


RePairAssocCommutativeOperators::RePairAssocCommutativeOperators()
  : d_cache()
{}
RePairAssocCommutativeOperators::~RePairAssocCommutativeOperators(){}
size_t RePairAssocCommutativeOperators::size() const{ return d_cache.size(); }
void RePairAssocCommutativeOperators::clear(){ d_cache.clear(); }

bool RePairAssocCommutativeOperators::isAssociateCommutative(Kind k){
  using namespace kind;
  switch(k){
  case BITVECTOR_CONCAT:
  case BITVECTOR_AND:
  case BITVECTOR_OR:
  case BITVECTOR_XOR:
  case BITVECTOR_MULT:
  case BITVECTOR_PLUS:
  case DISTINCT:
  case PLUS:
  case MULT:
  case AND:
  case OR:
    return true;
  default:
    return false;
  }
}

Node RePairAssocCommutativeOperators::rePairAssocCommutativeOperators(TNode n){
  if(d_cache.find(n) != d_cache.end()){
    return d_cache[n];
  }
  Node result =
    isAssociateCommutative(n.getKind()) ?
    case_assoccomm(n) : case_other(n);

  d_cache[n] = result;
  return result;
}

Node RePairAssocCommutativeOperators::case_assoccomm(TNode n){
  Kind k = n.getKind();
  Assert(isAssociateCommutative(k));
  Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
  unsigned N = n.getNumChildren();
  Assert(N >= 2);

  Node last = rePairAssocCommutativeOperators( n[N-1]);
  Node nextToLast = rePairAssocCommutativeOperators(n[N-2]);

  NodeManager* nm = NodeManager::currentNM();
  Node last2 = nm->mkNode(k, nextToLast, last);

  if(N <= 2){
    return last2;
  } else{
    Assert(N > 2);
    Node prevRound = last2;
    for(unsigned prevPos = N-2; prevPos > 0; --prevPos){
      unsigned currPos = prevPos-1;
      Node curr = rePairAssocCommutativeOperators(n[currPos]);
      Node round = nm->mkNode(k, curr, prevRound);
      prevRound = round;
    }
    return prevRound;
  }
}

Node RePairAssocCommutativeOperators::case_other(TNode n){
  if(n.isConst() || n.isVar()){
    return n;
  }

  NodeBuilder<> nb(n.getKind());

  if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
    nb << n.getOperator();
  }

  // Remove the ITEs from the children
  for(TNode::const_iterator i = n.begin(), end = n.end(); i != end; ++i) {
    Node newChild = rePairAssocCommutativeOperators(*i);
    nb << newChild;
  }

  Node result = (Node)nb;
  return result;
}

}/* util namespace */
}/* CVC4 namespace */
