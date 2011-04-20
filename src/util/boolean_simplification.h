/*********************                                                        */
/*! \file boolean_simplification.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BOOLEAN_SIMPLIFICATION_H
#define __CVC4__BOOLEAN_SIMPLIFICATION_H

#include "expr/node.h"
#include "util/Assert.h"
#include <vector>


namespace CVC4 {

class BooleanSimplification {
public:

  static const uint32_t DUPLICATE_REMOVAL_THRESHOLD = 10;

  static void removeDuplicates(std::vector<Node>& buffer){
    if(buffer.size() < DUPLICATE_REMOVAL_THRESHOLD){
      std::sort(buffer.begin(), buffer.end());
      std::vector<Node>::iterator new_end = std::unique(buffer.begin(), buffer.end());
      buffer.erase(new_end, buffer.end());
    }
  }

  static Node simplifyConflict(Node andNode){
    Assert(andNode.getKind() == kind::AND);
    std::vector<Node> buffer;
    push_back_associative_commute(andNode, buffer, kind::AND, kind::OR, false);

    removeDuplicates(buffer);

    NodeBuilder<> nb(kind::AND);
    nb.append(buffer);
    return nb;
  }

  static Node simplifyClause(Node orNode){
    Assert(orNode.getKind() == kind::OR);
    std::vector<Node> buffer;
    push_back_associative_commute(orNode, buffer, kind::OR, kind::AND, false);

    removeDuplicates(buffer);

    NodeBuilder<> nb(kind::OR);
    nb.append(buffer);
    return nb;
  }

  static Node simplifyHornClause(Node implication){
    Assert(implication.getKind() == kind::IMPLIES);
    TNode left = implication[0];
    TNode right = implication[1];
    Node notLeft = NodeBuilder<1>(kind::NOT)<<left;
    Node clause = NodeBuilder<2>(kind::OR)<< notLeft << right;
    return simplifyClause(clause);
  }

  static void push_back_associative_commute(Node n, std::vector<Node>& buffer, Kind k, Kind notK, bool negateNode){
    Node::iterator i = n.begin(), end = n.end();
    for(; i != end; ++i){
      Node child = *i;
      if(child.getKind() == k){
        push_back_associative_commute(child, buffer, k, notK, negateNode);
      }else if(child.getKind() == kind::NOT && child[0].getKind() == notK){
        push_back_associative_commute(child, buffer, notK, k, !negateNode);
      }else{
        if(negateNode){
          buffer.push_back(negate(child));
        }else{
          buffer.push_back(child);
        }
      }
    }
  }

  static Node negate(TNode n){
    bool polarity = true;
    TNode base = n;
    while(base.getKind() == kind::NOT){
      base = base[0];
      polarity = !polarity;
    }
    if(polarity){
      return base.notNode();
    }else{
      return base;
    }
  }

};/* class BooleanSimplification */

}/* CVC4 namespace */

#endif /* __CVC4__BOOLEAN_SIMPLIFICATION_H */
