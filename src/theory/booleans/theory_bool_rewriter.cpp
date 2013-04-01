/*********************                                                        */
/*! \file theory_bool_rewriter.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters, barrett
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <algorithm>
#include "theory/booleans/theory_bool_rewriter.h"

namespace CVC4 {
namespace theory {
namespace booleans {

RewriteResponse TheoryBoolRewriter::preRewrite(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();
  Node tt = nodeManager->mkConst(true);
  Node ff = nodeManager->mkConst(false);

  switch(n.getKind()) {
  case kind::NOT: {
    if (n[0] == tt) return RewriteResponse(REWRITE_DONE, ff);
    if (n[0] == ff) return RewriteResponse(REWRITE_DONE, tt);
    if (n[0].getKind() == kind::NOT) return RewriteResponse(REWRITE_AGAIN, n[0][0]);
    break;
  }
  case kind::OR: {
    if (n.getNumChildren() == 2) {
      if (n[0] == tt || n[1] == tt) return RewriteResponse(REWRITE_DONE, tt);
      if (n[0] == ff) return RewriteResponse(REWRITE_AGAIN, n[1]);
      if (n[1] == ff) return RewriteResponse(REWRITE_AGAIN, n[0]);
    }
    else {
      bool done = true;
      TNode::iterator i = n.begin(), iend = n.end();
      for(; i != iend; ++i) {
        if (*i == tt) return RewriteResponse(REWRITE_DONE, tt);
        if (*i == ff) done = false;
      }
      if (!done) {
        NodeBuilder<> nb(kind::OR);
        for(i = n.begin(); i != iend; ++i) {
          if (*i != ff) nb << *i;
        }
        if (nb.getNumChildren() == 0) return RewriteResponse(REWRITE_DONE, ff);
        if (nb.getNumChildren() == 1) return RewriteResponse(REWRITE_AGAIN, nb.getChild(0));
        return RewriteResponse(REWRITE_AGAIN, nb.constructNode());
      }
    }
    break;
  }
  case kind::AND: {
    //TODO: Why REWRITE_AGAIN here?
    if (n.getNumChildren() == 2) {
      if (n[0] == ff || n[1] == ff) return RewriteResponse(REWRITE_DONE, ff);
      if (n[0] == tt) return RewriteResponse(REWRITE_AGAIN, n[1]);
      if (n[1] == tt) return RewriteResponse(REWRITE_AGAIN, n[0]);
    }
    else {
      bool done = true;
      TNode::iterator i = n.begin(), iend = n.end();
      for(; i != iend; ++i) {
        if (*i == ff) return RewriteResponse(REWRITE_DONE, ff);
        if (*i == tt) done = false;
      }
      if (!done) {
        NodeBuilder<> nb(kind::AND);
        for(i = n.begin(); i != iend; ++i) {
          if (*i != tt) {
            nb << *i;
          }
        }
        if (nb.getNumChildren() == 0) return RewriteResponse(REWRITE_DONE, tt);
        if (nb.getNumChildren() == 1) return RewriteResponse(REWRITE_AGAIN, nb.getChild(0));
        return RewriteResponse(REWRITE_AGAIN, nb.constructNode());
      }
    }
    break;
  }
  case kind::IMPLIES: {
    if (n[0] == ff || n[1] == tt) return RewriteResponse(REWRITE_DONE, tt);
    if (n[0] == tt && n[0] == ff) return RewriteResponse(REWRITE_DONE, ff);
    if (n[0] == tt) return RewriteResponse(REWRITE_AGAIN, n[1]);
    if (n[1] == ff) return RewriteResponse(REWRITE_AGAIN, n[0].notNode());
    break;
  }
  case kind::IFF:
  case kind::EQUAL: {
    // rewrite simple cases of IFF
    if(n[0] == tt) {
      // IFF true x
      return RewriteResponse(REWRITE_AGAIN, n[1]);
    } else if(n[1] == tt) {
      // IFF x true
      return RewriteResponse(REWRITE_AGAIN, n[0]);
    } else if(n[0] == ff) {
      // IFF false x
      return RewriteResponse(REWRITE_AGAIN, n[1].notNode());
    } else if(n[1] == ff) {
      // IFF x false
      return RewriteResponse(REWRITE_AGAIN, n[0].notNode());
    } else if(n[0] == n[1]) {
      // IFF x x
      return RewriteResponse(REWRITE_DONE, tt);
    } else if(n[0].getKind() == kind::NOT && n[0][0] == n[1]) {
      // IFF (NOT x) x
      return RewriteResponse(REWRITE_DONE, ff);
    } else if(n[1].getKind() == kind::NOT && n[1][0] == n[0]) {
      // IFF x (NOT x)
      return RewriteResponse(REWRITE_DONE, ff);
    } else if(n[0].getKind() == kind::EQUAL && n[1].getKind() == kind::EQUAL) {
      // a : (= i x)
      // i : (= j k)
      // x : (= y z)

      // assume wlog k, z are constants and j is the same symbol as y
      // (iff (= j k) (= j z))
      // if k = z
      //  then (iff (= j k) (= j k)) => true
      // else
      //  (iff (= j k) (= j z)) <=> b
      //  b : (and (not (= j k)) (not (= j z)))
      //  (= j k) (= j z) | a b
      //  f       f       | t t
      //  f       t       | f f
      //  t       f       | f f
      //  t       t       | * f
      // * j cannot equal both k and z in a theory model
      TNode t,c;
      if (n[0][0].isConst()) {
        c = n[0][0];
        t = n[0][1];
      }
      else if (n[0][1].isConst()) {
        c = n[0][1];
        t = n[0][0];
      }
      bool matchesForm = false;
      bool constantsEqual = false;
      if (!c.isNull()) {
        if (n[1][0] == t && n[1][1].isConst()) {
          matchesForm = true;
          constantsEqual = (n[1][1] == c);
        }
        else if (n[1][1] == t && n[1][0].isConst()) {
          matchesForm = true;
          constantsEqual = (n[1][1] == c);
        }
      }
      if(matchesForm){
        if(constantsEqual){
          return RewriteResponse(REWRITE_DONE, tt);
        }else{
          Cardinality kappa = t.getType().getCardinality();
          Cardinality two(2l);
          if(kappa.knownLessThanOrEqual(two)){
            return RewriteResponse(REWRITE_DONE, ff);
          }else{
            Node neitherEquality = (n[0].notNode()).andNode(n[1].notNode());
            return RewriteResponse(REWRITE_AGAIN, neitherEquality);
          }
        }
      }
    }
    break;
  }
  case kind::XOR: {
    // rewrite simple cases of XOR
    if(n[0] == tt) {
      // XOR true x
      return RewriteResponse(REWRITE_AGAIN, n[1].notNode());
    } else if(n[1] == tt) {
      // XCR x true
      return RewriteResponse(REWRITE_AGAIN, n[0].notNode());
    } else if(n[0] == ff) {
      // XOR false x
      return RewriteResponse(REWRITE_AGAIN, n[1]);
    } else if(n[1] == ff) {
      // XOR x false
      return RewriteResponse(REWRITE_AGAIN, n[0]);
    } else if(n[0] == n[1]) {
      // XOR x x
      return RewriteResponse(REWRITE_DONE, ff);
    } else if(n[0].getKind() == kind::NOT && n[0][0] == n[1]) {
      // XOR (NOT x) x
      return RewriteResponse(REWRITE_DONE, tt);
    } else if(n[1].getKind() == kind::NOT && n[1][0] == n[0]) {
      // XOR x (NOT x)
      return RewriteResponse(REWRITE_DONE, tt);
    }
    break;
  }
  case kind::ITE: {
    // non-Boolean-valued ITEs should have been removed in place of
    // a variable
    // rewrite simple cases of ITE
    if (n[0].isConst()) {
      if (n[0] == tt) {
        // ITE true x y
        return RewriteResponse(REWRITE_AGAIN, n[1]);
      } else {
        Assert(n[0] == ff);
        // ITE false x y
        return RewriteResponse(REWRITE_AGAIN, n[2]);
      }
    } else if (n[1].isConst()) {
      if (n[1] == tt && n[2] == ff) {
        return RewriteResponse(REWRITE_AGAIN, n[0]);
      }
      else if (n[1] == ff && n[2] == tt) {
        return RewriteResponse(REWRITE_AGAIN, n[0].notNode());
      }
    }
    if (n[1] == n[2]) {
      return RewriteResponse(REWRITE_AGAIN, n[1]);
    // Curiously, this rewrite affects several benchmarks dramatically, including copy_array and some simple_startup - disable for now
    // } else if (n[0].getKind() == kind::NOT) {
    //   return RewriteResponse(REWRITE_AGAIN, n[0][0].iteNode(n[2], n[1]));
    } else if (n[0] == n[1]) {
      return RewriteResponse(REWRITE_AGAIN, n[0].iteNode(tt, n[2]));
    } else if (n[0] == n[2]) {
      return RewriteResponse(REWRITE_AGAIN, n[0].iteNode(n[1], ff));
    } else if (n[1].getKind() == kind::NOT && n[1][0] == n[0]) {
      return RewriteResponse(REWRITE_AGAIN, n[0].iteNode(ff, n[2]));
    } else if (n[2].getKind() == kind::NOT && n[2][0] == n[0]) {
      return RewriteResponse(REWRITE_AGAIN, n[0].iteNode(n[1], tt));
    }
    break;
  }
  default:
    return RewriteResponse(REWRITE_DONE, n);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
