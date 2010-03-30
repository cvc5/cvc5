/*********************                                                        */
/** theory_engine.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** The theory engine.
 **/

#include "theory/theory_engine.h"
#include "expr/node.h"
#include "expr/attribute.h"

#include <list>

using namespace std;

namespace CVC4 {

namespace theory {

struct PreRegisteredTag {};
typedef expr::Attribute<PreRegisteredTag, bool> PreRegistered;

}/* CVC4::theory namespace */

Node TheoryEngine::preprocess(TNode t) {
  Node top = rewrite(t);
  Debug("rewrite") << "rewrote: " << t << "\nto     : " << top << "\n";
  return top;

  list<TNode> toReg;
  toReg.push_back(top);

  /* Essentially this is doing a breadth-first numbering of
   * non-registered subterms with children.  Any non-registered
   * leaves are immediately registered. */
  for(list<TNode>::iterator workp = toReg.begin();
      workp != toReg.end();
      ++workp) {

    TNode n = *workp;

    for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
      TNode c = *i;

      if(!c.getAttribute(theory::PreRegistered())) {// c not yet registered
        if(c.getNumChildren() == 0) {
          c.setAttribute(theory::PreRegistered(), true);
          theoryOf(c)->preRegisterTerm(c);
        } else {
          toReg.push_back(c);
        }
      }
    }
  }

  /* Now register the list of terms in reverse order.  Between this
   * and the above registration of leaves, this should ensure that
   * all subterms in the entire tree were registered in
   * reverse-topological order. */
  for(std::list<TNode>::reverse_iterator i = toReg.rbegin();
      i != toReg.rend();
      ++i) {

    TNode n = *i;

    /* Note that a shared TNode in the DAG rooted at "fact" could
     * appear twice on the list, so we have to avoid hitting it
     * twice. */
    // FIXME when ExprSets are online, use one of those to avoid
    // duplicates in the above?
    if(!n.getAttribute(theory::PreRegistered())) {
      n.setAttribute(theory::PreRegistered(), true);
      theoryOf(n)->preRegisterTerm(n);
    }
  }

  return top;
}

Node TheoryEngine::rewrite(TNode in) {
  if(inRewriteCache(in)) {
    return getRewriteCache(in);
  }

  if(in.getMetaKind() == kind::metakind::VARIABLE) {
    return in;
  }

  /*
    theory::Theory* thy = theoryOf(in);
    if(thy == NULL) {
    Node out = rewriteBuiltins(in);
    setRewriteCache(in, out);
    return in;
    } else {
    Node out = thy->rewrite(in);
    setRewriteCache(in, out);
    return out;
    }
  */

  // these special cases should go away when theory rewriting comes online
  if(in.getKind() == kind::EQUAL) {
    Assert(in.getNumChildren() == 2);
    if(in[0] == in[1]) {
      Node out = NodeManager::currentNM()->mkNode(kind::TRUE);
      //setRewriteCache(in, out);
      return out;
    }
  } else if(in.getKind() == kind::DISTINCT) {
    vector<Node> diseqs;
    for(TNode::iterator i = in.begin(); i != in.end(); ++i) {
      TNode::iterator j = i;
      while(++j != in.end()) {
        Node eq = NodeManager::currentNM()->mkNode(CVC4::kind::EQUAL, *i, *j);
        Node neq = NodeManager::currentNM()->mkNode(CVC4::kind::NOT, eq);
        diseqs.push_back(neq);
      }
    }
    Node out =
      diseqs.size() == 1
      ? diseqs[0]
      : NodeManager::currentNM()->mkNode(CVC4::kind::AND, diseqs);
    //setRewriteCache(in, out);
    return out;
  } else {
    Node out = rewriteChildren(in);
    //setRewriteCache(in, out);
    return out;
  }

  //setRewriteCache(in, in);
  return in;
}

}/* CVC4 namespace */
