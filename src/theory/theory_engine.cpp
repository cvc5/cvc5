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

struct IteRewriteTag {};
typedef expr::Attribute<IteRewriteTag, Node> IteRewriteAttr;

}/* CVC4::theory namespace */

Node TheoryEngine::preprocess(TNode t) {
  Node top = rewrite(t);
  Debug("rewrite") << "rewrote: " << t << endl << "to     : " << top << endl;

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
  /* Our goal is to tease out any ITE's sitting under a theory operator. */
Node TheoryEngine::removeITEs(TNode node) {
  Debug("ite") << "handleNonAtomicNode(" << node << ")" << endl;

  /* The result may be cached already */
  Node rewrite;
  NodeManager *nodeManager = NodeManager::currentNM();
  if(nodeManager->getAttribute(node, theory::IteRewriteAttr(), rewrite)) {
    return rewrite.isNull() ? Node(node) : rewrite;
  }

  if(node.getKind() == kind::ITE){
    if(theoryOf(node[1]) != &d_bool && node[1].getKind() != kind::EQUAL) {
      Assert( node.getNumChildren() == 3 );

      Debug("ite") << theoryOf(node[1]) << " " << &d_bool <<endl;

      Node skolem = nodeManager->mkVar(node.getType());
      Node newAssertion =
        nodeManager->mkNode(
                            kind::ITE,
                            node[0],
                            nodeManager->mkNode(kind::EQUAL, skolem, node[1]),
                            nodeManager->mkNode(kind::EQUAL, skolem, node[2]));
      nodeManager->setAttribute(node, theory::IteRewriteAttr(), skolem);

      Node preprocessed = preprocess(newAssertion);
      d_propEngine->assertFormula(preprocessed);

      return skolem;
    }
  }
  std::vector<Node> newChildren;
  bool somethingChanged = false;
  for(TNode::const_iterator it = node.begin(), end = node.end(); it != end; ++it) {
    Node newChild = removeITEs(*it);
    somethingChanged |= (newChild != *it);
    newChildren.push_back(newChild);
  }

  if(somethingChanged) {

    rewrite = nodeManager->mkNode(node.getKind(), newChildren);
    nodeManager->setAttribute(node, theory::IteRewriteAttr(), rewrite);
    return rewrite;
  } else {
    nodeManager->setAttribute(node, theory::IteRewriteAttr(), Node::null());
    return node;
  }

}

Node TheoryEngine::rewrite(TNode in) {
  if(inRewriteCache(in)) {
    return getRewriteCache(in);
  }

  if(in.getMetaKind() == kind::metakind::VARIABLE) {
    return in;
  }

  in = removeITEs(in);

  // these special cases should go away when theory rewriting comes online
  if(in.getKind() == kind::DISTINCT) {
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
  }

  theory::Theory* thy = theoryOf(in);
  if(thy == NULL) {
    Node out = rewriteBuiltins(in);
    //setRewriteCache(in, out);
    return in;
  } else if(thy != &d_bool){
    Node out = thy->rewrite(in);
    //setRewriteCache(in, out);
    return out;
  }else{
    Node out = rewriteChildren(in);
    setRewriteCache(in, out);
    return out;
  }

  Unreachable();
}

}/* CVC4 namespace */
