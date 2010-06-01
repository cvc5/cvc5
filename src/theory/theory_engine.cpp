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
  Node cachedRewrite;
  NodeManager *nodeManager = NodeManager::currentNM();
  if(nodeManager->getAttribute(node, theory::IteRewriteAttr(), cachedRewrite)) {
    return cachedRewrite.isNull() ? Node(node) : cachedRewrite;
  }

  if(node.getKind() == kind::ITE){
    Assert( node.getNumChildren() == 3 );
    TypeNode nodeType = node[1].getType();
    if(!nodeType.isBoolean()){

      Node skolem = nodeManager->mkVar(node.getType());
      Node newAssertion =
        nodeManager->mkNode(
                            kind::ITE,
                            node[0],
                            nodeManager->mkNode(kind::EQUAL, skolem, node[1]),
                            nodeManager->mkNode(kind::EQUAL, skolem, node[2]));
      nodeManager->setAttribute(node, theory::IteRewriteAttr(), skolem);

      if(debugTagIsOn("ite")){
        Debug("ite") << "removeITEs([" << node.getId() << "," << node << "])"
                     << "->"
                     << "["<<newAssertion.getId() << "," << newAssertion << "]"
                     << endl;
      }

      Node preprocessed = rewrite(newAssertion);
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

    cachedRewrite = nodeManager->mkNode(node.getKind(), newChildren);
    nodeManager->setAttribute(node, theory::IteRewriteAttr(), cachedRewrite);
    return cachedRewrite;
  } else {
    nodeManager->setAttribute(node, theory::IteRewriteAttr(), Node::null());
    return node;
  }

}

Node blastDistinct(TNode in){
  Assert(in.getKind() == kind::DISTINCT);
  if(in.getNumChildren() == 2){
    //If this is the case exactly 1 != pair will be generated so the AND is not required
    Node eq = NodeManager::currentNM()->mkNode(CVC4::kind::EQUAL, in[0], in[1]);
    Node neq = NodeManager::currentNM()->mkNode(CVC4::kind::NOT, eq);
    return neq;
  }
  //Assume that in.getNumChildren() > 2
  // => diseqs.size() > 1
  vector<Node> diseqs;
  for(TNode::iterator i = in.begin(); i != in.end(); ++i) {
    TNode::iterator j = i;
    while(++j != in.end()) {
      Node eq = NodeManager::currentNM()->mkNode(CVC4::kind::EQUAL, *i, *j);
      Node neq = NodeManager::currentNM()->mkNode(CVC4::kind::NOT, eq);
      diseqs.push_back(neq);
    }
  }
  Node out = NodeManager::currentNM()->mkNode(CVC4::kind::AND, diseqs);
  return out;
}

Node TheoryEngine::rewrite(TNode in) {
  if(inRewriteCache(in)) {
    return getRewriteCache(in);
  }

  if(in.getMetaKind() == kind::metakind::VARIABLE) {
    return in;
  }

  Node intermediate = removeITEs(in);

  // these special cases should go away when theory rewriting comes online
  if(intermediate.getKind() == kind::DISTINCT) {
    Node out = blastDistinct(intermediate);
    //setRewriteCache(intermediate, out);
    return rewrite(out); //TODO let this fall through?
  }

  theory::Theory* thy = theoryOf(intermediate);
  if(thy == NULL) {
    Node out = rewriteBuiltins(intermediate);
    //setRewriteCache(intermediate, out);
    return out;
  } else if(thy != &d_bool){
    Node out = thy->rewrite(intermediate);
    //setRewriteCache(intermediate, out);
    return out;
  }else{
    Node out = rewriteChildren(intermediate);
    //setRewriteCache(intermediate, out);
    return out;
  }

  Unreachable();
}

}/* CVC4 namespace */
