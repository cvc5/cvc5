/*********************                                                        */
/*! \file ite_removal.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Removal of term ITEs
 **
 ** Removal of term ITEs.
 **/

#include <vector>

#include "util/ite_removal.h"
#include "theory/rewriter.h"
#include "expr/command.h"

using namespace CVC4;
using namespace std;

namespace CVC4 {

struct IteRewriteAttrTag {};
typedef expr::Attribute<IteRewriteAttrTag, Node> IteRewriteAttr;

void RemoveITE::run(std::vector<Node>& output, IteSkolemMap& iteSkolemMap)
{
  for (unsigned i = 0, i_end = output.size(); i < i_end; ++ i) {
    output[i] = run(output[i], output, iteSkolemMap);
  }
}

Node RemoveITE::run(TNode node, std::vector<Node>& output,
                    IteSkolemMap& iteSkolemMap) {
  // Current node
  Debug("ite") << "removeITEs(" << node << ")" << endl;

  // The result may be cached already
  Node cachedRewrite;
  NodeManager *nodeManager = NodeManager::currentNM();
  if(nodeManager->getAttribute(node, IteRewriteAttr(), cachedRewrite)) {
    Debug("ite") << "removeITEs: in-cache: " << cachedRewrite << endl;
    return cachedRewrite.isNull() ? Node(node) : cachedRewrite;
  }

  // If an ITE replace it
  if(node.getKind() == kind::ITE) {
    TypeNode nodeType = node.getType();
    if(!nodeType.isBoolean()) {
      // Make the skolem to represent the ITE
      Node skolem = nodeManager->mkSkolem("termITE_$$", nodeType, "a variable introduced due to term-level ITE removal");

      // The new assertion
      Node newAssertion =
        nodeManager->mkNode(kind::ITE, node[0], skolem.eqNode(node[1]),
                            skolem.eqNode(node[2]));
      Debug("ite") << "removeITEs(" << node << ") => " << newAssertion << endl;

      // Attach the skolem
      nodeManager->setAttribute(node, IteRewriteAttr(), skolem);

      // Remove ITEs from the new assertion, rewrite it and push it to the output
      newAssertion = run(newAssertion, output, iteSkolemMap);
      iteSkolemMap[skolem] = output.size();
      output.push_back(newAssertion);

      // The representation is now the skolem
      return skolem;
    }
  }

  // If not an ITE, go deep
  if( node.getKind() != kind::FORALL &&
      node.getKind() != kind::EXISTS &&
      node.getKind() != kind::REWRITE_RULE ) {
    vector<Node> newChildren;
    bool somethingChanged = false;
    if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
      newChildren.push_back(node.getOperator());
    }
    // Remove the ITEs from the children
    for(TNode::const_iterator it = node.begin(), end = node.end(); it != end; ++it) {
      Node newChild = run(*it, output, iteSkolemMap);
      somethingChanged |= (newChild != *it);
      newChildren.push_back(newChild);
    }

    // If changes, we rewrite
    if(somethingChanged) {
      cachedRewrite = nodeManager->mkNode(node.getKind(), newChildren);
      nodeManager->setAttribute(node, IteRewriteAttr(), cachedRewrite);
      return cachedRewrite;
    } else {
      nodeManager->setAttribute(node, IteRewriteAttr(), Node::null());
      return node;
    }
  } else {
    nodeManager->setAttribute(node, IteRewriteAttr(), Node::null());
    return node;
  }
}

}/* CVC4 namespace */
