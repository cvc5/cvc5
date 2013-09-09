#include "theory/sets/theory_sets_rewriter.h"

namespace CVC4 {
namespace theory {
namespace sets {

bool checkConstantMembership(TNode elementTerm, TNode setTerm)
{
  switch(setTerm.getKind()) {
  case kind::EMPTYSET:
    return false;
  case kind::SET_SINGLETON:
    return elementTerm == setTerm[0];
  case kind::UNION:
    return checkConstantMembership(elementTerm, setTerm[0]) ||
      checkConstantMembership(elementTerm, setTerm[1]);
  case kind::INTERSECTION:
    return checkConstantMembership(elementTerm, setTerm[0]) &&
      checkConstantMembership(elementTerm, setTerm[1]);
  case kind::SETMINUS:
    return checkConstantMembership(elementTerm, setTerm[0]) &&
      !checkConstantMembership(elementTerm, setTerm[1]);
  default:
    Unhandled();
  }
}

// static
RewriteResponse TheorySetsRewriter::postRewrite(TNode node) {
  NodeManager* nm = NodeManager::currentNM();

  switch(node.getKind()) {

  case kind::IN: {
    if(!node[0].isConst() || !node[1].isConst())
      break;

    // both are constants
    bool isMember = checkConstantMembership(node[0], node[1]);
    return RewriteResponse(REWRITE_DONE, nm->mkConst(isMember));
  }

  case kind::SUBSET: {
    // rewrite (A subset-or-equal B) as (A union B = B)
    TNode A = node[0];
    TNode B = node[1];
    return RewriteResponse(REWRITE_AGAIN,
                           nm->mkNode(kind::EQUAL,
                                      nm->mkNode(kind::UNION, A, B),
                                      B) );
  }//kind::SUBSET

  case kind::EQUAL:
  case kind::IFF: {
    //rewrite: t = t with true (t term)
    //rewrite: c = c' with c different from c' false (c, c' constants)
    //otherwise: sort them
    if(node[0] == node[1]) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning true" << std::endl;
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }
    else if (node[0].isConst() && node[1].isConst()) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning false" << std::endl;
      return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
    }
    else if (node[0] > node[1]) {
      Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    break;
  }

  case kind::UNION:
  case kind::INTERSECTION: {
    if(node[0] == node[1]) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
      return RewriteResponse(REWRITE_DONE, node[0]);
    } else if (node[0] > node[1]) {
      Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    break;
  }

  default:
    break;

  }//switch(node.getKind())

  // This default implementation
  return RewriteResponse(REWRITE_DONE, node);
}

// static
RewriteResponse TheorySetsRewriter::preRewrite(TNode node) {
  NodeManager* nm = NodeManager::currentNM();

  // do nothing
  if(node.getKind() == kind::EQUAL && node[0] == node[1])
    return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
  // Further optimization, if constants but differing ones

  return RewriteResponse(REWRITE_DONE, node);
}

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
