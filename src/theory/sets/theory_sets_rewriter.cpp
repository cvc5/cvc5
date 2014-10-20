/*********************                                                        */
/*! \file theory_sets_rewriter.cpp
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sets theory rewriter.
 **
 ** Sets theory rewriter.
 **/

#include "theory/sets/theory_sets_rewriter.h"
#include "theory/sets/normal_form.h"

namespace CVC4 {
namespace theory {
namespace sets {

typedef std::set<TNode> Elements;
typedef std::hash_map<TNode, Elements, TNodeHashFunction> SettermElementsMap;

bool checkConstantMembership(TNode elementTerm, TNode setTerm)
{
  // Assume from pre-rewrite constant sets look like the following:
  // (union (setenum bla) (union (setenum bla) ... (union (setenum bla) (setenum bla) ) ... ))

  if(setTerm.getKind() == kind::EMPTYSET) {
    return false;
  }

  if(setTerm.getKind() == kind::SINGLETON) {
    return elementTerm == setTerm[0];
  }

  Assert(setTerm.getKind() == kind::UNION && setTerm[1].getKind() == kind::SINGLETON,
         "kind was %d, term: %s", setTerm.getKind(), setTerm.toString().c_str());

  return elementTerm == setTerm[1][0] || checkConstantMembership(elementTerm, setTerm[0]);

  // switch(setTerm.getKind()) {
  // case kind::EMPTYSET:
  //   return false;
  // case kind::SINGLETON:
  //   return elementTerm == setTerm[0];
  // case kind::UNION:
  //   return checkConstantMembership(elementTerm, setTerm[0]) ||
  //     checkConstantMembership(elementTerm, setTerm[1]);
  // case kind::INTERSECTION:
  //   return checkConstantMembership(elementTerm, setTerm[0]) &&
  //     checkConstantMembership(elementTerm, setTerm[1]);
  // case kind::SETMINUS:
  //   return checkConstantMembership(elementTerm, setTerm[0]) &&
  //     !checkConstantMembership(elementTerm, setTerm[1]);
  // default:
  //   Unhandled();
  // }
}

// static
RewriteResponse TheorySetsRewriter::postRewrite(TNode node) {
  NodeManager* nm = NodeManager::currentNM();
  Kind kind = node.getKind();

  switch(kind) {

  case kind::MEMBER: {
    if(node[0].isConst() && node[1].isConst()) {
      // both are constants
      TNode S = preRewrite(node[1]).node;
      bool isMember = checkConstantMembership(node[0], S);
      return RewriteResponse(REWRITE_DONE, nm->mkConst(isMember));
    }
    break;
  }//kind::MEMBER

  case kind::SUBSET: {
    // rewrite (A subset-or-equal B) as (A union B = B)
    TNode A = node[0];
    TNode B = node[1];
    return RewriteResponse(REWRITE_AGAIN_FULL,
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
  }//kind::IFF

  case kind::SETMINUS: {
    if(node[0] == node[1]) {
      Node newNode = nm->mkConst(EmptySet(nm->toType(node[0].getType())));
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    } else if(node[0].getKind() == kind::EMPTYSET ||
              node[1].getKind() == kind::EMPTYSET) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
      return RewriteResponse(REWRITE_DONE, node[0]);
    }
    break;
  }//kind::INTERSECION

  case kind::INTERSECTION: {
    if(node[0] == node[1]) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
      return RewriteResponse(REWRITE_DONE, node[0]);
    } else if(node[0].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, node[0]);
    } else if(node[1].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, node[1]);
    } else if (node[0] > node[1]) {
      Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    break;
  }//kind::INTERSECION

  case kind::UNION: {
    if(node[0] == node[1]) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
      return RewriteResponse(REWRITE_DONE, node[0]);
    } else if(node[0].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, node[1]);
    } else if(node[1].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, node[0]);
    } else if (node[0] > node[1]) {
      Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    break;
  }//kind::UNION

  default:
    break;
  }//switch(node.getKind())

  // This default implementation
  return RewriteResponse(REWRITE_DONE, node);
}

const Elements& collectConstantElements(TNode setterm, SettermElementsMap& settermElementsMap) {
  SettermElementsMap::const_iterator it = settermElementsMap.find(setterm);
  if(it == settermElementsMap.end() ) {

    Kind k = setterm.getKind();
    unsigned numChildren = setterm.getNumChildren();
    Elements cur;
    if(numChildren == 2) {
      const Elements& left = collectConstantElements(setterm[0], settermElementsMap);
      const Elements& right = collectConstantElements(setterm[1], settermElementsMap);
      switch(k) {
      case kind::UNION:
        if(left.size() >= right.size()) {
          cur = left; cur.insert(right.begin(), right.end());
        } else {
          cur = right; cur.insert(left.begin(), left.end());
        }
        break;
      case kind::INTERSECTION:
        std::set_intersection(left.begin(), left.end(), right.begin(), right.end(),
                              std::inserter(cur, cur.begin()) );
        break;
      case kind::SETMINUS:
        std::set_difference(left.begin(), left.end(), right.begin(), right.end(),
                            std::inserter(cur, cur.begin()) );
        break;
      default:
        Unhandled();
      }
    } else {
      switch(k) {
      case kind::EMPTYSET:
        /* assign emptyset, which is default */
        break;
      case kind::SINGLETON:
        Assert(setterm[0].isConst());
        cur.insert(TheorySetsRewriter::preRewrite(setterm[0]).node);
        break;
      default:
        Unhandled();
      }
    }
    Debug("sets-rewrite-constant") << "[sets-rewrite-constant] "<< setterm << " " << setterm.getId() << std::endl;

    it = settermElementsMap.insert(SettermElementsMap::value_type(setterm, cur)).first;
  }
  return it->second;
}


// static
RewriteResponse TheorySetsRewriter::preRewrite(TNode node) {
  NodeManager* nm = NodeManager::currentNM();

  // do nothing
  if(node.getKind() == kind::EQUAL && node[0] == node[1])
    return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
  // Further optimization, if constants but differing ones

  if(node.getKind() == kind::INSERT) {
    Node insertedElements = nm->mkNode(kind::SINGLETON, node[0]);
    size_t setNodeIndex =  node.getNumChildren()-1;
    for(size_t i = 1; i < setNodeIndex; ++i) {
      insertedElements = nm->mkNode(kind::UNION, insertedElements, nm->mkNode(kind::SINGLETON, node[i]));
    }
    return RewriteResponse(REWRITE_AGAIN, nm->mkNode(kind::UNION, insertedElements, node[setNodeIndex]));
  }//kind::INSERT

  if(node.getType().isSet() && node.isConst()) {
    //rewrite set to normal form
    SettermElementsMap setTermElementsMap;   // cache
    const Elements& elements = collectConstantElements(node, setTermElementsMap);
    RewriteResponse response(REWRITE_DONE, NormalForm::elementsToSet(elements, node.getType()));
    Debug("sets-rewrite-constant") << "[sets-rewrite-constant] Rewriting " << node << std::endl
                                   << "[sets-rewrite-constant]        to " << response.node << std::endl;
    return response;
  }

  return RewriteResponse(REWRITE_DONE, node);
}

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
