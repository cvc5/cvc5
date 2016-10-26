/*********************                                                        */
/*! \file theory_sets_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory rewriter.
 **
 ** Sets theory rewriter.
 **/

#include "theory/sets/theory_sets_rewriter.h"
#include "theory/sets/normal_form.h"
#include "theory/sets/rels_utils.h"
#include "expr/attribute.h"
#include "options/sets_options.h"

namespace CVC4 {
namespace theory {
namespace sets {

typedef std::set<TNode> Elements;
typedef std::hash_map<TNode, Elements, TNodeHashFunction> SettermElementsMap;

struct FlattenedNodeTag {};
typedef expr::Attribute<FlattenedNodeTag, bool> flattened;


/**
 * flattenNode looks for children of same kind, and if found merges
 * them into the parent.
 *
 * It simultaneously handles a couple of other optimizations: 
 * - trivialNode - if found during exploration, return that node itself
 *    (like in case of OR, if "true" is found, makes sense to replace
 *     whole formula with "true")
 * - skipNode - as name suggests, skip them
 *    (like in case of OR, you may want to skip any "false" nodes found)
 *
 * Use a null node if you want to ignore any of the optimizations.
 */
RewriteResponse flattenNode(TNode n, TNode trivialNode, TNode skipNode)
{
  if(n.hasAttribute(flattened()) && n.getAttribute(flattened())) {
    return RewriteResponse(REWRITE_DONE, n);
  }

  typedef std::hash_set<TNode, TNodeHashFunction> node_set;

  node_set visited;
  visited.insert(skipNode);

  std::vector<TNode> toProcess;
  toProcess.push_back(n);

  Kind k = n.getKind();
  typedef std::vector<TNode> ChildList;
  ChildList childList;   //TNode should be fine, since 'n' is still there

  Debug("sets-rewrite-flatten") << "[sets-rewrite-flatten] " << n << std::endl;
  for (unsigned i = 0; i < toProcess.size(); ++ i) {
    TNode current = toProcess[i];
    Debug("sets-rewrite-flatten") << "[sets-rewrite-flatten]   > Processing " << current << std::endl;
    for(unsigned j = 0, j_end = current.getNumChildren(); j < j_end; ++ j) {
      TNode child = current[j];
      if(visited.find(child) != visited.end()) {
        continue;
      } else if(child == trivialNode) {
        return RewriteResponse(REWRITE_DONE, trivialNode);
      } else {
        visited.insert(child);
        if(child.getKind() == k) {
          toProcess.push_back(child);
        } else {
          childList.push_back(child);
        }
      }
    }
  }
  if (childList.size() == 0) return RewriteResponse(REWRITE_DONE, skipNode);
  if (childList.size() == 1) return RewriteResponse(REWRITE_AGAIN, childList[0]);

  sort(childList.begin(), childList.end());

  /* Make sure we are under number of children possible in a node */
  NodeManager* nodeManager = NodeManager::currentNM();
  static const unsigned MAX_CHILDREN = (1u << __CVC4__EXPR__NODE_VALUE__NBITS__NCHILDREN ) - 1;
  AlwaysAssert(childList.size() < MAX_CHILDREN, "do not support formulas this big");

  ChildList::iterator cur = childList.begin(), next, en = childList.end();
  Node ret = (*cur);
  ++cur;
  while( cur != en ) {
    ret = nodeManager->mkNode(k, ret, *cur);
    ret.setAttribute(flattened(), true);
    ++cur;
  }
  Trace("sets-postrewrite") << "flatten Sets::postRewrite returning " << ret << std::endl;
  if(ret != n) {
    return RewriteResponse(REWRITE_AGAIN, ret); // again for constants
  } else {
    return RewriteResponse(REWRITE_DONE, ret);
  }
  // if (childList.size() < MAX_CHILDREN) {
  //   Node retNode = nodeManager->mkNode(k, childList);
  //   return RewriteResponse(REWRITE_DONE, retNode);
  // } else {
  //   Assert(childList.size() < size_t(MAX_CHILDREN) * size_t(MAX_CHILDREN) );
  //   NodeBuilder<> nb(k);
  //   ChildList::iterator cur = childList.begin(), next, en = childList.end();
  //   while( cur != en ) {
  //     next = min(cur + MAX_CHILDREN, en);
  //     nb << (nodeManager->mkNode(k, ChildList(cur, next) ));
  //     cur = next;
  //   }
  //   return RewriteResponse(REWRITE_DONE, nb.constructNode());
  // }
}

bool checkConstantMembership(TNode elementTerm, TNode setTerm)
{
  if(setTerm.getKind() == kind::EMPTYSET) {
    return false;
  }

  if(setTerm.getKind() == kind::SINGLETON) {
    return elementTerm == setTerm[0];
  }

  Assert(setTerm.getKind() == kind::UNION && setTerm[1].getKind() == kind::SINGLETON,
         "kind was %d, term: %s", setTerm.getKind(), setTerm.toString().c_str());

  return
    elementTerm == setTerm[1][0] ||
    checkConstantMembership(elementTerm, setTerm[0]);
}

// static
RewriteResponse TheorySetsRewriter::postRewrite(TNode node) {
  NodeManager* nm = NodeManager::currentNM();
  Kind kind = node.getKind();


  if(node.isConst()) {
    // Dare you touch the const and mangle it to something else.
    return RewriteResponse(REWRITE_DONE, node);
  }

  switch(kind) {

  case kind::MEMBER: {
    if(node[0].isConst() && node[1].isConst()) {
      // both are constants
      TNode S = preRewrite(node[1]).node;
      bool isMember = checkConstantMembership(node[0], S);
      return RewriteResponse(REWRITE_DONE, nm->mkConst(isMember));
    }else if( node[1].getKind()==kind::EMPTYSET ){
      return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
    }else if( node[1].getKind()==kind::SINGLETON ){
      return RewriteResponse(REWRITE_AGAIN_FULL, nm->mkNode(kind::EQUAL, node[0], node[1][0] ) );
    }else if( node[1].getKind()==kind::UNION || node[1].getKind()==kind::INTERSECTION || node[1].getKind()==kind::SETMINUS ){
      std::vector< Node > children;
      for( unsigned i=0; i<node[1].getNumChildren(); i++ ){
        Node nc = nm->mkNode(kind::MEMBER, node[0], node[1][i] );
        if( node[1].getKind()==kind::SETMINUS && i==1 ){
          nc = nc.negate();
        }
        children.push_back( nc );
      }
      return RewriteResponse(REWRITE_AGAIN_FULL, nm->mkNode( node[1].getKind()==kind::UNION ? kind::OR : kind::AND, children ) );
    }
    break;
  }//kind::MEMBER

  case kind::SUBSET: {
    Assert(false, "TheorySets::postRrewrite(): Subset is handled in preRewrite.");

    // but in off-chance we do end up here, let us do our best

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
    } else if(node[0].isConst() && node[1].isConst()) {
      std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
      std::set<Node> newSet;
      std::set_difference(left.begin(), left.end(), right.begin(), right.end(),
        std::inserter(newSet, newSet.begin()));
      Node newNode = NormalForm::elementsToSet(newSet, node.getType());
      Assert(newNode.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    break;
  }//kind::SETMINUS

  case kind::INTERSECTION: {
    if(node[0] == node[1]) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
      return RewriteResponse(REWRITE_DONE, node[0]);
    } else if(node[0].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, node[0]);
    } else if(node[1].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, node[1]);
    } else if(node[0].isConst() && node[1].isConst()) {
      std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
      std::set<Node> newSet;
      std::set_intersection(left.begin(), left.end(), right.begin(), right.end(),
                            std::inserter(newSet, newSet.begin()));
      Node newNode = NormalForm::elementsToSet(newSet, node.getType());
      Assert(newNode.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    } else {
      std::vector< Node > els;
      NormalForm::getElementsFromBop( kind::INTERSECTION, node, els );
      std::sort( els.begin(), els.end() );
      Node rew = NormalForm::mkBop( kind::INTERSECTION, els, node.getType() );
      if( rew!=node ){
        Trace("sets-rewrite") << "Sets::rewrite " << node << " -> " << rew << std::endl;
      }
      return RewriteResponse(REWRITE_DONE, rew);
    }
    /*
    } else if (node[0] > node[1]) {
      Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    */
    break;
  }//kind::INTERSECION

  case kind::UNION: {
    // NOTE: case where it is CONST is taken care of at the top
    if(node[0] == node[1]) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
      return RewriteResponse(REWRITE_DONE, node[0]);
    } else if(node[0].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, node[1]);
    } else if(node[1].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, node[0]);
    } else if(node[0].isConst() && node[1].isConst()) {
      std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
      std::set<Node> newSet;
      std::set_union(left.begin(), left.end(), right.begin(), right.end(),
			  std::inserter(newSet, newSet.begin()));
      Node newNode = NormalForm::elementsToSet(newSet, node.getType());
      Assert(newNode.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    } else {
      std::vector< Node > els;
      NormalForm::getElementsFromBop( kind::UNION, node, els );
      std::sort( els.begin(), els.end() );
      Node rew = NormalForm::mkBop( kind::UNION, els, node.getType() );
      if( rew!=node ){
        Trace("sets-rewrite") << "Sets::rewrite " << node << " -> " << rew << std::endl;
      }
      return RewriteResponse(REWRITE_DONE, rew);
    }
    break;
  }//kind::UNION

  case kind::CARD: {
    if(node[0].isConst()) {
      std::set<Node> elements = NormalForm::getElementsFromNormalConstant(node[0]);
      return RewriteResponse(REWRITE_DONE, nm->mkConst(Rational(elements.size())));
    }else if( node[0].getKind()==kind::SINGLETON ){
      return RewriteResponse(REWRITE_DONE, nm->mkConst(Rational(1)));
    }else if( node[0].getKind()==kind::UNION ){
      Node ret = NodeManager::currentNM()->mkNode( kind::MINUS,
                   NodeManager::currentNM()->mkNode( kind::PLUS, NodeManager::currentNM()->mkNode( kind::CARD, node[0][0] ), 
                                                                 NodeManager::currentNM()->mkNode( kind::CARD, node[0][1] ) ),
                   NodeManager::currentNM()->mkNode( kind::CARD, NodeManager::currentNM()->mkNode( kind::INTERSECTION, node[0][0], node[0][1] ) ) );                                      
      return RewriteResponse(REWRITE_DONE, ret );
    }else if( node[0].getKind()==kind::SETMINUS ){
      Node ret = NodeManager::currentNM()->mkNode( kind::MINUS,
                   NodeManager::currentNM()->mkNode( kind::CARD, node[0][0] ),
                   NodeManager::currentNM()->mkNode( kind::CARD, NodeManager::currentNM()->mkNode( kind::INTERSECTION, node[0][0], node[0][1] ) ) );                                      
      return RewriteResponse(REWRITE_DONE, ret );
    }
  }
  case kind::TRANSPOSE: {
    if(node[0].getKind() == kind::TRANSPOSE) {
      return RewriteResponse(REWRITE_AGAIN, node[0][0]);
    }

    if(node[0].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, nm->mkConst(EmptySet(nm->toType(node.getType()))));
    } else if(node[0].isConst()) {
      std::set<Node> new_tuple_set;
      std::set<Node> tuple_set = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node>::iterator tuple_it = tuple_set.begin();

      while(tuple_it != tuple_set.end()) {
        new_tuple_set.insert(RelsUtils::reverseTuple(*tuple_it));
        tuple_it++;
      }
      Node new_node = NormalForm::elementsToSet(new_tuple_set, node.getType());
      Assert(new_node.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << new_node << std::endl;
      return RewriteResponse(REWRITE_DONE, new_node);

    }
    if(node[0].getKind() != kind::TRANSPOSE) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node << std::endl;
      return RewriteResponse(REWRITE_DONE, node);
    }
    break;
  }

  case kind::PRODUCT: {
    Trace("sets-rels-postrewrite") << "Sets::postRewrite processing " <<  node << std::endl;
    if( node[0].getKind() == kind::EMPTYSET ||
        node[1].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, nm->mkConst(EmptySet(nm->toType(node.getType()))));
    } else if( node[0].isConst() && node[1].isConst() ) {
      Trace("sets-rels-postrewrite") << "Sets::postRewrite processing **** " <<  node << std::endl;
      std::set<Node> new_tuple_set;
      std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
      std::set<Node>::iterator left_it = left.begin();
      int left_len = (*left_it).getType().getTupleLength();
      TypeNode tn = node.getType().getSetElementType();
      while(left_it != left.end()) {
        Trace("rels-debug") << "Sets::postRewrite processing left_it = " <<  *left_it << std::endl;
        std::vector<Node> left_tuple;
        left_tuple.push_back(Node::fromExpr(tn.getDatatype()[0].getConstructor()));
        for(int i = 0; i < left_len; i++) {
          left_tuple.push_back(RelsUtils::nthElementOfTuple(*left_it,i));
        }
        std::set<Node>::iterator right_it = right.begin();
        int right_len = (*right_it).getType().getTupleLength();
        while(right_it != right.end()) {
          Trace("rels-debug") << "Sets::postRewrite processing left_it = " <<  *right_it << std::endl;
          std::vector<Node> right_tuple;
          for(int j = 0; j < right_len; j++) {
            right_tuple.push_back(RelsUtils::nthElementOfTuple(*right_it,j));
          }
          std::vector<Node> new_tuple;
          new_tuple.insert(new_tuple.end(), left_tuple.begin(), left_tuple.end());
          new_tuple.insert(new_tuple.end(), right_tuple.begin(), right_tuple.end());
          Node composed_tuple = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, new_tuple);
          new_tuple_set.insert(composed_tuple);
          right_it++;
        }
        left_it++;
      }
      Node new_node = NormalForm::elementsToSet(new_tuple_set, node.getType());
      Assert(new_node.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << new_node << std::endl;
      return RewriteResponse(REWRITE_DONE, new_node);
    }
    break;
  }

  case kind::JOIN: {
    if( node[0].getKind() == kind::EMPTYSET ||
        node[1].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, nm->mkConst(EmptySet(nm->toType(node.getType()))));
    } else if( node[0].isConst() && node[1].isConst() ) {
      Trace("sets-rels-postrewrite") << "Sets::postRewrite processing " <<  node << std::endl;
      std::set<Node> new_tuple_set;
      std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
      std::set<Node>::iterator left_it = left.begin();
      int left_len = (*left_it).getType().getTupleLength();
      TypeNode tn = node.getType().getSetElementType();
      while(left_it != left.end()) {
        std::vector<Node> left_tuple;
        left_tuple.push_back(Node::fromExpr(tn.getDatatype()[0].getConstructor()));
        for(int i = 0; i < left_len - 1; i++) {
          left_tuple.push_back(RelsUtils::nthElementOfTuple(*left_it,i));
        }
        std::set<Node>::iterator right_it = right.begin();
        int right_len = (*right_it).getType().getTupleLength();
        while(right_it != right.end()) {
          if(RelsUtils::nthElementOfTuple(*left_it,left_len-1) == RelsUtils::nthElementOfTuple(*right_it,0)) {
            std::vector<Node> right_tuple;
            for(int j = 1; j < right_len; j++) {
              right_tuple.push_back(RelsUtils::nthElementOfTuple(*right_it,j));
            }
            std::vector<Node> new_tuple;
            new_tuple.insert(new_tuple.end(), left_tuple.begin(), left_tuple.end());
            new_tuple.insert(new_tuple.end(), right_tuple.begin(), right_tuple.end());
            Node composed_tuple = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, new_tuple);
            new_tuple_set.insert(composed_tuple);
          }
          right_it++;
        }
        left_it++;
      }
      Node new_node = NormalForm::elementsToSet(new_tuple_set, node.getType());
      Assert(new_node.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << new_node << std::endl;
      return RewriteResponse(REWRITE_DONE, new_node);
    }

    break;
  }

  case kind::TCLOSURE: {
    if(node[0].getKind() == kind::EMPTYSET) {
      return RewriteResponse(REWRITE_DONE, nm->mkConst(EmptySet(nm->toType(node.getType()))));
    } else if (node[0].isConst()) {
      std::set<Node> rel_mems = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> tc_rel_mems = RelsUtils::computeTC(rel_mems, node);
      Node new_node = NormalForm::elementsToSet(tc_rel_mems, node.getType());
      Assert(new_node.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << new_node << std::endl;
      return RewriteResponse(REWRITE_DONE, new_node);
      
    } else if(node[0].getKind() == kind::TCLOSURE) {
      return RewriteResponse(REWRITE_AGAIN, node[0]);
    } else if(node[0].getKind() != kind::TCLOSURE) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node << std::endl;
      return RewriteResponse(REWRITE_DONE, node);
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

  if(node.getKind() == kind::EQUAL) {

    if(node[0] == node[1]) {
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }

  }//kind::EQUAL
  else if(node.getKind() == kind::INSERT) {

    Node insertedElements = nm->mkNode(kind::SINGLETON, node[0]);
    size_t setNodeIndex =  node.getNumChildren()-1;
    for(size_t i = 1; i < setNodeIndex; ++i) {
      insertedElements = nm->mkNode(kind::UNION, 
				    insertedElements,
				    nm->mkNode(kind::SINGLETON, node[i]));
    }
    return RewriteResponse(REWRITE_AGAIN, 
			   nm->mkNode(kind::UNION,
				      insertedElements, 
				      node[setNodeIndex]));

  }//kind::INSERT
  else if(node.getKind() == kind::SUBSET) {

    // rewrite (A subset-or-equal B) as (A union B = B)
    return RewriteResponse(REWRITE_AGAIN,
                           nm->mkNode(kind::EQUAL,
                                      nm->mkNode(kind::UNION, node[0], node[1]),
                                      node[1]) );

  }//kind::SUBSET

  return RewriteResponse(REWRITE_DONE, node);
}

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
