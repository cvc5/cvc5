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
    if( options::setsAggRewrite() ){
      Node newNode = rewriteSet( node );
      if( newNode!=node ){
        return RewriteResponse(REWRITE_DONE, newNode);
      }
    }else{
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
    }
    break;
  }//kind::SETMINUS

  case kind::INTERSECTION: {
    if( options::setsAggRewrite() ){
      Node newNode = rewriteSet( node );
      if( newNode!=node ){
        return RewriteResponse(REWRITE_DONE, newNode);
      }
    // }else{
    //   Node emptySet = nm->mkConst(EmptySet(nm->toType(node[0].getType())));
    //   if(node[0].isConst() && node[1].isConst()) {
    //     std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
    //     std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
    //     std::set<Node> newSet;
    //     std::set_intersection(left.begin(), left.end(), right.begin(), right.end(),
    //             std::inserter(newSet, newSet.begin()));
    //     Node newNode = NormalForm::elementsToSet(newSet, node.getType());
    //     Assert(newNode.isConst());
    //     Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
    //     return RewriteResponse(REWRITE_DONE, newNode);
    //   } else {
    //     return flattenNode(node, /* trivialNode = */ emptySet, /* skipNode = */ Node());
    //   }
    // }
    }else{
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
      } else if (node[0] > node[1]) {
        Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
        Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
        return RewriteResponse(REWRITE_DONE, newNode);
      }
    }
    break;
  }//kind::INTERSECION

  case kind::UNION: {
    // NOTE: case where it is CONST is taken care of at the top
    if( options::setsAggRewrite() ){
      Node newNode = rewriteSet( node );
      if( newNode!=node ){
        return RewriteResponse(REWRITE_DONE, newNode);
      }
    }else if(node[0] == node[1]) {
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
    }else if (node[0] > node[1]) {
      Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    break;
  }//kind::UNION

  case kind::CARD: {
    if(node[0].isConst()) {
      std::set<Node> elements = NormalForm::getElementsFromNormalConstant(node[0]);
      return RewriteResponse(REWRITE_DONE, nm->mkConst(Rational(elements.size())));
    }
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

Node TheorySetsRewriter::rewriteSet( Node s ) {
  Trace("sets-rewrite-debug") << "Rewrite set : " << s << std::endl;
  Node empSet = NodeManager::currentNM()->mkConst(EmptySet(NodeManager::currentNM()->toType(s.getType())));
  bool success;
  do{
    success = false;
    std::map< Node, bool > ca;
    Node ss = rewriteSet( s, ca, empSet );
    if( ss!=s ){
      Assert( !ss.isNull() );
      Trace("sets-rewrite") << "Rewrite set : " << s << std::endl;
      Trace("sets-rewrite") << "........got : " << ss << std::endl;
      success = true;
      s = ss;
    }
  }while( success );
  return s;
}

Node TheorySetsRewriter::rewriteSet( Node s, std::map< Node, bool >& ca, Node empSet ) {
  if( s.getKind()!=kind::UNION && s.getKind()!=kind::INTERSECTION && s.getKind()!=kind::SETMINUS ){
    std::map< Node, bool >::iterator it = ca.find( s );
    if( it==ca.end() ){
      return s;
    }else if( it->second ){
      return Node::null();
    }else{
      return empSet;
    }
  }else{
    Trace("sets-rewrite-debug") << "Get components : " << s << std::endl;
    std::map< Node, bool > c;
    bool pol = s.getKind()!=kind::UNION;
    if( pol ){
      //copy current components
      for( std::map< Node, bool >::iterator it = ca.begin(); it != ca.end(); ++it ){
        c[it->first] = it->second;
      }
    }
    if( collectSetComponents( s, c, pol ) ){
      if( Trace.isOn("sets-rewrite-debug") ){
        Trace("sets-rewrite-debug") << "  got components : " << std::endl;
        for( std::map< Node, bool >::iterator it = c.begin(); it != c.end(); ++it ){
          Trace("sets-rewrite-debug") << "    " << it->first << " -> " << it->second << std::endl;
        }
      }
      
      //simplify components based on what is asserted in ca, recursively
      std::map< Node, bool > nc;
      if( pol ){
        //copy map
        for( std::map< Node, bool >::iterator it = c.begin(); it != c.end(); ++it ){
          nc[it->first] = it->second;
        }
        //rewrite each new component based on current assertions
        for( std::map< Node, bool >::iterator it = c.begin(); it != c.end(); ++it ){
          if( ca.find( it->first )==ca.end() ){
            nc.erase( it->first );
            Node prev = it->first;
            //only rewrite positive components here
            Node ss = it->second ? rewriteSet( it->first, nc, empSet ) : it->first;
            if( prev!=ss ){
              Trace("sets-rewrite-debug") << "  simplify component : " << prev << "..." << ss << std::endl;
            }
            if( ss==empSet ){
              Trace("sets-rewrite-debug") << "  return singularity " << ss << std::endl;
              return ss;
            }else if( !ss.isNull() ){
              std::map< Node, bool >::iterator itc = nc.find( ss );
              if( itc==nc.end() ){
                nc[ss] = it->second;
              }else if( it->second!=itc->second ){
                Trace("sets-rewrite-debug") << "...conflict, return empty set." << std::endl;
                return empSet;
              }
            }
          }
        }
      }else{
        for( std::map< Node, bool >::iterator it = c.begin(); it != c.end(); ++it ){
          Node prev = it->first;
          Node ss = rewriteSet( it->first, ca, empSet );
          if( prev!=ss ){
            Trace("sets-rewrite-debug") << "  simplify component : " << prev << "..." << ss << std::endl;
          }
          if( ss.isNull() ){
            Trace("sets-rewrite-debug") << "  return singularity " << ss << std::endl;
            return ss;
          }else if( ss!=empSet ){
            std::map< Node, bool >::iterator itc = nc.find( ss );
            if( itc==nc.end() ){
              nc[ss] = it->second;
            }else if( it->second!=itc->second ){
                Trace("sets-rewrite-debug") << "...conflict, return complete set." << std::endl;
              return Node::null();
            }
          }
        }
      }

      
      //construct sorted lists of positive, negative components
      std::vector< Node > comp[2];
      for( std::map< Node, bool >::iterator it = nc.begin(); it != nc.end(); ++it ){
        if( !pol || ca.find( it->first )==ca.end() ){
          comp[ ( it->second==pol ) ? 0 : 1 ].push_back( it->first );
        }
      }
      //construct normalized set
      Node curr;
      for( unsigned i=0; i<2; i++ ){
        if( comp[i].size()>1 ){
          std::sort( comp[i].begin(), comp[i].end() );
        }
        if( i==0 ){
          if( comp[i].empty() ){
            Trace("sets-rewrite-debug") << "...return trivial set (no components)." << std::endl;
            if( pol ){
              return Node::null();
            }else{
              return empSet;
            }
          }else{
            curr = comp[i][0];
            for( unsigned j=1; j<comp[i].size(); j++ ){
              curr = NodeManager::currentNM()->mkNode( pol ? kind::INTERSECTION : kind::UNION, curr, comp[i][j] );
            }
          }
        }else if( i==1 ){
          if( !comp[i].empty() ){
            Assert( pol );
            Node rem = comp[i][0];
            for( unsigned j=1; j<comp[i].size(); j++ ){
              rem = NodeManager::currentNM()->mkNode( kind::UNION, rem, comp[i][j] );
            }
            curr = NodeManager::currentNM()->mkNode( kind::SETMINUS, curr, rem );
          }
        }
      }
      Trace("sets-rewrite-debug") << "...return " << curr << std::endl;
      return curr;
    }else{
      if( pol ){
        Trace("sets-rewrite-debug") << "...return empty set." << std::endl;
        return NodeManager::currentNM()->mkConst(EmptySet(NodeManager::currentNM()->toType(s.getType())));
      }else{
        Trace("sets-rewrite-debug") << "...return complete set." << std::endl;
        return Node::null();
      }
    }
  }
}

bool TheorySetsRewriter::collectSetComponents( Node n, std::map< Node, bool >& c, bool pol ) {
  std::map< Node, bool >::iterator itc = c.find( n );
  if( itc!=c.end() ){
    if( itc->second!=pol ){
      return false;
    }
  }else{
    if( ( pol && ( n.getKind()==kind::INTERSECTION || n.getKind()==kind::SETMINUS ) ) || ( !pol && n.getKind()==kind::UNION ) ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        bool newPol = ( i==1 && n.getKind()==kind::SETMINUS ) ? !pol : pol;
        if( !collectSetComponents( n[i], c, newPol ) ){
          return false;
        }
      }
    }else{
      c[n] = pol;
    }
  }
  return true;
}

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
