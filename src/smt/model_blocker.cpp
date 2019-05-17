/*********************                                                        */
/*! \file model_blocker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utility for blocking models.
 **/

#include "smt/model_blocker.h"

#include "theory/quantifiers/term_util.h"
#include "expr/node.h"

using namespace CVC4::kind;

namespace CVC4 {

Expr ModelBlocker::getModelBlocker(const std::vector<Expr>& assertions,
                              Model* m)
{
  // convert to nodes
  std::vector<Node> tlAsserts;
  for (unsigned i = 0, size = assertions.size(); i < size; i++)
  {
    Node a = Node::fromExpr(assertions[i]);
    tlAsserts.push_back(a);
  }
  Trace("model-blocker") << "Compute model blocker, assertions:" << std::endl;
  // optimization: filter to only top-level disjunctions
  unsigned counter = 0;
  std::vector<Node> asserts;
  while( counter<tlAsserts.size() ){
    Node cur = tlAsserts[counter];
    counter++;
    Node catom = cur.getKind()==NOT ? cur[0] : cur;
    bool cpol = cur.getKind()!=NOT;
    if( catom.getKind()==NOT ){
      tlAsserts.push_back(catom[0]);
    }
    else if( catom.getKind()==AND && cpol )
    {
      for( const Node& c : catom ){
        tlAsserts.push_back(c);
      }
    }
    else if( theory::quantifiers::TermUtil::isBoolConnectiveTerm(catom) )
    {
      asserts.push_back(cur);
      Trace("model-blocker") << "  " << cur << std::endl;
    }
  }
  
  
  NodeManager* nm = NodeManager::currentNM();

  Node formula = asserts.size() > 1? nm->mkNode(AND, asserts) : asserts[0];
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction> implicant;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(formula);
  do 
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end()) 
    {
      visited[cur] = Node::null();
      Node catom = cur.getKind()==NOT ? cur[0] : cur;
      bool cpol = cur.getKind()!=NOT;
      // compute the implicant
      // impl is a formula that implies cur that is also satisfied by m
      Node impl;
      if( catom.getKind()==NOT )
      {
        // double negation
        impl = catom[0];
      }
      else if( catom.getKind()==OR || catom.getKind()==AND )
      {
        // if disjunctive
        if( (catom.getKind()==OR)==cpol )
        {
          // take the first literal that is satisfied
          for( Node n : catom )
          {
            // rewrite, this ensures that e.g. the propositional value of
            // quantified formulas can be queried
            n = theory::Rewriter::rewrite(n);
            Node vn = Node::fromExpr(m->getValue(n.toExpr()));
            Assert( vn.isConst() );
            if( vn.getConst<bool>()==cpol )
            {
              impl = cpol ? n : n.negate();
              break;
            }
          }
        }
        else if( catom.getKind()==OR )
        {
          // one step NNF
          std::vector< Node > children;
          for (const Node& cn : cur )
          {
            children.push_back(cn.negate());
          }
          impl = nm->mkNode( AND, children );
        }
      }
      else if( catom.getKind()==ITE )
      {
        Node vcond = Node::fromExpr(m->getValue(cur[0].toExpr()));
        Assert( vcond.isConst() );
        Node cond = cur[0];
        Node branch;
        if( vcond.getConst<bool>() )
        {
          branch = cur[1];
        }
        else
        {
          cond = cond.negate();
          branch = cur[2];
        }
        impl = nm->mkNode(AND, cond, cpol ? branch : branch.negate() );
      }
      else if( ( catom.getKind()==EQUAL && catom[0].getType().isBoolean() ) || catom.getKind()==XOR )
      {
        // based on how the children evaluate in the model
        std::vector< Node > children;
        for (const Node& cn : catom )
        {
          Node vn = Node::fromExpr(m->getValue(cn.toExpr()));
          Assert( vn.isConst() );
          children.push_back(vn.getConst<bool>() ? cn : cn.negate());
        }
        impl = nm->mkNode( AND, children );
      }
      else
      {
        // literals justified by themselves
        visited[cur] = cur;
      }
      if( visited[cur].isNull() )
      {
        visit.push_back(cur);
        if( impl.isNull() )
        {
          Assert( cur.getKind()==AND );
          for (const Node& cn : cur )
          {
            visit.push_back(cn);
          }
        }
        else
        {
          implicant[cur] = impl;
          visit.push_back(impl);
        }
      }
    } 
    else if (it->second.isNull()) 
    {
      Node ret = cur;
      it = implicant.find(cur);
      if( it!=implicant.end() )
      {
        Node impl = it->second;
        it = visited.find(impl);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        ret = it->second;
      }
      else
      {
        bool childChanged = false;
        std::vector<Node> children;
        // we never recurse to parameterized nodes
        Assert(cur.getMetaKind() != metakind::PARAMETERIZED);
        for (const Node& cn : cur )
        {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
        }
        if (childChanged) 
        {
          ret = nm->mkNode(cur.getKind(), children);
        }
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(formula) != visited.end());
  Assert(!visited.find(formula)->second.isNull());
  Node blocker = visited[formula].negate();
  Trace("model-blocker") << "...model blocker is " << blocker << std::endl;
  return blocker.toExpr();
}

} /* namespace CVC4 */
