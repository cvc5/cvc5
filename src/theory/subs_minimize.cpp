/*********************                                                        */
/*! \file subs_minimize.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of subs_minimize
 **/

#include "theory/subs_minimize.h"

#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

SubstitutionMinimize::SubstitutionMinimize() {}

bool SubstitutionMinimize::find(Node n,
                                Node target,
                                const std::vector<Node>& vars,
                                const std::vector<Node>& subs,
                                std::vector<Node>& reqVars)
{
  NodeManager* nm = NodeManager::currentNM();

  std::map< Node, std::unordered_set< Node, NodeHashFunction > > fvDepend;
  
  // the value of each subterm in n under the substitution
  std::unordered_map<TNode, Node, TNodeHashFunction> value;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = value.find(cur);

    if (it == value.end())
    {
      if (cur.isVar())
      {
        const std::vector<Node>::const_iterator& it =
            std::find(vars.begin(), vars.end(), cur);
        if (it == vars.end())
        {
          value[cur] = cur;
        }
        else
        {
          ptrdiff_t pos = std::distance(vars.begin(), it);
          value[cur] = subs[pos];
        }
      }
      else
      {
        value[cur] = Node::null();
        visit.push_back(cur);
        if (cur.getKind()==APPLY_UF)
        {
          visit.push_back(cur.getOperator());
        }
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      std::vector<Node> children;
      std::vector<Node> vchildren;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        if( cur.getKind()==APPLY_UF )
        {
          children.push_back(cur.getOperator());
        }
        else
        {
          vchildren.push_back(cur.getOperator());
        }
      }
      for (const Node& cn : cur)
      {
        children.push_back(cn);
      }
      for (const Node& cn : children)
      {
        it = value.find(cn);
        Assert(it != value.end());
        Assert(!it->second.isNull());
        vchildren.push_back(it->second);
      }
      ret = nm->mkNode(cur.getKind(), vchildren);
      ret = Rewriter::rewrite(ret);
      value[cur] = ret;
    }
  } while (!visit.empty());
  Assert(value.find(n) != value.end());
  Assert(!value.find(n)->second.isNull());
  
  if(n!=target)
  {
    return false;
  }
  
  
  std::unordered_set< Node, NodeHashFunction > rlvFv;
  // only variables that occur in assertions are relevant
  std::map< Node, unsigned > iteBranch;
  std::map< Node, std::vector< unsigned > > justifyArgs;
  
  visit.push_back(n);
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator itv;
  do {
    cur = visit.back();
    visit.pop_back();
    itv = visited.find(cur);
    if (itv == visited.end()) {
      if( cur.isVar() )
      {
        visited[cur] = true;
        if( value[cur]!=cur )
        {
          // must include
          rlvFv.insert(cur);
        }
      }
      else if( cur.getKind()==ITE )
      {
        visited[cur] = false;
        // only recurse on relevant branch
        Node bval = value[cur[0]];
        Assert( !bval.isNull() && bval.isConst() );
        unsigned cindex = bval.getConst<bool>() ? 1 : 2;
        visit.push_back(cur[0]);
        visit.push_back(cur[cindex]);
      }
      else if( cur.getNumChildren()>0 )
      {
        visited[cur] = false;
        // if the operator is a variable, expand first
        if( cur.getKind()==APPLY_UF )
        {
          // TODO
        }
      
        // see if there are any arguments that fully justify the evaluation
        Kind ck = cur.getKind();
        std::vector< unsigned > justifyArgs;
        bool alreadyJustified = false;
        if( cur.getNumChildren()>1 )
        {
          for (unsigned i=0, size=cur.getNumChildren(); i<size; i++ )
          {
            Node cn = cur[i];
            it = value.find(cn);
            Assert(it != value.end());
            Assert(!it->second.isNull());
            if (isSingularArg(cn,ck,i) )
            {
              // have we seen this argument already? if so, we are done
              if( visited.find(cn)!=visited.end() )
              {
                alreadyJustified = true;
                break;
              }
              justifyArgs.push_back(i);
            }
          }
        }
        if( !alreadyJustified )
        {
          // we need to recurse on at most one child
          if( !justifyArgs.empty() )
          {
            unsigned sindex = justifyArgs[0];
            bool 
            if( justifyArgs.size()>1 )
            {
              // choose best index TODO
              //for( unsigned sai : justifyArgs )
              //{

              //}
            }
            visit.push_back(cur[sindex]);
          }
          else
          {
            // must recurse on all arguments
            if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
            {
              visit.push_back(cur.getOperator());
            }
            for (const Node& cn : cur)
            {
              visit.push_back(cn);
            }
          }
        }
      }
    }
  } while (!visit.empty());
  
  
  for( const Node& v : rlvFv )
  {
    Assert( std::find(vars.begin(),vars.end(),v)!=vars.end());
    reqVars.push_back(v);
  }
  
  return true;
}


bool SubstitutionMinimize::isSingularArg(Node n, Kind k, unsigned arg)
{
  Assert( n.isConst() );
  if( k==AND )
  {
    return !n.getConst<bool>();
  }
  else if( k==OR )
  {
    return n.getConst<bool>();
  }
  else if( k==IMPLIES )
  {
    return arg==(n.getConst<bool>() ? 1 : 0);
  }
  if( k==MULT || ( arg==0 && ( k == DIVISION_TOTAL || k == INTS_DIVISION_TOTAL || k==INTS_MODULUS_TOTAL ) ) )
  {
    // zero
    if( n.getConst<Rational>().sgn()==0 )
    {
      return true;
    }
  }
  if (k == BITVECTOR_AND || k == BITVECTOR_MULT 
             || k == BITVECTOR_UDIV_TOTAL
             || k == BITVECTOR_UREM_TOTAL ||
     ( arg==0 && (
      k == BITVECTOR_SHL || k == BITVECTOR_LSHR || k == BITVECTOR_ASHR)))
  {
    // bit-vector zero
    //Node cmpz = bv::utils::mkZero(
  }
  if( k==BITVECTOR_OR )
  {
    // bit-vector ones
  }
  
  if( ( arg==1 && k==STRING_STRCTN ) || ( arg==0 && k==STRING_SUBSTR ) )
  {
    // empty string 
    
  }
  if( ( arg!=0 && k==STRING_SUBSTR ) || ( arg==2 && k==STRING_STRIDOF ) )
  {
    // negative integer
    if( n.getConst<Rational>().sgn() < 0 )
    {
      return true;
    }
  }
  return false;
}

}  // namespace theory
}  // namespace CVC4
