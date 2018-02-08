/*********************                                                        */
/*! \file extended_rewrite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of extended rewriting techniques
 **/

#include "theory/quantifiers/extended_rewrite.h"

#include "theory/arith/arith_msum.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/bv/theory_bv_utils.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

ExtendedRewriter::ExtendedRewriter()
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

Node ExtendedRewriter::extendedRewritePullIte(Node n)
{
  // generalize this?
  Assert(n.getNumChildren() == 2);
  Assert(n.getType().isBoolean());
  Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
  std::vector<Node> children;
  for (unsigned i = 0; i < n.getNumChildren(); i++)
  {
    children.push_back(n[i]);
  }
  for (unsigned i = 0; i < 2; i++)
  {
    if (n[i].getKind() == kind::ITE)
    {
      for (unsigned j = 0; j < 2; j++)
      {
        children[i] = n[i][j + 1];
        Node eqr = extendedRewrite(
            NodeManager::currentNM()->mkNode(n.getKind(), children));
        children[i] = n[i];
        if (eqr.isConst())
        {
          std::vector<Node> new_children;
          Kind new_k;
          if (eqr == d_true)
          {
            new_k = kind::OR;
            new_children.push_back(j == 0 ? n[i][0] : n[i][0].negate());
          }
          else
          {
            Assert(eqr == d_false);
            new_k = kind::AND;
            new_children.push_back(j == 0 ? n[i][0].negate() : n[i][0]);
          }
          children[i] = n[i][2 - j];
          Node rem_eq = NodeManager::currentNM()->mkNode(n.getKind(), children);
          children[i] = n[i];
          new_children.push_back(rem_eq);
          Node nc = NodeManager::currentNM()->mkNode(new_k, new_children);
          Trace("q-ext-rewrite") << "sygus-extr : " << n << " rewrites to "
                                 << nc << " by simple ITE pulling."
                                 << std::endl;
          // recurse
          return extendedRewrite(nc);
        }
      }
    }
  }
  return Node::null();
}

Node ExtendedRewriter::extendedRewrite(Node n)
{
  n = Rewriter::rewrite( n );
  NodeManager * nm = NodeManager::currentNM();
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it =
      d_ext_rewrite_cache.find(n);
  if (it == d_ext_rewrite_cache.end())
  {
    Trace("q-ext-rewrite-debug") << "Do extended pre-rewrite on : " << n << std::endl;
    Node orig_n = n;
    
    Node ret = n;
    if (n.getNumChildren() > 0)
    {
      std::vector<Node> children;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(n.getOperator());
      }
      bool childChanged = false;
      for (unsigned i = 0; i < n.getNumChildren(); i++)
      {
        Node nc = extendedRewrite(n[i]);
        childChanged = nc != n[i] || childChanged;
        children.push_back(nc);
      }
      // Some commutative operators have rewriters that are agnostic to order,
      // thus, we sort here.
      if (TermUtil::isComm(n.getKind()))
      {
        childChanged = true;
        std::sort(children.begin(), children.end());
      }
      if (childChanged)
      {
        ret = nm->mkNode(n.getKind(), children);
      }
    }
    ret = Rewriter::rewrite(ret);
    Trace("q-ext-rewrite-debug") << "Do extended rewrite on : " << ret
                                 << " (from " << n << ")" << std::endl;

    Node new_ret;
    Kind k = ret.getKind();
    if (k == kind::EQUAL)
    {
      // simple ITE pulling
      new_ret = extendedRewritePullIte(ret);
    }
    else if (k == kind::ITE)
    {
      Assert(ret[1] != ret[2]);
      if (ret[0].getKind() == NOT)
      {
        ret = nm->mkNode( kind::ITE, ret[0][0], ret[2], ret[1]);
      }
      if (ret[0].getKind() == kind::EQUAL)
      {
        // simple invariant ITE
        for (unsigned i = 0; i < 2; i++)
        {
          if (ret[1] == ret[0][i] && ret[2] == ret[0][1 - i])
          {
            new_ret = ret[2];
            debugExtendedRewrite(ret,new_ret,"subs-ITE");
            break;
          }
        }
        // notice this is strictly more general than the above
        if (new_ret.isNull())
        {
          // simple substitution
          for (unsigned i = 0; i < 2; i++)
          {              
            TNode r1 = ret[0][i];
            TNode r2 = ret[0][1 - i];
            if (r1.isVar() && ((r2.isVar() && r1 < r2) || r2.isConst()))
            {
              Node retn = ret[1].substitute(r1, r2);
              if (retn != ret[1])
              {
                new_ret = nm->mkNode(ITE, ret[0], retn, ret[2]);
                debugExtendedRewrite(ret,new_ret,"subs-ITE");
              }
            }
          }
        }
      }
    }
    else if (k == DIVISION || k == INTS_DIVISION || k == INTS_MODULUS)
    {
      // rewrite as though total
      std::vector<Node> children;
      bool all_const = true;
      for (unsigned i = 0; i < ret.getNumChildren(); i++)
      {
        if (ret[i].isConst())
        {
          children.push_back(ret[i]);
        }
        else
        {
          all_const = false;
          break;
        }
      }
      if (all_const)
      {
        Kind new_k =
            (ret.getKind() == DIVISION
                 ? DIVISION_TOTAL
                 : (ret.getKind() == INTS_DIVISION ? INTS_DIVISION_TOTAL
                                                   : INTS_MODULUS_TOTAL));
        new_ret = nm->mkNode(new_k, children);
        debugExtendedRewrite(ret,new_ret,"total-interpretation");
      }
    }
    else if( k == BITVECTOR_AND || k == BITVECTOR_OR )
    {
      bool isAnd = ( k == BITVECTOR_AND );
      std::unordered_set< unsigned > drops;
      std::vector< Node > children;
      unsigned size=ret.getNumChildren();
      for( unsigned i=0; i<size; i++ )
      {
        Node cmpi = isAnd ? ret[i] : nm->mkNode( BITVECTOR_NOT, ret[i] );
        bool success = true;
        for( unsigned j=0; j<size; j++ )
        {
          if( i!=j && drops.find(j)==drops.end() )
          {
            bool cond = isAnd ? bitVectorSubsume( ret[i], ret[j] ) : bitVectorSubsume( ret[j], ret[i] );
            if( cond )
            {
              drops.insert(i);
              success = false;
            }
            Node cmpj = isAnd ? ret[j] : nm->mkNode( BITVECTOR_NOT, ret[j] );
            if( i<j && bitvectorDisjoint( cmpi, cmpj ) )
            {
              unsigned size = bv::utils::getSize(ret);
              new_ret = isAnd ? bv::utils::mkZero(size) : bv::utils::mkOnes(size);
              debugExtendedRewrite( ret, new_ret, "AND/OR-disjoint" );
              break;
            }
          }
        }
        if( !new_ret.isNull() )
        {
          break;
        }
        if( success )
        {
          children.push_back(ret[i]);
        }
      }
      if( new_ret.isNull() )
      {
        Assert( !children.empty() );
        if( children.size()<size )
        {
          new_ret = children.size()==1 ? children[0] : nm->mkNode( k, children );
          debugExtendedRewrite( ret, new_ret, "AND/OR subsume" );
        }
      }
    }
    else if( k == BITVECTOR_ULT )
    {
      if( bitVectorArithComp( ret[0], ret[1] ) )
      {
        new_ret = nm->mkConst(false);
        debugExtendedRewrite( ret, new_ret, "ULT-arith" );
      }
    }
    else if( k == BITVECTOR_SLT )
    {
      if( ret[0]==ret[1] )
      {
        new_ret = nm->mkConst(false);
        debugExtendedRewrite( ret, new_ret, "SLT-id" );
      }
    }
    else if( k == BITVECTOR_LSHR || k == BITVECTOR_SHL )
    {
      std::vector< Node > cchildren;
      Node base = decomposeChain( k, ret, cchildren );
      
      std::vector< Node > bchildren;
      if( k == BITVECTOR_LSHR )
      {
        if( base.getKind()==BITVECTOR_OR )
        {
          for( const Node& cr : base ) 
          {
            bchildren.push_back(cr);
          }
        }
        else
        {
          bchildren.push_back(base);
        }
        std::vector< Node > bctemp;
        bctemp.insert(bctemp.end(),bchildren.begin(),bchildren.end());
        bchildren.clear();
        for( const Node& bc : bctemp )
        {
          bool shifted = false;
          for( const Node& cc : cchildren )
          {
            if( bitVectorArithComp( cc, bc ) )
            {
              shifted = true;
              break;
            }
          }
          // for each child of an OR, if we shift more than this component,
          // it can be removed.
          if( !shifted )
          {
            bchildren.push_back( bc );
          }
        }
      }
      else
      {
        bchildren.push_back( base );
      }
      if( bchildren.empty() )
      {
        unsigned size = bv::utils::getSize(base);
        new_ret = bv::utils::mkZero(size);
      }
      else
      {
        base = bchildren.size()==1 ? bchildren[0] : nm->mkNode( BITVECTOR_OR, bchildren );
        std::sort( cchildren.begin(), cchildren.end() );
        new_ret = mkChain( k, base, cchildren );
        if( new_ret==ret )
        {
          new_ret = Node::null();
        }
      }
      if( !new_ret.isNull() )
      {
        debugExtendedRewrite( orig_n, n, "shift-sort-arith" );
      }
    }
    else if( k == BITVECTOR_PLUS || k == BITVECTOR_MULT )
    {
      std::vector< Node > rchildren;
      bool rchildrenChanged = false;
      for( const Node& rc : ret )
      {
        Node rcc = rc;
        if( rcc.getKind()==BITVECTOR_NOT )
        {
          // ~x + y ----> -(x+1)+y
          unsigned size = bv::utils::getSize(rc[0]);
          rcc = nm->mkNode( BITVECTOR_NEG, nm->mkNode( BITVECTOR_PLUS, rc[0], bv::utils::mkOne(size) ) );
          rchildrenChanged = true;
        }
        rchildren.push_back( rcc );
      }
      if( rchildrenChanged )
      {
        new_ret = nm->mkNode( k, rchildren );
        debugExtendedRewrite( ret, new_ret, "PLUS-not-child" );
        new_ret = extendedRewrite( new_ret );
      }
      else if( k == BITVECTOR_PLUS )
      {
        bool success = true;
        unsigned size=ret.getNumChildren();
        for( unsigned i=0; i<size; i++ )
        {
          for( unsigned j=(i+1); j<size; j++ )
          {
            if( !bitvectorDisjoint( ret[i], ret[j] ) )
            {
              success = false;
              break;
            }
          }
          if( !success )
          {
            break;
          }
        }
        if( success )
        {
          // if we prove disjointness, PLUS turns into OR
          // ( ( x ^ y ) ---> 0 ) => ( x+y ----> x V y )
          new_ret = nm->mkNode( BITVECTOR_OR, ret[0], ret[1] );
          debugExtendedRewrite( ret, new_ret, "PLUS-disjoint" );
        }
      }
    }
    else if( k == BITVECTOR_NEG )
    {
      // miniscope
      if( ret[0].getKind()==BITVECTOR_SHL )
      {
        new_ret = nm->mkNode( BITVECTOR_SHL, nm->mkNode( BITVECTOR_NEG, ret[0][0] ), ret[0][1] );
        debugExtendedRewrite( ret, new_ret, "NEG-SHL-miniscope" );
        new_ret = extendedRewrite( new_ret );
      }
      else if( ret[0].getKind()==BITVECTOR_NOT )
      {
        unsigned size = bv::utils::getSize(ret[0][0]);
        new_ret = nm->mkNode( BITVECTOR_PLUS, ret[0][0], bv::utils::mkOne(size) );
        debugExtendedRewrite( ret, new_ret, "NEG-NOT-miniscope" );
        new_ret = extendedRewrite( new_ret );
      }
    }
    else if( k == BITVECTOR_NOT )
    {
      // ~( -( x ) ) ----> x+1
      // ~( x+y ) ----> -(x+y)+1
      Kind ck = ret[0].getKind();
      if( ck==BITVECTOR_NEG || ck==BITVECTOR_PLUS )
      {
        Node c = ck==BITVECTOR_NEG ? ret[0][0] : nm->mkNode( BITVECTOR_NEG, ret[0] );
        unsigned size = bv::utils::getSize(c);
        new_ret = nm->mkNode( BITVECTOR_PLUS, c, bv::utils::mkOnes(size) );
        debugExtendedRewrite( ret, new_ret, "NOT-arith-miniscope" );
        new_ret = extendedRewrite( new_ret );
      }
    }
    
    
    // more expensive rewrites
    if (new_ret.isNull())
    {
      Trace("q-ext-rewrite-debug2") << "Do expensive rewrites on " << ret
                                    << std::endl;
      bool polarity = ret.getKind() != NOT;
      Node ret_atom = ret.getKind() == NOT ? ret[0] : ret;
      if ((ret_atom.getKind() == EQUAL && ret_atom[0].getType().isReal())
          || ret_atom.getKind() == GEQ)
      {
        Trace("q-ext-rewrite-debug2") << "Compute monomial sum " << ret_atom
                                      << std::endl;
        // compute monomial sum
        std::map<Node, Node> msum;
        if (ArithMSum::getMonomialSumLit(ret_atom, msum))
        {
          for (std::map<Node, Node>::iterator itm = msum.begin();
               itm != msum.end();
               ++itm)
          {
            Node v = itm->first;
            Trace("q-ext-rewrite-debug2") << itm->first << " * " << itm->second
                                          << std::endl;
            if (v.getKind() == ITE)
            {
              Node veq;
              int res = ArithMSum::isolate(v, msum, veq, ret_atom.getKind());
              if (res != 0)
              {
                Trace("q-ext-rewrite-debug")
                    << "  have ITE relation, solved form : " << veq
                    << std::endl;
                // try pulling ITE
                new_ret = extendedRewritePullIte(veq);
                if (!new_ret.isNull())
                {
                  if (!polarity)
                  {
                    new_ret = new_ret.negate();
                  }
                  debugExtendedRewrite(ret,new_ret,"solve-ITE");
                  break;
                }
              }
              else
              {
                Trace("q-ext-rewrite-debug") << "  failed to isolate " << v
                                             << " in " << ret << std::endl;
              }
            }
          }
        }
        else
        {
          Trace("q-ext-rewrite-debug") << "  failed to get monomial sum of "
                                       << ret << std::endl;
        }
      }
      else if (ret_atom.getKind() == ITE)
      {
        // TODO : conditional rewriting
      }
      else if (ret.getKind() == kind::AND || ret.getKind() == kind::OR)
      {
        // TODO condition merging
      }
    }

    if (!new_ret.isNull())
    {
      ret = Rewriter::rewrite(new_ret);
    }
    d_ext_rewrite_cache[orig_n] = ret;
    return ret;
  }
  else
  {
    return it->second;
  }
}  


bool ExtendedRewriter::bitVectorSubsume( Node a, Node b, bool strict )
{
  Trace("q-ext-rewrite-debug2") << "Subsume " << a << " " << b << "?" << std::endl;
  if( a==b )
  {
    return !strict;
  }
  if( a.getKind()==BITVECTOR_OR )
  {
    for( const Node& ac : a )
    {
      if( bitVectorSubsume( ac, b, strict ) )
      {
        return true;
      }
    }
  }
  else if( b.getKind()==BITVECTOR_AND )
  {
    for( const Node& bc : b )
    {
      if( bitVectorSubsume( a, bc, strict ) )
      {
        return true;
      }
    }
  }
  else if( b.getKind()==BITVECTOR_SHL )
  {
    if( b[0].getKind()==BITVECTOR_LSHR )
    {
      if( b[0][0]==a && b[0][1]==b[1] )
      {
        // or strict and geq zero
        return !strict;
      }
    }
  }
  else if( b.getKind()==BITVECTOR_LSHR )
  {
    if( b[0].getKind()==BITVECTOR_SHL )
    {
      if( b[0][0]==a && b[0][1]==b[1] )
      {
        // or strict and geq zero
        return !strict;
      }
    }
  }
  
  return false;
}

bool ExtendedRewriter::bitVectorArithComp( Node a, Node b, bool strict )
{
  if( bitVectorSubsume(a,b,strict) )
  {
    return true;
  }
  // shifting right always shrinks
  if( b.getKind() == BITVECTOR_LSHR )
  {
    if( bitVectorArithComp( a, b[0], strict ) )
    {
      return true;
    }
  }

  return false;
}

bool ExtendedRewriter::bitvectorDisjoint( Node a, Node b )
{
  for( unsigned r=0; r<2; r++ )
  {
    Node x = r==0 ? a : b;
    Node y = r==0 ? b : a;
    
    if( x.getKind()==BITVECTOR_NOT  )
    {
      if( x[0]==y )
      {
        return true;
      }
    }
    if( x.getKind()==BITVECTOR_SHL )
    {
      // bvshl( x, y ) is disjoint from z if y>z.
      if( bitVectorArithComp( x[1], y ) )
      {
        return true;
      }
    }
    else if( x.getKind()==BITVECTOR_AND )
    {
      for( const Node& xc : x ) 
      {
        if( bitvectorDisjoint( xc, y ) )
        {
          return true;
        }
      }
    }
  }
  
  return false;
}

Node ExtendedRewriter::decomposeChain( Kind k, Node n, std::vector< Node >& children )
{
  Node curr = n;
  while( curr.getKind()==k )
  {
    children.push_back( curr[1] );
    curr = curr[0];
  }
  return curr;
}

Node ExtendedRewriter::mkChain( Kind k, Node base, std::vector< Node >& children )
{
  NodeManager * nm = NodeManager::currentNM();
  Node curr = base;
  for( const Node& c : children )
  {
    curr = nm->mkNode( k, curr, c );
  }
  return curr;
}

void ExtendedRewriter::debugExtendedRewrite( Node n, Node ret, const char * c )
{
  Trace("q-ext-rewrite") << "sygus-extr : " << n << " rewrites to "
                          << ret << " due to " <<  c << "." << std::endl;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
