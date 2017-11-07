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

#include "theory/rewriter.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/strings/theory_strings_rewriter.h"
#include "theory/quantifiers/quant_util.h" // for QuantArith

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
ExtendedRewriter::ExtendedRewriter(){
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

Node ExtendedRewriter::extendedRewritePullIte( Node n ) {
  // generalize this?
  Assert( n.getNumChildren()==2 );
  Assert( n.getType().isBoolean() );
  Assert( n.getMetaKind() != kind::metakind::PARAMETERIZED );
  std::vector< Node > children;
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    children.push_back( n[i] );
  }
  for( unsigned i=0; i<2; i++ ){
    if( n[i].getKind()==kind::ITE ){
      for( unsigned j=0; j<2; j++ ){
        children[i] = n[i][j+1];
        Node eqr = extendedRewrite( NodeManager::currentNM()->mkNode( n.getKind(), children ) );
        children[i] = n[i];
        if( eqr.isConst() ){
          std::vector< Node > new_children;
          Kind new_k;
          if( eqr==d_true ){
            new_k = kind::OR;
            new_children.push_back( j==0 ? n[i][0] : n[i][0].negate() );
          }else{
            Assert( eqr==d_false );
            new_k = kind::AND;
            new_children.push_back( j==0 ? n[i][0].negate() : n[i][0] );
          }
          children[i] = n[i][2-j];
          Node rem_eq = NodeManager::currentNM()->mkNode( n.getKind(), children );
          children[i] = n[i];
          new_children.push_back( rem_eq );
          Node nc = NodeManager::currentNM()->mkNode( new_k, new_children );
          Trace("sygus-ext-rewrite") << "sygus-extr : " << n << " rewrites to " << nc << " by simple ITE pulling." << std::endl;
          //recurse
          return extendedRewrite( nc );
        }
      }
    }
  }
  return Node::null();
}

Node ExtendedRewriter::extendedRewrite( Node n ) {
  std::map< Node, Node >::iterator it = d_ext_rewrite_cache.find( n );
  if( it == d_ext_rewrite_cache.end() ){
    Node ret = n;
    if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( n.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node nc = extendedRewrite( n[i] );
        childChanged = nc!=n[i] || childChanged;
        children.push_back( nc );
      }
      Node ret;
      if( childChanged ){
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    ret = Rewriter::rewrite( n );
    Trace("sygus-ext-rewrite-debug") << "Do extended rewrite on : " << ret << " (from " << n << ")" << std::endl; 

    Node new_ret;
    if( ret.getKind()==kind::EQUAL ){
      // string equalities with disequal prefix or suffix
      if( ret[0].getType().isString() ){
        std::vector< Node > c[2];
        for( unsigned i=0; i<2; i++ ){
          strings::TheoryStringsRewriter::getConcat( ret[i], c[i] );
        }
        if( c[0].empty()==c[1].empty() ){
          if( !c[0].empty() ){
            for( unsigned i=0; i<2; i++ ){
              unsigned index1 = i==0 ? 0 : c[0].size()-1;
              unsigned index2 = i==0 ? 0 : c[1].size()-1;
              if( c[0][index1].isConst() && c[1][index2].isConst() ){
                CVC4::String s = c[0][index1].getConst<String>();
                CVC4::String t = c[1][index2].getConst<String>();
                unsigned len_short = s.size() <= t.size() ? s.size() : t.size();
                bool isSameFix = i==1 ? s.rstrncmp(t, len_short): s.strncmp(t, len_short);
                if( !isSameFix ){
                  Trace("sygus-ext-rewrite") << "sygus-extr : " << ret << " rewrites to false due to disequal string prefix/suffix." << std::endl;
                  new_ret = d_false;
                  break;
                }
              }
            }
          }
        }else{
          new_ret = d_false;
        }
      }
      if( new_ret.isNull() ){
        // simple ITE pulling
        new_ret = extendedRewritePullIte( ret );
      }
      // TODO : ( ~contains( x, y ) --> false ) => ( ~x=y --> false )
    }else if( ret.getKind()==kind::ITE ){
      Assert( ret[1]!=ret[2] );
      if( ret[0].getKind()==NOT ){
        ret = NodeManager::currentNM()->mkNode( kind::ITE, ret[0][0], ret[2], ret[1] );
      }
      if( ret[0].getKind()==kind::EQUAL ){
        // simple invariant ITE
        for( unsigned i=0; i<2; i++ ){
          if( ret[1]==ret[0][i] && ret[2]==ret[0][1-i] ){
            Trace("sygus-ext-rewrite") << "sygus-extr : " << ret << " rewrites to " << ret[2] << " due to simple invariant ITE." << std::endl;
            new_ret = ret[2];
            break;
          }
        }
        // notice this is strictly more general that the above
        if( new_ret.isNull() ){
          // simple substitution
          for( unsigned i=0; i<2; i++ ){
            if( ret[0][i].isVar() && ( ( ret[0][1-i].isVar() && ret[0][i]<ret[0][1-i] ) || ret[0][1-i].isConst() ) ){
              TNode r1 = ret[0][i];
              TNode r2 = ret[0][1-i];
              Node retn = ret[1].substitute( r1, r2 );
              if( retn!=ret[1] ){
                new_ret = NodeManager::currentNM()->mkNode( kind::ITE, ret[0], retn, ret[2] );
                Trace("sygus-ext-rewrite") << "sygus-extr : " << ret << " rewrites to " << new_ret << " due to simple ITE substitution." << std::endl;
              }
            }
          }
        }
      }
    }else if( ret.getKind()==DIVISION || ret.getKind()==INTS_DIVISION || ret.getKind()==INTS_MODULUS ){
      // rewrite as though total
      std::vector< Node > children;
      bool all_const = true;
      for( unsigned i=0; i<ret.getNumChildren(); i++ ){
        if( ret[i].isConst() ){
          children.push_back( ret[i] );
        }else{
          all_const = false;
          break;
        }
      }
      if( all_const ){
        Kind new_k = ( ret.getKind()==DIVISION ? DIVISION_TOTAL : ( ret.getKind()==INTS_DIVISION ? INTS_DIVISION_TOTAL : INTS_MODULUS_TOTAL ) ); 
        new_ret = NodeManager::currentNM()->mkNode( new_k, children );
        Trace("sygus-ext-rewrite") << "sygus-extr : " << ret << " rewrites to " << new_ret << " due to total interpretation." << std::endl;
      }
    }
    // more expensive rewrites 
    if( new_ret.isNull() ){
      Trace("sygus-ext-rewrite-debug2")  << "Do expensive rewrites on " << ret << std::endl;
      bool polarity = ret.getKind()!=NOT;
      Node ret_atom = ret.getKind()==NOT ? ret[0] : ret;
      if( ( ret_atom.getKind()==EQUAL && ret_atom[0].getType().isReal() ) || ret_atom.getKind()==GEQ ){
        Trace("sygus-ext-rewrite-debug2")  << "Compute monomial sum " << ret_atom << std::endl;
        //compute monomial sum
        std::map< Node, Node > msum;
        if( QuantArith::getMonomialSumLit( ret_atom, msum ) ){
          for( std::map< Node, Node >::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
            Node v = itm->first;
            Trace("sygus-ext-rewrite-debug2") << itm->first << " * " << itm->second << std::endl;
            if( v.getKind()==ITE ){
              Node veq;
              int res = QuantArith::isolate( v, msum, veq, ret_atom.getKind() );
              if( res!=0 ){
                Trace("sygus-ext-rewrite-debug") << "  have ITE relation, solved form : " << veq << std::endl;
                // try pulling ITE
                new_ret = extendedRewritePullIte( veq );
                if( !new_ret.isNull() ){
                  if( !polarity ){
                    new_ret = new_ret.negate();
                  }
                  break;
                }
              }else{
                Trace("sygus-ext-rewrite-debug") << "  failed to isolate " << v << " in " << ret << std::endl;
              }
            }
          }
        }else{
          Trace("sygus-ext-rewrite-debug") << "  failed to get monomial sum of " << ret << std::endl;
        }
      }else if( ret_atom.getKind()==ITE ){
        // TODO : conditional rewriting
      }else if( ret.getKind()==kind::AND || ret.getKind()==kind::OR ){
        // TODO condition merging
      }
    }
    
    if( !new_ret.isNull() ){
      ret = Rewriter::rewrite( new_ret );
    }
    d_ext_rewrite_cache[n] = ret;
    return ret;
  }else{
    return it->second;
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
