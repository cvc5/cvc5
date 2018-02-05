/*********************                                                        */
/*! \file sygus_grammar_red.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_grammar_red
 **/

#include "theory/quantifiers/sygus_grammar_red.h"

#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "options/quantifiers_options.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

class ReconstructTrie {
public:
  std::map< Node, ReconstructTrie > d_children;
  std::vector< Node > d_reconstruct;
  void add( std::vector< Node >& cons, Node r, unsigned index = 0 ){
    if( index==cons.size() ){
      d_reconstruct.push_back( r );
    }else{
      d_children[cons[index]].add( cons, r, index+1 );
    }
  }
  Node getReconstruct( std::map< Node, int >& rcons, unsigned depth ) {
    if( !d_reconstruct.empty() ){
      for( unsigned i=0, size = d_reconstruct.size(); i<size; i++ ){
        Node r = d_reconstruct[i];
        if( rcons[r]==0 ){
          Trace("sygus-static-enum") << "...eliminate constructor " << r << std::endl;
          rcons[r] = 1;
          return r;
        }
      }
    }
    if( depth>0 ){
      for( unsigned w=0; w<2; w++ ){
        for( std::map< Node, ReconstructTrie >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
          Node n = it->first;
          if( ( w==0 && rcons[n]!=0 ) || ( w==1 && rcons[n]==0 ) ){
            Node r = it->second.getReconstruct( rcons, depth - w );
            if( !r.isNull() ){
              if( w==1 ){
                Trace("sygus-static-enum") << "...use " << n << " to eliminate constructor " << r << std::endl;
                rcons[n] = -1;
              }
              return r;
            }
          }
        }
      }
    }
    return Node::null();
  }
};

void SygusRedundantCons::initialize( QuantifiersEngine * qe, TypeNode tn )
{
  Assert( qe!=nullptr );
  Trace("sygus-red") << "Initialize for " << tn << std::endl;
  d_type = tn;
  Assert( tn.isDatatype() );
  TermDbSygus * tds = qe->getTermDatabaseSygus();
  tds->registerSygusType( tn );
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  Assert( dt.isSygus() );
  TypeNode btn = TypeNode::fromType( dt.getSygusType() );
  for( unsigned i=0, ncons = dt.getNumConstructors(); i<ncons; i++ ){
    bool nred = true;
    Trace("sygus-red-debug") << "Is " << dt[i].getName() << " a redundant operator?" << std::endl;
    Kind ck = tds->getConsNumKind( tn, i );
    if( ck!=UNDEFINED_KIND ){
      Kind dk;
      if (TermUtil::isAntisymmetric(ck, dk))
      {
        int j = tds->getKindConsNum( tn, dk );
        if( j!=-1 ){
          Trace("sygus-red-debug") << "Possible redundant operator : " << ck << " with " << dk << std::endl;
          //check for type mismatches
          bool success = true;
          for( unsigned k=0; k<2; k++ ){
            unsigned ko = k==0 ? 1 : 0;
            TypeNode tni = tds->getArgType( dt[i], k );
            TypeNode tnj = tds->getArgType( dt[j], ko );
            if( tni!=tnj ){
              Trace("sygus-red-debug") << "Argument types " << tni << " and " << tnj << " are not equal." << std::endl;
              success = false;
              break;
            }
          }
          if( success ){
            Trace("sygus-red") << "* Sygus norm " << dt.getName() << " : do not consider any " << ck << " terms." << std::endl;
            nred = false;
          }
        }
      }
    }
    if( nred ){
      Trace("sygus-red-debug") << "Check " << dt[i].getName() << " based on generic rewriting" << std::endl;
      std::map< int, Node > pre;
      Node g = tds->mkGeneric( dt, i, pre );
      Trace("sygus-red-debug") << "...generic term is " << g << std::endl;
      nred = !computeRedundant( tn, g );
      Trace("sygus-red-debug") << "...done check " << dt[i].getName() << " based on generic rewriting" << std::endl;
    }
    d_sygus_red_status.push_back( nred ? 0 : 1 );
  }
  // run an enumerator for this type
  if( options::sygusMinGrammarAgg() ){
    TermUtil * tutil = qe->getTermUtil();
    TypeEnumerator te(tn);
    unsigned count = 0;
    std::map< Node, std::vector< Node > > builtin_to_orig;
    Trace("sygus-static-enum") << "Static enumerate " << dt.getName() << "..." << std::endl;
    while( !te.isFinished() && count<1000 ){
      Node n = *te;
      Node bn = tds->sygusToBuiltin( n, tn );
      Trace("sygus-static-enum") << "  " << bn;
      Node bnr = Rewriter::rewrite( bn );
      Trace("sygus-static-enum") << "  ..." << bnr << std::endl;
      builtin_to_orig[bnr].push_back( n );
      ++te;
      count++;
    }
    std::map< Node, bool > reserved;
    for( unsigned i=0; i<=2; i++ ){
      Node rsv =
          i == 2 ? tutil->getTypeMaxValue(btn)
                  : tutil->getTypeValue(btn, i);
      if( !rsv.isNull() ){
        reserved[ rsv ] = true;
      }
    }
    Trace("sygus-static-enum") << "...make the reconstruct index data structure..." << std::endl;
    ReconstructTrie rt;
    std::map< Node, int > rcons;
    unsigned max_depth = 0;
    for( std::map< Node, std::vector< Node > >::iterator itb = builtin_to_orig.begin(); itb != builtin_to_orig.end(); ++itb ){
      if( itb->second.size()>0 ){
        std::map< Node, std::vector< Node > > clist;
        Node single_cons;
        for( unsigned j=0; j<itb->second.size(); j++ ){
          Node e = itb->second[j];
          tds->getSygusConstructors( e, clist[e] );
          if( clist[e].size()>max_depth ){
            max_depth = clist[e].size();
          }
          for( unsigned k=0; k<clist[e].size(); k++ ){

            rcons[clist[e][k]] = 0;
          }
          if( clist[e].size()==1 ){
            Trace("sygus-static-enum") << "...single constructor term : " << e << ", builtin is " << itb->first << ", cons is " << clist[e][0] << std::endl;
            if( single_cons.isNull() ){
              single_cons = clist[e][0];
            }else{
              Trace("sygus-static-enum") << "*** already can eliminate constructor " << clist[e][0] << std::endl;
              unsigned cindex =  Datatype::indexOf( clist[e][0].toExpr() );
              d_sygus_red_status[cindex] = 1;
            }
          }
        }
        // do not eliminate 0, 1, or max
        if( !single_cons.isNull() && reserved.find( itb->first )==reserved.end() ){
          Trace("sygus-static-enum") << "...possibly elim " << single_cons << std::endl;
          for( std::map< Node, std::vector< Node > >::iterator itc = clist.begin(); itc != clist.end(); ++itc ){
            if( std::find( itc->second.begin(), itc->second.end(), single_cons )==itc->second.end() ){
              rt.add( itc->second, single_cons );
            }
          }
        }
      }
    }
    Trace("sygus-static-enum") << "...compute reconstructions..." << std::endl;
    Node next_rcons;
    do {
      unsigned depth = 0;
      do{
        next_rcons = rt.getReconstruct( rcons, depth );
        depth++;
      }while( next_rcons.isNull() && depth<=max_depth );
      // if we found a constructor to eliminate
      if( !next_rcons.isNull() ){
        Trace("sygus-static-enum") << "*** eliminate constructor " << next_rcons << std::endl;
        unsigned cindex =  Datatype::indexOf( next_rcons.toExpr() );
        d_sygus_red_status[cindex] = 2;
      }
    }while( !next_rcons.isNull() );
    Trace("sygus-static-enum") << "...finished..." << std::endl;
  }
}

bool SygusRedundantCons::computeRedundant( TypeNode tn, Node g ) {
  //everything added to this cache should be mutually exclusive cases
  std::map< Node, bool >::iterator it = d_gen_redundant.find( g );
  if( it!=d_gen_redundant.end() ){
    return it->second;
  }
  Trace("sygus-red-debug") << "Register generic for " << tn << " : " << g << std::endl;
  Node gr = Rewriter::rewrite( g );
  Trace("sygus-red-debug") << "Generic " << g << " rewrites to " << gr << std::endl;
  std::map< Node, Node >::iterator itg = d_gen_terms.find( gr );
  bool red = true;
  if( itg==d_gen_terms.end() ){
    red = false;
    d_gen_terms[gr] = g;
    Trace("sygus-red-debug") << "...not redundant." << std::endl;
    Trace("sygus-red-debug") << "*** Sygus (generic) normal form : normal form of " << g << " is " << gr << std::endl;
  }else{
    Trace("sygus-red-debug") << "...redundant." << std::endl;
    Trace("sygus-red") << "* Sygus normal form : simplify since " << g << " and " << itg->second << " both rewrite to " << gr << std::endl;
  }
  d_gen_redundant[g] = red;
  return red;
}


void SygusRedundantCons::getRedundant( std::vector< unsigned >& indices )
{
  const Datatype& dt = static_cast<DatatypeType>(d_type.toType()).getDatatype();
  for( unsigned i=0, ncons = dt.getNumConstructors(); i<ncons; i++ )
  {
    if( isRedundant( i ) )
    {
      indices.push_back( i );
    }
  }
}

bool SygusRedundantCons::isRedundant( unsigned i ) {
  Assert( i<d_sygus_red_status.size() );
  if( options::sygusMinGrammarAgg() ){
    return d_sygus_red_status[i]!=0;
  }
  return d_sygus_red_status[i]==1;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
