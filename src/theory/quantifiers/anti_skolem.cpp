/*********************                                                        */
/*! \file anti_skolem.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of anti-skolemization, e.g.:
 **          ( forall x. P[ f( x ) ] ^ forall x. Q[ f( x ) ]  ) => forall x. exists y. ( P[ y ] ^ Q[ y ] )
 **/

#include "theory/quantifiers/anti_skolem.h"

#include "expr/term_canonize.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

struct sortTypeOrder {
  expr::TermCanonize* d_tu;
  bool operator() (TypeNode i, TypeNode j) {
    return d_tu->getIdForType( i )<d_tu->getIdForType( j );
  }
};

void QuantAntiSkolem::SkQuantTypeCache::add( std::vector< TypeNode >& typs, Node q, unsigned index ) {
  if( index==typs.size() ){
    Assert(std::find(d_quants.begin(), d_quants.end(), q) == d_quants.end());
    d_quants.push_back( q );
  }else{
    d_children[typs[index]].add( typs, q, index+1 );
  }
}

void QuantAntiSkolem::SkQuantTypeCache::sendLemmas( QuantAntiSkolem * ask ) {
  for( std::map< TypeNode, SkQuantTypeCache >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
    it->second.sendLemmas( ask );
  }
  if( !d_quants.empty() ){
    ask->sendAntiSkolemizeLemma( d_quants );
  }
}

bool QuantAntiSkolem::CDSkQuantCache::add( context::Context* c, std::vector< Node >& quants, unsigned index ) {
  if( index==quants.size() ){
    if( !d_valid.get() ){
      d_valid.set( true );
      return true;
    }else{
      return false;
    }
  }else{
    Node n = quants[index];
    std::map< Node, CDSkQuantCache* >::iterator it = d_data.find( n );
    CDSkQuantCache* skc;
    if( it==d_data.end() ){
      skc = new CDSkQuantCache( c );
      d_data[n] = skc;
    }else{
      skc = it->second;
    }
    return skc->add( c, quants, index+1 );
  }
}

QuantAntiSkolem::CDSkQuantCache::~CDSkQuantCache() {
  for(std::map< Node, CDSkQuantCache* >::iterator i = d_data.begin(), iend = d_data.end();
      i != iend; ++i){
    CDSkQuantCache* current = (*i).second;
    Assert(current != NULL);
    delete current;
  }
}

QuantAntiSkolem::QuantAntiSkolem(QuantifiersEngine* qe)
    : QuantifiersModule(qe) {
  d_sqc = new CDSkQuantCache(qe->getUserContext());
}

QuantAntiSkolem::~QuantAntiSkolem() { delete d_sqc; }

/* Call during quantifier engine's check */
void QuantAntiSkolem::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e == QEFFORT_STANDARD)
  {
    d_sqtc.clear();
    for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
      if( d_quant_processed.find( q )==d_quant_processed.end() ){
        d_quant_processed[q] = true;
        Trace("anti-sk") << "Process quantified formula : " << q << std::endl;
        bool success = false;
        if( d_quant_sip[q].init( q[1] ) ){
          Trace("anti-sk") << "- Partitioned to single invocation parts : " << std::endl;
          d_quant_sip[q].debugPrint( "anti-sk" );
          //check if it is single invocation
          if( d_quant_sip[q].isPurelySingleInvocation() ){
            //for now, only do purely single invocation
            success = true;
          }
        }else{
          Trace("anti-sk") << "- Failed to initialize." << std::endl;
        }
        if( success ){
          //sort the argument variables
          std::vector<Node> sivars;
          d_quant_sip[q].getSingleInvocationVariables(sivars);
          for (const Node& v : sivars)
          {
            d_ask_types[q].push_back(v.getType());
          }
          std::map< TypeNode, std::vector< unsigned > > indices;
          for (unsigned j = 0, size = d_ask_types[q].size(); j < size; j++)
          {
            indices[d_ask_types[q][j]].push_back( j );
          }
          sortTypeOrder sto;
          sto.d_tu = d_quantEngine->getTermCanonize();
          std::sort( d_ask_types[q].begin(), d_ask_types[q].end(), sto );
          //increment j on inner loop
          for( unsigned j=0; j<d_ask_types[q].size();  ){
            TypeNode curr = d_ask_types[q][j];
            for( unsigned k=0; k<indices[curr].size(); k++ ){
              Assert(d_ask_types[q][j] == curr);
              d_ask_types_index[q].push_back( indices[curr][k] );
              j++;
            }
          }
          Assert(d_ask_types_index[q].size() == d_ask_types[q].size());
        }else{
          d_quant_sip.erase( q );
        }
      }
      //now, activate the quantified formula
      std::map< Node, std::vector< TypeNode > >::iterator it = d_ask_types.find( q );
      if( it!=d_ask_types.end() ){
        d_sqtc.add( it->second, q );        
      }
    }
    Trace("anti-sk-debug") << "Process lemmas..." << std::endl;
    //send out lemmas for each anti-skolemizable group of quantified formulas
    d_sqtc.sendLemmas( this );
    Trace("anti-sk-debug") << "...Finished process lemmas" << std::endl;
  }
}

bool QuantAntiSkolem::sendAntiSkolemizeLemma( std::vector< Node >& quants, bool pconnected ) {
  Assert(!quants.empty());
  std::sort( quants.begin(), quants.end() );
  if( d_sqc->add( d_quantEngine->getUserContext(), quants ) ){
    //partition into connected components
    if( pconnected && quants.size()>1 ){
      Trace("anti-sk-debug") << "Partition into connected components..." << std::endl;
      int eqc_count = 0;
      std::map< Node, int > func_to_eqc;
      std::map< int, std::vector< Node > > eqc_to_func;
      std::map< int, std::vector< Node > > eqc_to_quant;
      for( unsigned i=0; i<quants.size(); i++ ){
        Node q = quants[i];
        std::vector< int > eqcs;
        std::vector<Node> funcs;
        d_quant_sip[q].getFunctions(funcs);
        for (const Node& f : funcs)
        {
          std::map< Node, int >::iterator itf = func_to_eqc.find( f );
          if( itf == func_to_eqc.end() ){
            if( eqcs.empty() ){
              func_to_eqc[f] = eqc_count;
              eqc_to_func[eqc_count].push_back( f );
              eqc_count++;
            }else{
              func_to_eqc[f] = eqcs[0];
              eqc_to_func[eqcs[0]].push_back( f );
            }
          }
          if( std::find( eqcs.begin(), eqcs.end(), func_to_eqc[f] )==eqcs.end() ){
            eqcs.push_back( func_to_eqc[f] );
          }
        }
        Assert(!eqcs.empty());
        //merge equivalence classes
        int id = eqcs[0];
        eqc_to_quant[id].push_back( q );
        for( unsigned j=1; j<eqcs.size(); j++ ){
          int id2 = eqcs[j];
          std::map< int, std::vector< Node > >::iterator itef = eqc_to_func.find( id2 );
          if( itef!=eqc_to_func.end() ){
            for( unsigned k=0; k<itef->second.size(); k++ ){
              func_to_eqc[itef->second[k]] = id;
              eqc_to_func[id].push_back( itef->second[k] );
            }
            eqc_to_func.erase( id2 );
          }
          itef = eqc_to_quant.find( id2 );
          if( itef!=eqc_to_quant.end() ){
            eqc_to_quant[id].insert( eqc_to_quant[id].end(), itef->second.begin(), itef->second.end() );
            eqc_to_quant.erase( id2 );
          }
        }
      }
      if( eqc_to_quant.size()>1 ){
        bool addedLemma = false;
        for( std::map< int, std::vector< Node > >::iterator it = eqc_to_quant.begin(); it != eqc_to_quant.end(); ++it ){
          Assert(it->second.size() < quants.size());
          bool ret = sendAntiSkolemizeLemma( it->second, false );
          addedLemma = addedLemma || ret;
        }
        return addedLemma;
      }
    }    
    
    Trace("anti-sk") << "Anti-skolemize group : " << std::endl;
    for( unsigned i=0; i<quants.size(); i++ ){
      Trace("anti-sk") << "   " << quants[i] << std::endl;
    }

    std::vector< Node > outer_vars;
    std::vector< Node > inner_vars;
    Node q0 = quants[0];
    for (unsigned i = 0, size = d_ask_types[q0].size(); i < size; i++)
    {
      Node v = NodeManager::currentNM()->mkBoundVar(d_ask_types[q0][i]);
      Trace("anti-sk-debug") << "Outer var " << i << " : " << v << std::endl;
      outer_vars.push_back( v );
    }

    std::map< Node, Node > func_to_var;
    std::vector< Node > conj;
    for( unsigned i=0; i<quants.size(); i++ ){
      Node q = quants[i];
      Trace("anti-sk-debug") << "Process " << q << std::endl;
      std::vector< Node > subs_lhs;
      std::vector< Node > subs_rhs;
      //get outer variable substitution
      Assert(d_ask_types_index[q].size() == d_ask_types[q].size());
      std::vector<Node> sivars;
      d_quant_sip[q].getSingleInvocationVariables(sivars);
      for (unsigned j = 0, size = d_ask_types_index[q].size(); j < size; j++)
      {
        Trace("anti-sk-debug")
            << " o_subs : " << sivars[d_ask_types_index[q][j]] << " -> "
            << outer_vars[j] << std::endl;
        subs_lhs.push_back(sivars[d_ask_types_index[q][j]]);
        subs_rhs.push_back( outer_vars[j] );
      }
      //get function substitution
      std::vector<Node> funcs;
      d_quant_sip[q].getFunctions(funcs);
      for (const Node& f : funcs)
      {
        Node fv = d_quant_sip[q].getFirstOrderVariableForFunction(f);
        if( func_to_var.find( f )==func_to_var.end() ){
          Node v = NodeManager::currentNM()->mkBoundVar( fv.getType() );
          Trace("anti-sk-debug") << "Inner var for " << f << " : " << v << std::endl;
          inner_vars.push_back( v );
          func_to_var[f] = v;
        }
        subs_lhs.push_back( fv );
        subs_rhs.push_back( func_to_var[f] );
        Trace("anti-sk-debug") << " i_subs : " << fv << " -> " << func_to_var[f] << std::endl;
      }
      Node c = d_quant_sip[q].getSingleInvocation();
      if( !subs_lhs.empty() ){
        c = c.substitute( subs_lhs.begin(), subs_lhs.end(), subs_rhs.begin(), subs_rhs.end() );
      }
      conj.push_back( c );
    }
    Node body = conj.size()==1 ? conj[0] : NodeManager::currentNM()->mkNode( kind::AND, conj );
    if( !inner_vars.empty() ){
      Node bvl = NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, inner_vars );
      body = NodeManager::currentNM()->mkNode( kind::EXISTS, bvl, body );
    }
    if( !outer_vars.empty() ){
      Node bvl = NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, outer_vars );
      body = NodeManager::currentNM()->mkNode( kind::FORALL, bvl, body );
    }
    Trace("anti-sk") << "Produced : " << body << std::endl;
    quants.push_back( body.negate() );
    Node lem = NodeManager::currentNM()->mkNode( kind::AND, quants ).negate();
    Trace("anti-sk-lemma") << "Anti-skolemize lemma : " << lem << std::endl;
    quants.pop_back();
    return d_quantEngine->addLemma( lem ); 
  }else{
    return false;
  }
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
