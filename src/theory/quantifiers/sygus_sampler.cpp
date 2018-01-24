/*********************                                                        */
/*! \file sygus_sampler.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_sampler
 **/

#include "theory/quantifiers/sygus_sampler.h"

#include "util/bitvector.h"
#include "util/random.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
Node LazyTrie::add(Node n, LazyTrieEvaluator* ev, unsigned index, unsigned ntotal)
{
  LazyTrie * lt = this;
  while( lt!=NULL )
  {
    if (index == ntotal) {
      // lazy child holds the leaf data
      if (lt->d_lazy_child.isNull()) {
        lt->d_lazy_child = n;
      }
      return lt->d_lazy_child;
    } else {
      std::vector<Node> ex;
      if (lt->d_children.empty()) {
        if (lt->d_lazy_child.isNull()) {
          // no one has been here, we are done
          lt->d_lazy_child = n;
          return lt->d_lazy_child;
        } else {
          // evaluate the lazy child
          Node e_lc = ev->evaluate(lt->d_lazy_child, index);
          lt->d_children[e_lc].add(lt->d_lazy_child, ev, index+1, ntotal);
          lt->d_lazy_child = Node::null();
        }
      }
      // recurse
      Node e = ev->evaluate(n, index);
      lt = &lt->d_children[e];
      index = index+1;
    }
  }
  return Node::null();
}
  
SygusSampler::SygusSampler( QuantifiersEngine * qe, Node f, unsigned nsamples ) : 
d_qe( qe ), d_tds( qe->getTermDatabaseSygus() ), d_is_valid( true ) {
  d_ftn = f.getType();
  Assert( d_ftn.isDatatype() );
  const Datatype& dt = static_cast<DatatypeType>(d_ftn.toType()).getDatatype();
  Assert( dt.isSygus() );
  
  Trace("sygus-sample") << "Register sampler for " << f << std::endl;

  std::vector< TypeNode > types;
  // get the sygus variable list
  Node var_list = Node::fromExpr( dt.getSygusVarList() );
  if( !var_list.isNull() ){
    for( const Node& sv : var_list ){
      TypeNode svt = sv.getType();
      d_type_vars[svt].push_back( sv );
      types.push_back( svt );
      Trace("sygus-sample") << "  var #" << types.size() << " : " << sv << " : " << svt << std::endl;
    }
  }
  
  for( unsigned i=0; i<nsamples; i++ )
  {
    std::vector< Node > sample_pt;
    Trace("sygus-sample") << "Sample point #" << i << " : ";
    for( unsigned j=0, size = types.size(); j<size; j++ )
    {
      Node r = getRandomValue( types[j] );
      if( r.isNull() ){
        Trace("sygus-sample") << "INVALID";
        d_is_valid = false;
      }
      Trace("sygus-sample") << r << " ";
      sample_pt.push_back( r );
    }
    Trace("sygus-sample") << std::endl;
    d_samples.push_back( sample_pt );
  }
}

Node SygusSampler::registerTerm( Node n )
{
  if( d_is_valid )
  {
    // check whether the free variables in n are contiguous
    bool is_contiguous = true;
    
    
    
    if( is_contiguous )
    {
      return d_trie.add(n,this,0,d_samples.size());
    }
  }
  return n;
}

Node SygusSampler::evaluate(Node n, unsigned index)
{
  Assert( index<d_samples.size() );
  Node ev = d_tds->evaluateBuiltin(d_ftn, n, d_samples[index]);
  Trace("sygus-sample-ev") << "( " << n << ", " << index << " ) -> " << ev << std::endl;
  return ev;
}

Node SygusSampler::getRandomValue( TypeNode tn )
{
  NodeManager * nm = NodeManager::currentNM();
  if( tn.isBoolean() )
  {
    return nm->mkConst(Random::getRandom().pickWithProb(0.5));
  }
  else if( tn.isBitVector() )
  {
    unsigned sz = tn.getBitVectorSize();
    std::stringstream ss;
    for( unsigned i=0; i<sz; i++ )
    {
      ss << ( Random::getRandom().pickWithProb(0.5) ? "1" : "0" );
    }
    return nm->mkConst(BitVector(ss.str(), 2));
  }
  else if( tn.isString() )
  {
    
  }
  else if( tn.isInteger() )
  {
    
  }
  else if( tn.isReal() )
  {
    
  }
  
  return Node::null();
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
