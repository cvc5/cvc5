/*********************                                                        */
/*! \file relevant_domain.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of relevant domain class
 **/

#include "theory/quantifiers/relevant_domain.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void RelevantDomain::RDomain::merge( RDomain * r ) {
  Assert(!d_parent);
  Assert(!r->d_parent);
  d_parent = r;
  for( unsigned i=0; i<d_terms.size(); i++ ){
    r->addTerm( d_terms[i] );
  }
  d_terms.clear();
}

void RelevantDomain::RDomain::addTerm( Node t ) {
  if( std::find( d_terms.begin(), d_terms.end(), t )==d_terms.end() ){
    d_terms.push_back( t );
  }
}

RelevantDomain::RDomain * RelevantDomain::RDomain::getParent() {
  if( !d_parent ){
    return this;
  }else{
    RDomain * p = d_parent->getParent();
    d_parent = p;
    return p;
  }
}

void RelevantDomain::RDomain::removeRedundantTerms(QuantifiersState& qs)
{
  std::map< Node, Node > rterms;
  for( unsigned i=0; i<d_terms.size(); i++ ){
    Node r = d_terms[i];
    if( !TermUtil::hasInstConstAttr( d_terms[i] ) ){
      r = qs.getRepresentative(d_terms[i]);
    }
    if( rterms.find( r )==rterms.end() ){
      rterms[r] = d_terms[i];
    }
  }
  d_terms.clear();
  for( std::map< Node, Node >::iterator it = rterms.begin(); it != rterms.end(); ++it ){
    d_terms.push_back( it->second );
  }
}



RelevantDomain::RelevantDomain( QuantifiersEngine* qe ) : d_qe( qe ){
   d_is_computed = false;
}

RelevantDomain::~RelevantDomain() {
  for( std::map< Node, std::map< int, RDomain * > >::iterator itr = d_rel_doms.begin(); itr != d_rel_doms.end(); ++itr ){
    for( std::map< int, RDomain * >::iterator itr2 = itr->second.begin(); itr2 != itr->second.end(); ++itr2 ){
      RDomain * current = (*itr2).second;
      Assert(current != NULL);
      delete current;
    }
  }
}

RelevantDomain::RDomain * RelevantDomain::getRDomain( Node n, int i, bool getParent ) {
  if( d_rel_doms.find( n )==d_rel_doms.end() || d_rel_doms[n].find( i )==d_rel_doms[n].end() ){
    d_rel_doms[n][i] = new RDomain;
    d_rn_map[d_rel_doms[n][i]] = n;
    d_ri_map[d_rel_doms[n][i]] = i;
  }
  return getParent ? d_rel_doms[n][i]->getParent() : d_rel_doms[n][i];
}

bool RelevantDomain::reset( Theory::Effort e ) {
  d_is_computed = false;
  return true;
}

void RelevantDomain::registerQuantifier(Node q) {}
void RelevantDomain::compute(){
  if( !d_is_computed ){
    d_is_computed = true;
    for( std::map< Node, std::map< int, RDomain * > >::iterator it = d_rel_doms.begin(); it != d_rel_doms.end(); ++it ){
      for( std::map< int, RDomain * >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        it2->second->reset();
      }
    }
    FirstOrderModel* fm = d_qe->getModel();
    for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
      Node q = fm->getAssertedQuantifier( i );
      Node icf = d_qe->getTermUtil()->getInstConstantBody( q );
      Trace("rel-dom-debug") << "compute relevant domain for " << icf << std::endl;
      computeRelevantDomain( q, icf, true, true );
    }

    Trace("rel-dom-debug") << "account for ground terms" << std::endl;
    TermDb * db = d_qe->getTermDatabase();
    for (unsigned k = 0; k < db->getNumOperators(); k++)
    {
      Node op = db->getOperator(k);
      unsigned sz = db->getNumGroundTerms( op );
      for( unsigned i=0; i<sz; i++ ){
        Node n = db->getGroundTerm(op, i);
        //if it is a non-redundant term
        if( db->isTermActive( n ) ){
          for( unsigned j=0; j<n.getNumChildren(); j++ ){
            RDomain * rf = getRDomain( op, j );
            rf->addTerm( n[j] );
            Trace("rel-dom-debug") << "...add ground term " << n[j] << " to rel dom " << op << "[" << j << "]" << std::endl;
          }
        }
      }
    }
    //print debug
    for( std::map< Node, std::map< int, RDomain * > >::iterator it = d_rel_doms.begin(); it != d_rel_doms.end(); ++it ){
      Trace("rel-dom") << "Relevant domain for " << it->first << " : " << std::endl;
      for( std::map< int, RDomain * >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        Trace("rel-dom") << "   " << it2->first << " : ";
        RDomain * r = it2->second;
        RDomain * rp = r->getParent();
        if( r==rp ){
          r->removeRedundantTerms(d_qe->getState());
          for( unsigned i=0; i<r->d_terms.size(); i++ ){
            Trace("rel-dom") << r->d_terms[i] << " ";
          }
        }else{
          Trace("rel-dom") << "Dom( " << d_rn_map[rp] << ", " << d_ri_map[rp] << " ) ";
        }
        Trace("rel-dom") << std::endl;
      }
    }
  }
}

void RelevantDomain::computeRelevantDomain( Node q, Node n, bool hasPol, bool pol ) {
  Trace("rel-dom-debug") << "Compute relevant domain " << n << "..." << std::endl;
  Node op = d_qe->getTermDatabase()->getMatchOperator( n );
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if( !op.isNull() ){
      RDomain * rf = getRDomain( op, i );
      if( n[i].getKind()==ITE ){
        for( unsigned j=1; j<=2; j++ ){
          computeRelevantDomainOpCh( rf, n[i][j] );
        }
      }else{
        computeRelevantDomainOpCh( rf, n[i] );
      }
    }
    // do not recurse under nested closures
    if (!n[i].isClosure())
    {
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getPolarity( n, i, hasPol, pol, newHasPol, newPol );
      computeRelevantDomain( q, n[i], newHasPol, newPol );
    }
  }

  if( ( ( n.getKind()==EQUAL && !n[0].getType().isBoolean() ) || n.getKind()==GEQ ) && TermUtil::hasInstConstAttr( n ) ){
    //compute the information for what this literal does
    computeRelevantDomainLit( q, hasPol, pol, n );
    if( d_rel_dom_lit[hasPol][pol][n].d_merge ){
      Assert(d_rel_dom_lit[hasPol][pol][n].d_rd[0] != NULL
             && d_rel_dom_lit[hasPol][pol][n].d_rd[1] != NULL);
      RDomain * rd1 = d_rel_dom_lit[hasPol][pol][n].d_rd[0]->getParent();
      RDomain * rd2 = d_rel_dom_lit[hasPol][pol][n].d_rd[1]->getParent();
      if( rd1!=rd2 ){
        rd1->merge( rd2 );
      }
    }else{
      if( d_rel_dom_lit[hasPol][pol][n].d_rd[0]!=NULL ){
        RDomain * rd = d_rel_dom_lit[hasPol][pol][n].d_rd[0]->getParent();
        for( unsigned i=0; i<d_rel_dom_lit[hasPol][pol][n].d_val.size(); i++ ){
          rd->addTerm( d_rel_dom_lit[hasPol][pol][n].d_val[i] );
        }
      }
    }
  }
  Trace("rel-dom-debug") << "...finished Compute relevant domain " << n << std::endl;
}

void RelevantDomain::computeRelevantDomainOpCh( RDomain * rf, Node n ) {
  if( n.getKind()==INST_CONSTANT ){
    Node q = d_qe->getTermUtil()->getInstConstAttr( n );
    //merge the RDomains
    unsigned id = n.getAttribute(InstVarNumAttribute());
    Assert(q[0][id].getType() == n.getType());
    Trace("rel-dom-debug") << n << " is variable # " << id << " for " << q;
    Trace("rel-dom-debug") << " with body : " << d_qe->getTermUtil()->getInstConstantBody( q ) << std::endl;
    RDomain * rq = getRDomain( q, id );
    if( rf!=rq ){
      rq->merge( rf );
    }
  }else if( !TermUtil::hasInstConstAttr( n ) ){
    Trace("rel-dom-debug") << "...add ground term to rel dom " << n << std::endl;
    //term to add
    rf->addTerm( n );
  }
}

void RelevantDomain::computeRelevantDomainLit( Node q, bool hasPol, bool pol, Node n ) {
  if( d_rel_dom_lit[hasPol][pol].find( n )==d_rel_dom_lit[hasPol][pol].end() ){
    d_rel_dom_lit[hasPol][pol][n].d_merge = false;
    int varCount = 0;
    int varCh = -1;
    TermUtil* tu = d_qe->getTermUtil();
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( n[i].getKind()==INST_CONSTANT ){
        // must get the quantified formula this belongs to, which may be
        // different from q
        Node qi = tu->getInstConstAttr(n[i]);
        unsigned id = n[i].getAttribute(InstVarNumAttribute());
        d_rel_dom_lit[hasPol][pol][n].d_rd[i] = getRDomain(qi, id, false);
        varCount++;
        varCh = i;
      }else{
        d_rel_dom_lit[hasPol][pol][n].d_rd[i] = NULL;
      }
    }
    
    Node r_add;
    bool varLhs = true;
    if( varCount==2 ){
      d_rel_dom_lit[hasPol][pol][n].d_merge = true;
    }else{
      if( varCount==1 ){
        r_add = n[1-varCh];
        varLhs = (varCh==0);
        d_rel_dom_lit[hasPol][pol][n].d_rd[0] = d_rel_dom_lit[hasPol][pol][n].d_rd[varCh];
        d_rel_dom_lit[hasPol][pol][n].d_rd[1] = NULL;
      }else{
        //solve the inequality for one/two variables, if possible
        if( n[0].getType().isReal() ){
          std::map< Node, Node > msum;
          if (ArithMSum::getMonomialSumLit(n, msum))
          {
            Node var;
            Node var2;
            bool hasNonVar = false;
            for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
              if (!it->first.isNull() && it->first.getKind() == INST_CONSTANT
                  && tu->getInstConstAttr(it->first) == q)
              {
                if( var.isNull() ){
                  var = it->first;
                }else if( var2.isNull() ){
                  var2 = it->first;
                }else{
                  hasNonVar = true;
                }
              }else{
                hasNonVar = true;
              }
            }
            if( !var.isNull() ){
              if( var2.isNull() ){
                //single variable solve
                Node veq_c;
                Node val;
                int ires =
                    ArithMSum::isolate(var, msum, veq_c, val, n.getKind());
                if( ires!=0 ){
                  if( veq_c.isNull() ){
                    r_add = val;
                    varLhs = (ires==1);
                    d_rel_dom_lit[hasPol][pol][n].d_rd[0] = getRDomain( q, var.getAttribute(InstVarNumAttribute()), false );
                    d_rel_dom_lit[hasPol][pol][n].d_rd[1] = NULL;
                  }
                }
              }else if( !hasNonVar ){
                //merge the domains
                d_rel_dom_lit[hasPol][pol][n].d_rd[0] = getRDomain( q, var.getAttribute(InstVarNumAttribute()), false );
                d_rel_dom_lit[hasPol][pol][n].d_rd[1] = getRDomain( q, var2.getAttribute(InstVarNumAttribute()), false );
                d_rel_dom_lit[hasPol][pol][n].d_merge = true;
              }
            }
          }
        }
      }
    }
    if( d_rel_dom_lit[hasPol][pol][n].d_merge ){
      //do not merge if constant negative polarity
      if( hasPol && !pol ){
        d_rel_dom_lit[hasPol][pol][n].d_merge = false;
      }
    }else if( !r_add.isNull() && !TermUtil::hasInstConstAttr( r_add ) ){
      Trace("rel-dom-debug") << "...add term " << r_add << ", pol = " << pol << ", kind = " << n.getKind() << std::endl;
      //the negative occurrence adds the term to the domain
      if( !hasPol || !pol ){
        d_rel_dom_lit[hasPol][pol][n].d_val.push_back( r_add );
      }
      //the positive occurence adds other terms
      if( ( !hasPol || pol ) && n[0].getType().isInteger() ){
        if( n.getKind()==EQUAL ){
          for( unsigned i=0; i<2; i++ ){
            d_rel_dom_lit[hasPol][pol][n].d_val.push_back(
                ArithMSum::offset(r_add, i == 0 ? 1 : -1));
          }
        }else if( n.getKind()==GEQ ){
          d_rel_dom_lit[hasPol][pol][n].d_val.push_back(
              ArithMSum::offset(r_add, varLhs ? 1 : -1));
        }
      }
    }else{
      d_rel_dom_lit[hasPol][pol][n].d_rd[0] = NULL;
      d_rel_dom_lit[hasPol][pol][n].d_rd[1] = NULL;
    }
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
