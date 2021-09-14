/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of relevant domain class.
 */

#include "theory/quantifiers/relevant_domain.h"

#include "expr/term_context.h"
#include "expr/term_context_stack.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"

using namespace cvc5::kind;

namespace cvc5 {
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

RelevantDomain::RelevantDomain(Env& env,
                               QuantifiersState& qs,
                               QuantifiersRegistry& qr,
                               TermRegistry& tr)
    : QuantifiersUtil(env), d_qs(qs), d_qreg(qr), d_treg(tr)
{
  d_is_computed = false;
}

RelevantDomain::~RelevantDomain() {
  for (std::map<Node, std::map<size_t, RDomain*> >::iterator itr =
           d_rel_doms.begin();
       itr != d_rel_doms.end();
       ++itr)
  {
    for (std::map<size_t, RDomain*>::iterator itr2 = itr->second.begin();
         itr2 != itr->second.end();
         ++itr2)
    {
      RDomain * current = (*itr2).second;
      Assert(current != NULL);
      delete current;
    }
  }
}

RelevantDomain::RDomain* RelevantDomain::getRDomain(Node n,
                                                    size_t i,
                                                    bool getParent)
{
  if( d_rel_doms.find( n )==d_rel_doms.end() || d_rel_doms[n].find( i )==d_rel_doms[n].end() ){
    d_rel_doms[n][i] = new RDomain;
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
    for (std::map<Node, std::map<size_t, RDomain*> >::iterator it =
             d_rel_doms.begin();
         it != d_rel_doms.end();
         ++it)
    {
      for (std::map<size_t, RDomain*>::iterator it2 = it->second.begin();
           it2 != it->second.end();
           ++it2)
      {
        it2->second->reset();
      }
    }
    FirstOrderModel* fm = d_treg.getModel();
    for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
      Node q = fm->getAssertedQuantifier( i );
      Node icf = d_qreg.getInstConstantBody(q);
      Trace("rel-dom-debug") << "compute relevant domain for " << icf << std::endl;
      computeRelevantDomain(q);
    }

    Trace("rel-dom-debug") << "account for ground terms" << std::endl;
    TermDb* db = d_treg.getTermDatabase();
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
    for (std::map<Node, std::map<size_t, RDomain*> >::iterator it =
             d_rel_doms.begin();
         it != d_rel_doms.end();
         ++it)
    {
      Trace("rel-dom") << "Relevant domain for " << it->first << " : " << std::endl;
      for (std::map<size_t, RDomain*>::iterator it2 = it->second.begin();
           it2 != it->second.end();
           ++it2)
      {
        Trace("rel-dom") << "   " << it2->first << " : ";
        RDomain * r = it2->second;
        RDomain * rp = r->getParent();
        if( r==rp ){
          r->removeRedundantTerms(d_qs);
          Trace("rel-dom") << r->d_terms;
        }else{
          Trace("rel-dom") << "Dom( " << it->first << ", " << it2->first
                           << " ) ";
        }
        Trace("rel-dom") << std::endl;
        if (Configuration::isAssertionBuild())
        {
          if (it->first.getKind() == FORALL)
          {
            TypeNode expectedType = it->first[0][it2->first].getType();
            for (const Node& t : r->d_terms)
            {
              if (!t.getType().isComparableTo(expectedType))
              {
                Unhandled() << "Relevant domain: bad type " << t.getType()
                            << ", expected " << expectedType;
              }
            }
          }
        }
      }
    }
  }
}

void RelevantDomain::computeRelevantDomain(Node q)
{
  Assert(q.getKind() == FORALL);
  Node n = d_qreg.getInstConstantBody(q);
  // we care about polarity in the traversal, so we use a polarity term context
  PolarityTermContext tc;
  TCtxStack ctx(&tc);
  ctx.pushInitial(n);
  std::unordered_set<std::pair<Node, uint32_t>,
                     PairHashFunction<Node, uint32_t, std::hash<Node> > >
      visited;
  std::pair<Node, uint32_t> curr;
  Node node;
  uint32_t nodeVal;
  std::unordered_set<
      std::pair<Node, uint32_t>,
      PairHashFunction<Node, uint32_t, std::hash<Node> > >::const_iterator itc;
  bool hasPol, pol;
  while (!ctx.empty())
  {
    curr = ctx.getCurrent();
    itc = visited.find(curr);
    ctx.pop();
    if (itc == visited.end())
    {
      visited.insert(curr);
      node = curr.first;
      // if not a quantified formula
      if (!node.isClosure())
      {
        nodeVal = curr.second;
        // get the polarity of the current term and process it
        PolarityTermContext::getFlags(nodeVal, hasPol, pol);
        computeRelevantDomainNode(q, node, hasPol, pol);
        // traverse the children
        ctx.pushChildren(node, nodeVal);
      }
    }
  }
}

void RelevantDomain::computeRelevantDomainNode(Node q,
                                               Node n,
                                               bool hasPol,
                                               bool pol)
{
  Trace("rel-dom-debug") << "Compute relevant domain " << n << "..." << std::endl;
  Node op = d_treg.getTermDatabase()->getMatchOperator(n);
  // Relevant domain only makes sense for non-parametric operators, thus we
  // check op==n.getOperator() here. This otherwise would lead to bad types
  // for terms in the relevant domain.
  if (!op.isNull() && op == n.getOperator())
  {
    for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      RDomain * rf = getRDomain( op, i );
      if( n[i].getKind()==ITE ){
        for( unsigned j=1; j<=2; j++ ){
          computeRelevantDomainOpCh( rf, n[i][j] );
        }
      }else{
        computeRelevantDomainOpCh( rf, n[i] );
      }
    }
  }

  if( ( ( n.getKind()==EQUAL && !n[0].getType().isBoolean() ) || n.getKind()==GEQ ) && TermUtil::hasInstConstAttr( n ) ){
    //compute the information for what this literal does
    computeRelevantDomainLit( q, hasPol, pol, n );
    RDomainLit& rdl = d_rel_dom_lit[hasPol][pol][n];
    if (rdl.d_merge)
    {
      Assert(rdl.d_rd[0] != NULL && rdl.d_rd[1] != NULL);
      RDomain* rd1 = rdl.d_rd[0]->getParent();
      RDomain* rd2 = rdl.d_rd[1]->getParent();
      if( rd1!=rd2 ){
        rd1->merge( rd2 );
      }
    }
    else
    {
      if (rdl.d_rd[0] != NULL)
      {
        RDomain* rd = rdl.d_rd[0]->getParent();
        for (unsigned i = 0; i < rdl.d_val.size(); i++)
        {
          rd->addTerm(rdl.d_val[i]);
        }
      }
    }
  }
  Trace("rel-dom-debug") << "...finished Compute relevant domain " << n << std::endl;
}

void RelevantDomain::computeRelevantDomainOpCh( RDomain * rf, Node n ) {
  if( n.getKind()==INST_CONSTANT ){
    Node q = TermUtil::getInstConstAttr(n);
    //merge the RDomains
    size_t id = n.getAttribute(InstVarNumAttribute());
    Assert(q[0][id].getType() == n.getType());
    Trace("rel-dom-debug") << n << " is variable # " << id << " for " << q;
    Trace("rel-dom-debug") << " with body : " << d_qreg.getInstConstantBody(q)
                           << std::endl;
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
    RDomainLit& rdl = d_rel_dom_lit[hasPol][pol][n];
    rdl.d_merge = false;
    int varCount = 0;
    int varCh = -1;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( n[i].getKind()==INST_CONSTANT ){
        // must get the quantified formula this belongs to, which may be
        // different from q
        Node qi = TermUtil::getInstConstAttr(n[i]);
        unsigned id = n[i].getAttribute(InstVarNumAttribute());
        rdl.d_rd[i] = getRDomain(qi, id, false);
        varCount++;
        varCh = i;
      }else{
        rdl.d_rd[i] = nullptr;
      }
    }
    
    Node r_add;
    bool varLhs = true;
    if( varCount==2 ){
      rdl.d_merge = true;
    }else{
      if( varCount==1 ){
        r_add = n[1-varCh];
        varLhs = (varCh==0);
        rdl.d_rd[0] = rdl.d_rd[varCh];
        rdl.d_rd[1] = nullptr;
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
                  && TermUtil::getInstConstAttr(it->first) == q)
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
            Trace("rel-dom") << "Process lit " << n << ", var/var2=" << var
                             << "/" << var2 << std::endl;
            if( !var.isNull() ){
              Assert(var.hasAttribute(InstVarNumAttribute()));
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
                    rdl.d_rd[0] = getRDomain(
                        q, var.getAttribute(InstVarNumAttribute()), false);
                    rdl.d_rd[1] = nullptr;
                  }
                }
              }else if( !hasNonVar ){
                Assert(var2.hasAttribute(InstVarNumAttribute()));
                //merge the domains
                rdl.d_rd[0] = getRDomain(
                    q, var.getAttribute(InstVarNumAttribute()), false);
                rdl.d_rd[1] = getRDomain(
                    q, var2.getAttribute(InstVarNumAttribute()), false);
                rdl.d_merge = true;
              }
            }
          }
        }
      }
    }
    if (rdl.d_merge)
    {
      //do not merge if constant negative polarity
      if( hasPol && !pol ){
        rdl.d_merge = false;
      }
    }
    else if (!r_add.isNull() && !TermUtil::hasInstConstAttr(r_add))
    {
      Trace("rel-dom-debug") << "...add term " << r_add << ", pol = " << pol << ", kind = " << n.getKind() << std::endl;
      //the negative occurrence adds the term to the domain
      if( !hasPol || !pol ){
        rdl.d_val.push_back(r_add);
      }
      //the positive occurence adds other terms
      if( ( !hasPol || pol ) && n[0].getType().isInteger() ){
        if( n.getKind()==EQUAL ){
          for( unsigned i=0; i<2; i++ ){
            rdl.d_val.push_back(ArithMSum::offset(r_add, i == 0 ? 1 : -1));
          }
        }else if( n.getKind()==GEQ ){
          rdl.d_val.push_back(ArithMSum::offset(r_add, varLhs ? 1 : -1));
        }
      }
    }
    else
    {
      rdl.d_rd[0] = NULL;
      rdl.d_rd[1] = NULL;
    }
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
