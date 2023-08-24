/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
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
  for (auto& r : d_rel_doms)
  {
    for (auto& rr : r.second)
    {
      RDomain* current = rr.second;
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
    for (auto& r : d_rel_doms)
    {
      for (auto& rr : r.second)
      {
        rr.second->reset();
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
    // print debug and verify types are correct
    NodeManager* nm = NodeManager::currentNM();
    for (std::pair<const Node, std::map<size_t, RDomain*> >& d : d_rel_doms)
    {
      Trace("rel-dom") << "Relevant domain for " << d.first << " : "
                       << std::endl;
      for (std::pair<const size_t, RDomain*>& dd : d.second)
      {
        Trace("rel-dom") << "   " << dd.first << " : ";
        RDomain* r = dd.second;
        RDomain * rp = r->getParent();
        if( r==rp ){
          r->removeRedundantTerms(d_qs);
          Trace("rel-dom") << r->d_terms;
        }else{
          Trace("rel-dom") << "Dom( " << d.first << ", " << dd.first << " ) ";
        }
        Trace("rel-dom") << std::endl;
        if (d.first.getKind() == FORALL)
        {
          TypeNode expectedType = d.first[0][dd.first].getType();
          for (Node& t : r->d_terms)
          {
            TypeNode tt = t.getType();
            if (tt != expectedType)
            {
              // Computation may merge Int with Real due to inequalities. We
              // correct this here.
              if (tt.isInteger() && expectedType.isReal())
              {
                t = nm->mkNode(TO_REAL, t);
              }
              else
              {
                Assert(false) << "Relevant domain: bad type " << t.getType()
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
      Assert(rdl.d_rd[0] != nullptr && rdl.d_rd[1] != nullptr);
      RDomain* rd1 = rdl.d_rd[0]->getParent();
      RDomain* rd2 = rdl.d_rd[1]->getParent();
      if( rd1!=rd2 ){
        rd1->merge( rd2 );
      }
    }
    else
    {
      if (rdl.d_rd[0] != nullptr)
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
  if (d_rel_dom_lit[hasPol][pol].find(n) != d_rel_dom_lit[hasPol][pol].end())
  {
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  RDomainLit& rdl = d_rel_dom_lit[hasPol][pol][n];
  rdl.d_merge = false;
  size_t varCount = 0;
  size_t varCh = 0;
  Assert(n.getNumChildren() == 2);
  for (size_t i = 0; i < 2; i++)
  {
    if (n[i].getKind() == INST_CONSTANT)
    {
      // must get the quantified formula this belongs to, which may be
      // different from q
      Node qi = TermUtil::getInstConstAttr(n[i]);
      unsigned id = n[i].getAttribute(InstVarNumAttribute());
      rdl.d_rd[i] = getRDomain(qi, id, false);
      varCount++;
      varCh = i;
    }
    else
    {
      rdl.d_rd[i] = nullptr;
    }
  }

  Node rAdd;
  Node rVar;
  bool varLhs = true;
  if (varCount == 2)
  {
    // don't merge Int and Real
    rdl.d_merge = (n[0].getType() == n[1].getType());
  }
  else if (varCount == 1)
  {
    rVar = n[varCh];
    rAdd = n[1 - varCh];
    varLhs = (varCh == 0);
    rdl.d_rd[0] = rdl.d_rd[varCh];
    rdl.d_rd[1] = nullptr;
  }
  else if (n[0].getType().isRealOrInt())
  {
    // solve the inequality for one/two variables, if possible
    std::map<Node, Node> msum;
    if (ArithMSum::getMonomialSumLit(n, msum))
    {
      Node var;
      Node var2;
      bool hasNonVar = false;
      for (std::pair<const Node, Node>& m : msum)
      {
        if (!m.first.isNull() && m.first.getKind() == INST_CONSTANT
            && TermUtil::getInstConstAttr(m.first) == q)
        {
          if (var.isNull())
          {
            var = m.first;
          }
          else if (var2.isNull())
          {
            var2 = m.first;
          }
          else
          {
            hasNonVar = true;
          }
        }
        else
        {
          hasNonVar = true;
        }
      }
      Trace("rel-dom") << "Process lit " << n << ", var/var2=" << var << "/"
                       << var2 << std::endl;
      if (!var.isNull())
      {
        Assert(var.hasAttribute(InstVarNumAttribute()));
        if (var2.isNull())
        {
          // single variable solve
          Node veq_c;
          Node val;
          int ires = ArithMSum::isolate(var, msum, veq_c, val, n.getKind());
          if (ires != 0)
          {
            if (veq_c.isNull())
            {
              rVar = var;
              rAdd = val;
              varLhs = (ires == 1);
              rdl.d_rd[0] =
                  getRDomain(q, var.getAttribute(InstVarNumAttribute()), false);
              rdl.d_rd[1] = nullptr;
            }
          }
        }
        else if (!hasNonVar)
        {
          Assert(var2.hasAttribute(InstVarNumAttribute()));
          // merge the domains
          rdl.d_rd[0] =
              getRDomain(q, var.getAttribute(InstVarNumAttribute()), false);
          rdl.d_rd[1] =
              getRDomain(q, var2.getAttribute(InstVarNumAttribute()), false);
          rdl.d_merge = true;
        }
      }
    }
  }
  if (rdl.d_merge)
  {
    // do not merge if constant negative polarity
    if (hasPol && !pol)
    {
      rdl.d_merge = false;
    }
    return;
  }
  if (!rAdd.isNull())
  {
    // Ensure that rAdd has the same type as the variable. This is necessary
    // since GEQ may mix Int and Real, as well as the equality solving above
    // may introduce mixed Int and Real.
    rAdd = Instantiate::ensureType(rAdd, rVar.getType());
  }
  if (!rAdd.isNull() && !TermUtil::hasInstConstAttr(rAdd))
  {
    Trace("rel-dom-debug") << "...add term " << rAdd << ", pol = " << pol
                           << ", kind = " << n.getKind() << std::endl;
    // the negative occurrence adds the term to the domain
    if (!hasPol || !pol)
    {
      rdl.d_val.push_back(rAdd);
    }
    // the positive occurence adds other terms
    if ((!hasPol || pol) && n[0].getType().isInteger())
    {
      if (n.getKind() == EQUAL)
      {
        for (size_t i = 0; i < 2; i++)
        {
          Node roff =
              nm->mkNode(ADD, rAdd, nm->mkConstInt(Rational(i == 0 ? 1 : -1)));
          rdl.d_val.push_back(roff);
        }
      }
      else if (n.getKind() == GEQ)
      {
        Node roff =
            nm->mkNode(ADD, rAdd, nm->mkConstInt(Rational(varLhs ? 1 : -1)));
        rdl.d_val.push_back(roff);
      }
    }
  }
  else
  {
    rdl.d_rd[0] = nullptr;
    rdl.d_rd[1] = nullptr;
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
