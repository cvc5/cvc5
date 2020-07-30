/*********************                                                        */
/*! \file bounded_integers.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bounded integers module
 **
 ** This class manages integer bounds for quantifiers
 **/

#include "theory/quantifiers/fmf/bounded_integers.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fmf/model_engine.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;

BoundedIntegers::IntRangeDecisionHeuristic::IntRangeDecisionHeuristic(
    Node r,
    context::Context* c,
    context::Context* u,
    Valuation valuation,
    bool isProxy)
    : DecisionStrategyFmf(c, valuation), d_range(r), d_ranges_proxied(u)
{
  if( options::fmfBoundLazy() ){
    d_proxy_range = isProxy ? r : NodeManager::currentNM()->mkSkolem( "pbir", r.getType() );
  }else{
    d_proxy_range = r;
  }
  if( !isProxy ){
    Trace("bound-int") << "Introduce proxy " << d_proxy_range << " for " << d_range << std::endl;
  }
}
Node BoundedIntegers::IntRangeDecisionHeuristic::mkLiteral(unsigned n)
{
  NodeManager* nm = NodeManager::currentNM();
  Node cn = nm->mkConst(Rational(n == 0 ? 0 : n - 1));
  return nm->mkNode(n == 0 ? LT : LEQ, d_proxy_range, cn);
}

Node BoundedIntegers::IntRangeDecisionHeuristic::proxyCurrentRangeLemma()
{
  if (d_range == d_proxy_range)
  {
    return Node::null();
  }
  unsigned curr = 0;
  if (!getAssertedLiteralIndex(curr))
  {
    return Node::null();
  }
  if (d_ranges_proxied.find(curr) != d_ranges_proxied.end())
  {
    return Node::null();
  }
  d_ranges_proxied[curr] = true;
  NodeManager* nm = NodeManager::currentNM();
  Node currLit = getLiteral(curr);
  Node lem =
      nm->mkNode(EQUAL,
                 currLit,
                 nm->mkNode(curr == 0 ? LT : LEQ,
                            d_range,
                            nm->mkConst(Rational(curr == 0 ? 0 : curr - 1))));
  return lem;
}

BoundedIntegers::BoundedIntegers(context::Context* c, QuantifiersEngine* qe)
    : QuantifiersModule(qe)
{
}

BoundedIntegers::~BoundedIntegers() {}

void BoundedIntegers::presolve() {
  d_bnd_it.clear();
}

bool BoundedIntegers::hasNonBoundVar( Node f, Node b, std::map< Node, bool >& visited ) {
  if( visited.find( b )==visited.end() ){
    visited[b] = true;
    if( b.getKind()==BOUND_VARIABLE ){
      if( !isBound( f, b ) ){
        return true;
      }
    }else{
      for( unsigned i=0; i<b.getNumChildren(); i++ ){
        if( hasNonBoundVar( f, b[i], visited ) ){
          return true;
        }
      }
    }
  }
  return false;
}
bool BoundedIntegers::hasNonBoundVar( Node f, Node b ) {
  std::map< Node, bool > visited;
  return hasNonBoundVar( f, b, visited );
}

bool BoundedIntegers::processEqDisjunct( Node q, Node n, Node& v, std::vector< Node >& v_cases ) {
  if( n.getKind()==EQUAL ){
    for( unsigned i=0; i<2; i++ ){
      Node t = n[i];
      if( !hasNonBoundVar( q, n[1-i] ) ){
        if( t==v ){
          v_cases.push_back( n[1-i] );
          return true;
        }else if( v.isNull() && t.getKind()==BOUND_VARIABLE ){
          v = t;
          v_cases.push_back( n[1-i] );
          return true;
        }
      }
    }
  }
  return false;
}

void BoundedIntegers::processMatchBoundVars( Node q, Node n, std::vector< Node >& bvs, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==BOUND_VARIABLE && !isBound( q, n ) ){
      bvs.push_back( n );
    //injective operators
    }else if( n.getKind()==kind::APPLY_CONSTRUCTOR ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        processMatchBoundVars( q, n[i], bvs, visited );
      }
    }    
  }
}

void BoundedIntegers::process( Node q, Node n, bool pol,
                               std::map< Node, unsigned >& bound_lit_type_map,
                               std::map< int, std::map< Node, Node > >& bound_lit_map,
                               std::map< int, std::map< Node, bool > >& bound_lit_pol_map,
                               std::map< int, std::map< Node, Node > >& bound_int_range_term,
                               std::map< Node, std::vector< Node > >& bound_fixed_set ){
  if( n.getKind()==OR || n.getKind()==AND ){
    if( (n.getKind()==OR)==pol ){
      for( unsigned i=0; i<n.getNumChildren(); i++) {
        process( q, n[i], pol, bound_lit_type_map, bound_lit_map, bound_lit_pol_map, bound_int_range_term, bound_fixed_set );
      }
    }else{
      //if we are ( x != t1 ^ ...^ x != tn ), then x can be bound to { t1...tn }
      Node conj = n;
      if( !pol ){
        conj = TermUtil::simpleNegate( conj );
      }
      Trace("bound-int-debug") << "Process possible finite disequality conjunction : " << conj << std::endl;
      Assert(conj.getKind() == AND);
      Node v;
      std::vector< Node > v_cases;
      bool success = true;
      for( unsigned i=0; i<conj.getNumChildren(); i++ ){
        if( conj[i].getKind()==NOT && processEqDisjunct( q, conj[i][0], v, v_cases ) ){
          //continue
        }else{
          Trace("bound-int-debug") << "...failed due to " << conj[i] << std::endl;
          success = false;
          break;
        }
      }
      if( success && !isBound( q, v ) ){
        Trace("bound-int-debug") << "Success with variable " << v << std::endl;
        bound_lit_type_map[v] = BOUND_FIXED_SET;
        bound_lit_map[3][v] = n;
        bound_lit_pol_map[3][v] = pol;
        bound_fixed_set[v].clear();
        bound_fixed_set[v].insert( bound_fixed_set[v].end(), v_cases.begin(), v_cases.end() );
      }
    }
  }else if( n.getKind()==EQUAL ){
    if( !pol ){
      // non-applied DER on x != t, x can be bound to { t }
      Node v;
      std::vector< Node > v_cases;
      if( processEqDisjunct( q, n, v, v_cases ) ){
        if( !isBound( q, v ) ){
          bound_lit_type_map[v] = BOUND_FIXED_SET;
          bound_lit_map[3][v] = n;
          bound_lit_pol_map[3][v] = pol;
          Assert(v_cases.size() == 1);
          bound_fixed_set[v].clear();
          bound_fixed_set[v].push_back( v_cases[0] );
        }
      }
    }  
  }else if( n.getKind()==NOT ){
    process( q, n[0], !pol, bound_lit_type_map, bound_lit_map, bound_lit_pol_map, bound_int_range_term, bound_fixed_set );
  }else if( n.getKind()==GEQ ){
    if( n[0].getType().isInteger() ){
      std::map< Node, Node > msum;
      if (ArithMSum::getMonomialSumLit(n, msum))
      {
        Trace("bound-int-debug") << "literal (polarity = " << pol << ") " << n << " is monomial sum : " << std::endl;
        ArithMSum::debugPrintMonomialSum(msum, "bound-int-debug");
        for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
          if ( !it->first.isNull() && it->first.getKind()==BOUND_VARIABLE && !isBound( q, it->first ) ){
            //if not bound in another way
            if( bound_lit_type_map.find( it->first )==bound_lit_type_map.end() || bound_lit_type_map[it->first] == BOUND_INT_RANGE ){
              Node veq;
              if (ArithMSum::isolate(it->first, msum, veq, GEQ) != 0)
              {
                Node n1 = veq[0];
                Node n2 = veq[1];
                if(pol){
                  //flip
                  n1 = veq[1];
                  n2 = veq[0];
                  if( n1.getKind()==BOUND_VARIABLE ){
                    n2 = ArithMSum::offset(n2, 1);
                  }else{
                    n1 = ArithMSum::offset(n1, -1);
                  }
                  veq = NodeManager::currentNM()->mkNode( GEQ, n1, n2 );
                }
                Trace("bound-int-debug") << "Isolated for " << it->first << " : (" << n1 << " >= " << n2 << ")" << std::endl;
                Node t = n1==it->first ? n2 : n1;
                if( !hasNonBoundVar( q, t ) ) {
                  Trace("bound-int-debug") << "The bound is relevant." << std::endl;
                  int loru = n1==it->first ? 0 : 1;
                  bound_lit_type_map[it->first] = BOUND_INT_RANGE;
                  bound_int_range_term[loru][it->first] = t;
                  bound_lit_map[loru][it->first] = n;
                  bound_lit_pol_map[loru][it->first] = pol;
                }else{
                  Trace("bound-int-debug") << "The term " << t << " has non-bound variable." << std::endl;
                }
              }
            }
          }
        }
      }
    }
  }else if( n.getKind()==MEMBER ){
    if( !pol && !hasNonBoundVar( q, n[1] ) ){
      std::vector< Node > bound_vars;
      std::map< Node, bool > visited;
      processMatchBoundVars( q, n[0], bound_vars, visited );
      for( unsigned i=0; i<bound_vars.size(); i++ ){
        Node v = bound_vars[i];
        Trace("bound-int-debug") << "literal (polarity = " << pol << ") " << n << " is membership." << std::endl;
        bound_lit_type_map[v] = BOUND_SET_MEMBER;
        bound_lit_map[2][v] = n;
        bound_lit_pol_map[2][v] = pol;
      }
    }
  }else{
    Assert(n.getKind() != LEQ && n.getKind() != LT && n.getKind() != GT);
  }
}

bool BoundedIntegers::needsCheck( Theory::Effort e ) {
  return e==Theory::EFFORT_LAST_CALL;
}

void BoundedIntegers::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }
  Trace("bint-engine") << "---Bounded Integers---" << std::endl;
  bool addedLemma = false;
  // make sure proxies are up-to-date with range
  for (const Node& r : d_ranges)
  {
    Node prangeLem = d_rms[r]->proxyCurrentRangeLemma();
    if (!prangeLem.isNull())
    {
      Trace("bound-int-lemma")
          << "*** bound int : proxy lemma : " << prangeLem << std::endl;
      d_quantEngine->addLemma(prangeLem);
      addedLemma = true;
    }
  }
  Trace("bint-engine") << "   addedLemma = " << addedLemma << std::endl;
}
void BoundedIntegers::setBoundedVar(Node q, Node v, BoundVarType bound_type)
{
  d_bound_type[q][v] = bound_type;
  d_set_nums[q][v] = d_set[q].size();
  d_set[q].push_back( v );
  Trace("bound-int-var") << "Bound variable #" << d_set_nums[q][v] << " : " << v
                         << std::endl;
}

void BoundedIntegers::checkOwnership(Node f)
{
  //this needs to be done at preregister since it affects e.g. QuantDSplit's preregister
  Trace("bound-int") << "check ownership quantifier " << f << std::endl;
  NodeManager* nm = NodeManager::currentNM();

  bool success;
  do{
    std::map< Node, unsigned > bound_lit_type_map;
    std::map< int, std::map< Node, Node > > bound_lit_map;
    std::map< int, std::map< Node, bool > > bound_lit_pol_map;
    std::map< int, std::map< Node, Node > > bound_int_range_term;
    std::map< Node, std::vector< Node > > bound_fixed_set;
    success = false;
    process( f, f[1], true, bound_lit_type_map, bound_lit_map, bound_lit_pol_map, bound_int_range_term, bound_fixed_set );
    //for( std::map< Node, Node >::iterator it = d_bounds[0][f].begin(); it != d_bounds[0][f].end(); ++it ){
    for( std::map< Node, unsigned >::iterator it = bound_lit_type_map.begin(); it != bound_lit_type_map.end(); ++it ){
      Node v = it->first;
      if( !isBound( f, v ) ){
        bool setBoundVar = false;
        if( it->second==BOUND_INT_RANGE ){
          //must have both
          std::map<Node, Node>& blm0 = bound_lit_map[0];
          std::map<Node, Node>& blm1 = bound_lit_map[1];
          if (blm0.find(v) != blm0.end() && blm1.find(v) != blm1.end())
          {
            setBoundedVar( f, v, BOUND_INT_RANGE );
            setBoundVar = true;
            for( unsigned b=0; b<2; b++ ){
              //set the bounds
              Assert(bound_int_range_term[b].find(v)
                     != bound_int_range_term[b].end());
              d_bounds[b][f][v] = bound_int_range_term[b][v];
            }
            Node r = nm->mkNode(MINUS, d_bounds[1][f][v], d_bounds[0][f][v]);
            d_range[f][v] = Rewriter::rewrite(r);
            Trace("bound-int") << "Variable " << v << " is bound because of int range literals " << bound_lit_map[0][v] << " and " << bound_lit_map[1][v] << std::endl;
          }
        }else if( it->second==BOUND_SET_MEMBER ){
          // only handles infinite element types currently (cardinality is not
          // supported for finite element types #1123). Regardless, this is
          // typically not a limitation since this variable can be bound in a
          // standard way below since its type is finite.
          if (!v.getType().isInterpretedFinite())
          {
            setBoundedVar(f, v, BOUND_SET_MEMBER);
            setBoundVar = true;
            d_setm_range[f][v] = bound_lit_map[2][v][1];
            d_setm_range_lit[f][v] = bound_lit_map[2][v];
            d_range[f][v] = nm->mkNode(CARD, d_setm_range[f][v]);
            Trace("bound-int") << "Variable " << v
                               << " is bound because of set membership literal "
                               << bound_lit_map[2][v] << std::endl;
          }
        }else if( it->second==BOUND_FIXED_SET ){
          setBoundedVar(f, v, BOUND_FIXED_SET);
          setBoundVar = true;
          for (unsigned i = 0; i < bound_fixed_set[v].size(); i++)
          {
            Node t = bound_fixed_set[v][i];
            if (expr::hasBoundVar(t))
            {
              d_fixed_set_ngr_range[f][v].push_back(t);
            }
            else
            {
              d_fixed_set_gr_range[f][v].push_back(t);
            }
          }
          Trace("bound-int") << "Variable " << v
                             << " is bound because of disequality conjunction "
                             << bound_lit_map[3][v] << std::endl;
        }
        if( setBoundVar ){
          success = true;
          //set Attributes on literals
          for( unsigned b=0; b<2; b++ ){
            std::map<Node, Node>& blm = bound_lit_map[b];
            if (blm.find(v) != blm.end())
            {
              std::map<Node, bool>& blmp = bound_lit_pol_map[b];
              // WARNING_CANDIDATE:
              // This assertion may fail. We intentionally do not enable this in
              // production as it is considered safe for this to fail. We fail
              // the assertion in debug mode to have this instance raised to
              // our attention.
              Assert(blmp.find(v) != blmp.end());
              BoundIntLitAttribute bila;
              bound_lit_map[b][v].setAttribute(bila, blmp[v] ? 1 : 0);
            }
            else
            {
              Assert(it->second != BOUND_INT_RANGE);
            }
          }
        }
      }
    }
    if( !success ){
      //resort to setting a finite bound on a variable
      for( unsigned i=0; i<f[0].getNumChildren(); i++) {
        if( d_bound_type[f].find( f[0][i] )==d_bound_type[f].end() ){
          TypeNode tn = f[0][i].getType();
          if ((tn.isSort() && tn.isInterpretedFinite())
              || d_quantEngine->getTermEnumeration()->mayComplete(tn))
          {
            success = true;
            setBoundedVar( f, f[0][i], BOUND_FINITE );
            break;
          }
        }
      }
    }
  }while( success );
  
  if( Trace.isOn("bound-int") ){
    Trace("bound-int") << "Bounds are : " << std::endl;
    for( unsigned i=0; i<f[0].getNumChildren(); i++) {
      Node v = f[0][i];
      if( std::find( d_set[f].begin(), d_set[f].end(), v )!=d_set[f].end() ){
        Assert(d_bound_type[f].find(v) != d_bound_type[f].end());
        if( d_bound_type[f][v]==BOUND_INT_RANGE ){
          Trace("bound-int") << "  " << d_bounds[0][f][v] << " <= " << v << " <= " << d_bounds[1][f][v] << " (range is " << d_range[f][v] << ")" << std::endl;
        }else if( d_bound_type[f][v]==BOUND_SET_MEMBER ){
          if( d_setm_range_lit[f][v][0]==v ){
            Trace("bound-int") << "  " << v << " in " << d_setm_range[f][v] << std::endl;
          }else{
            Trace("bound-int") << "  " << v << " unifiable in " << d_setm_range_lit[f][v] << std::endl;
          }
        }else if( d_bound_type[f][v]==BOUND_FIXED_SET ){
          Trace("bound-int") << "  " << v << " in { ";
          for (TNode fnr : d_fixed_set_ngr_range[f][v])
          {
            Trace("bound-int") << fnr << " ";
          }
          for (TNode fgr : d_fixed_set_gr_range[f][v])
          {
            Trace("bound-int") << fgr << " ";
          }
          Trace("bound-int") << "}" << std::endl;
        }else if( d_bound_type[f][v]==BOUND_FINITE ){
          Trace("bound-int") << "  " << v << " has small finite type." << std::endl;
        }else{
          Trace("bound-int") << "  " << v << " has unknown bound." << std::endl;
          Assert(false);
        }
      }else{
        Trace("bound-int") << "  " << "*** " << v << " is unbounded." << std::endl;
      }
    }
  }
  
  bool bound_success = true;
  for( unsigned i=0; i<f[0].getNumChildren(); i++) {
    if( d_bound_type[f].find( f[0][i] )==d_bound_type[f].end() ){
      Trace("bound-int-warn") << "Warning : Bounded Integers : Due to quantification on " << f[0][i] << ", could not find bounds for " << f << std::endl;
      bound_success = false;
      break;
    }
  }
  
  if( bound_success ){
    d_bound_quants.push_back( f );
    for( unsigned i=0; i<d_set[f].size(); i++) {
      Node v = d_set[f][i];
      std::map< Node, Node >::iterator itr = d_range[f].find( v );
      if( itr != d_range[f].end() ){
        Node r = itr->second;
        Assert(!r.isNull());
        bool isProxy = false;
        if (expr::hasBoundVar(r))
        {
          // introduce a new bound
          Node new_range = NodeManager::currentNM()->mkSkolem(
              "bir", r.getType(), "bound for term");
          d_nground_range[f][v] = r;
          d_range[f][v] = new_range;
          r = new_range;
          isProxy = true;
        }
        if( !r.isConst() ){
          if (d_rms.find(r) == d_rms.end())
          {
            Trace("bound-int") << "For " << v << ", bounded Integer Module will try to minimize : " << r << std::endl;
            d_ranges.push_back( r );
            d_rms[r].reset(
                new IntRangeDecisionHeuristic(r,
                                              d_quantEngine->getSatContext(),
                                              d_quantEngine->getUserContext(),
                                              d_quantEngine->getValuation(),
                                              isProxy));
            d_quantEngine->getTheoryEngine()
                ->getDecisionManager()
                ->registerStrategy(DecisionManager::STRAT_QUANT_BOUND_INT_SIZE,
                                   d_rms[r].get());
          }
        }
      }
    }
  }
}

bool BoundedIntegers::isBound(Node q, Node v) const
{
  std::map<Node, std::vector<Node> >::const_iterator its = d_set.find(q);
  if (its == d_set.end())
  {
    return false;
  }
  return std::find(its->second.begin(), its->second.end(), v)
         != its->second.end();
}

BoundVarType BoundedIntegers::getBoundVarType(Node q, Node v) const
{
  std::map<Node, std::map<Node, BoundVarType> >::const_iterator itb =
      d_bound_type.find(q);
  if (itb == d_bound_type.end())
  {
    return BOUND_NONE;
  }
  std::map<Node, BoundVarType>::const_iterator it = itb->second.find(v);
  if (it == itb->second.end())
  {
    return BOUND_NONE;
  }
  return it->second;
}

void BoundedIntegers::getBoundVarIndices(Node q,
                                         std::vector<unsigned>& indices) const
{
  std::map<Node, std::vector<Node> >::const_iterator it = d_set.find(q);
  if (it != d_set.end())
  {
    for (const Node& v : it->second)
    {
      indices.push_back(d_quantEngine->getTermUtil()->getVariableNum(q, v));
    }
  }
}

void BoundedIntegers::getBounds( Node f, Node v, RepSetIterator * rsi, Node & l, Node & u ) {
  l = d_bounds[0][f][v];
  u = d_bounds[1][f][v];
  if( d_nground_range[f].find(v)!=d_nground_range[f].end() ){
    //get the substitution
    std::vector< Node > vars;
    std::vector< Node > subs;
    if( getRsiSubsitution( f, v, vars, subs, rsi ) ){
      u = u.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
      l = l.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    }else{
      u = Node::null();
      l = Node::null();
    }
  }
}

void BoundedIntegers::getBoundValues( Node f, Node v, RepSetIterator * rsi, Node & l, Node & u ) {
  getBounds( f, v, rsi, l, u );
  Trace("bound-int-rsi") << "Get value in model for..." << l << " and " << u << std::endl;
  if( !l.isNull() ){
    l = d_quantEngine->getModel()->getValue( l );
  }
  if( !u.isNull() ){
    u = d_quantEngine->getModel()->getValue( u );
  }
  Trace("bound-int-rsi") << "Value is " << l << " ... " << u << std::endl;
  return;
}

bool BoundedIntegers::isGroundRange(Node q, Node v)
{
  if (isBound(q, v))
  {
    if (d_bound_type[q][v] == BOUND_INT_RANGE)
    {
      return !expr::hasBoundVar(getLowerBound(q, v))
             && !expr::hasBoundVar(getUpperBound(q, v));
    }
    else if (d_bound_type[q][v] == BOUND_SET_MEMBER)
    {
      return !expr::hasBoundVar(d_setm_range[q][v]);
    }
    else if (d_bound_type[q][v] == BOUND_FIXED_SET)
    {
      return !d_fixed_set_ngr_range[q][v].empty();
    }
  }
  return false;
}

Node BoundedIntegers::getSetRange( Node q, Node v, RepSetIterator * rsi ) {
  Node sr = d_setm_range[q][v];
  if( d_nground_range[q].find(v)!=d_nground_range[q].end() ){
    Trace("bound-int-rsi-debug")
        << sr << " is non-ground, apply substitution..." << std::endl;
    //get the substitution
    std::vector< Node > vars;
    std::vector< Node > subs;
    if( getRsiSubsitution( q, v, vars, subs, rsi ) ){
      Trace("bound-int-rsi-debug")
          << "  apply " << vars << " -> " << subs << std::endl;
      sr = sr.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    }else{
      sr = Node::null();
    }
  }
  return sr;
}

Node BoundedIntegers::getSetRangeValue( Node q, Node v, RepSetIterator * rsi ) {
  Node sr = getSetRange( q, v, rsi );
  if (sr.isNull())
  {
    return sr;
  }
  Trace("bound-int-rsi") << "Get value in model for..." << sr << std::endl;
  Assert(!expr::hasFreeVar(sr));
  Node sro = sr;
  sr = d_quantEngine->getModel()->getValue(sr);
  // if non-constant, then sr does not occur in the model, we fail
  if (!sr.isConst())
  {
    return Node::null();
  }
  Trace("bound-int-rsi") << "Value is " << sr << std::endl;
  if (sr.getKind() == EMPTYSET)
  {
    return sr;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node nsr;
  TypeNode tne = sr.getType().getSetElementType();

  // we can use choice functions for canonical symbolic instantiations
  unsigned srCard = 0;
  while (sr.getKind() == UNION)
  {
    srCard++;
    sr = sr[0];
  }
  Assert(sr.getKind() == SINGLETON);
  srCard++;
  // choices[i] stores the canonical symbolic representation of the (i+1)^th
  // element of sro
  std::vector<Node> choices;
  Node srCardN = nm->mkNode(CARD, sro);
  Node choice_i;
  for (unsigned i = 0; i < srCard; i++)
  {
    if (i == d_setm_choice[sro].size())
    {
      choice_i = nm->mkBoundVar(tne);
      choices.push_back(choice_i);
      Node cBody = nm->mkNode(MEMBER, choice_i, sro);
      if (choices.size() > 1)
      {
        cBody = nm->mkNode(AND, cBody, nm->mkNode(DISTINCT, choices));
      }
      choices.pop_back();
      Node bvl = nm->mkNode(BOUND_VAR_LIST, choice_i);
      Node cMinCard = nm->mkNode(LEQ, srCardN, nm->mkConst(Rational(i)));
      choice_i = nm->mkNode(WITNESS, bvl, nm->mkNode(OR, cMinCard, cBody));
      d_setm_choice[sro].push_back(choice_i);
    }
    Assert(i < d_setm_choice[sro].size());
    choice_i = d_setm_choice[sro][i];
    choices.push_back(choice_i);
    Node sChoiceI = nm->mkNode(SINGLETON, choice_i);
    if (nsr.isNull())
    {
      nsr = sChoiceI;
    }
    else
    {
      nsr = nm->mkNode(UNION, nsr, sChoiceI);
    }
  }
  // turns the concrete model value of sro into a canonical representation
  //   e.g.
  // singleton(0) union singleton(1)
  //   becomes
  // C1 union ( witness y. card(S)<=1 OR ( y in S AND distinct( y, C1 ) ) )
  // where C1 = ( witness x. card(S)<=0 OR x in S ).
  Trace("bound-int-rsi") << "...reconstructed " << nsr << std::endl;
  return nsr;
}

bool BoundedIntegers::getRsiSubsitution( Node q, Node v, std::vector< Node >& vars, std::vector< Node >& subs, RepSetIterator * rsi ) {

  Trace("bound-int-rsi") << "Get bound value in model of variable " << v << std::endl;
  Assert(d_set_nums[q].find(v) != d_set_nums[q].end());
  int vindex = d_set_nums[q][v];
  Assert(d_set_nums[q][v] == vindex);
  Trace("bound-int-rsi-debug") << "  index order is " << vindex << std::endl;
  //must take substitution for all variables that are iterating at higher level
  for( int i=0; i<vindex; i++) {
    Assert(d_set_nums[q][d_set[q][i]] == i);
    Trace("bound-int-rsi") << "Look up the value for " << d_set[q][i] << " " << i << std::endl;
    int vo = rsi->getVariableOrder(i);
    Assert(q[0][vo] == d_set[q][i]);
    Node t = rsi->getCurrentTerm(vo, true);
    Trace("bound-int-rsi") << "term : " << t << std::endl;
    vars.push_back( d_set[q][i] );
    subs.push_back( t );
  }
  
  //check if it has been instantiated
  if( !vars.empty() && !d_bnd_it[q][v].hasInstantiated(subs) ){
    if( d_bound_type[q][v]==BOUND_INT_RANGE || d_bound_type[q][v]==BOUND_SET_MEMBER ){
      //must add the lemma
      Node nn = d_nground_range[q][v];
      nn = nn.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
      Node lem = NodeManager::currentNM()->mkNode( LEQ, nn, d_range[q][v] );
      Trace("bound-int-lemma") << "*** Add lemma to minimize instantiated non-ground term " << lem << std::endl;
      d_quantEngine->getOutputChannel().lemma(lem, LemmaProperty::PREPROCESS);
    }
    return false;
  }else{
    return true;
  }
}

Node BoundedIntegers::matchBoundVar( Node v, Node t, Node e ){
  if( t==v ){
    return e;
  }else if( t.getKind()==kind::APPLY_CONSTRUCTOR ){
    if( e.getKind()==kind::APPLY_CONSTRUCTOR ){
      if( t.getOperator() != e.getOperator() ) {
        return Node::null();
      }
    }
    NodeManager* nm = NodeManager::currentNM();
    const DType& dt = datatypes::utils::datatypeOf(t.getOperator());
    unsigned index = datatypes::utils::indexOf(t.getOperator());
    for( unsigned i=0; i<t.getNumChildren(); i++ ){
      Node u;
      if( e.getKind()==kind::APPLY_CONSTRUCTOR ){
        u = matchBoundVar( v, t[i], e[i] );
      }else{
        Node se = nm->mkNode(APPLY_SELECTOR_TOTAL,
                             dt[index].getSelectorInternal(e.getType(), i),
                             e);
        u = matchBoundVar( v, t[i], se );
      }
      if( !u.isNull() ){
        return u;
      }
    }
  }
  return Node::null();
}

bool BoundedIntegers::getBoundElements( RepSetIterator * rsi, bool initial, Node q, Node v, std::vector< Node >& elements ) {
  if( initial || !isGroundRange( q, v ) ){
    elements.clear();
    BoundVarType bvt = getBoundVarType(q, v);
    if( bvt==BOUND_INT_RANGE ){
      Node l, u;
      getBoundValues( q, v, rsi, l, u );
      if( l.isNull() || u.isNull() ){
        Trace("bound-int-warn") << "WARNING: Could not find integer bounds in model for " << v << " in " << q << std::endl;
        //failed, abort the iterator
        return false;
      }else{
        Trace("bound-int-rsi") << "Can limit bounds of " << v << " to " << l << "..." << u << std::endl;
        Node range = Rewriter::rewrite( NodeManager::currentNM()->mkNode( MINUS, u, l ) );
        Node ra = Rewriter::rewrite( NodeManager::currentNM()->mkNode( LEQ, range, NodeManager::currentNM()->mkConst( Rational( 9999 ) ) ) );
        Node tl = l;
        Node tu = u;
        getBounds( q, v, rsi, tl, tu );
        Assert(!tl.isNull() && !tu.isNull());
        if( ra==d_quantEngine->getTermUtil()->d_true ){
          long rr = range.getConst<Rational>().getNumerator().getLong()+1;
          Trace("bound-int-rsi")  << "Actual bound range is " << rr << std::endl;
          for( unsigned k=0; k<rr; k++ ){
            Node t = NodeManager::currentNM()->mkNode(PLUS, tl, NodeManager::currentNM()->mkConst( Rational(k) ) );
            t = Rewriter::rewrite( t );
            elements.push_back( t );
          }
          return true;
        }else{
          Trace("fmf-incomplete") << "Incomplete because of integer quantification, bounds are too big for " << v << "." << std::endl;
          return false;
        }
      }
    }else if( bvt==BOUND_SET_MEMBER  ){ 
      Node srv = getSetRangeValue( q, v, rsi );
      if( srv.isNull() ){
        Trace("bound-int-warn") << "WARNING: Could not find set bound in model for " << v << " in " << q << std::endl;
        return false;
      }else{
        Trace("bound-int-rsi") << "Bounded by set membership : " << srv << std::endl;
        if( srv.getKind()!=EMPTYSET ){
          //collect the elements
          while( srv.getKind()==UNION ){
            Assert(srv[1].getKind() == kind::SINGLETON);
            elements.push_back( srv[1][0] );
            srv = srv[0];
          }
          Assert(srv.getKind() == kind::SINGLETON);
          elements.push_back( srv[0] );
          //check if we need to do matching, for literals like ( tuple( v ) in S )
          Node t = d_setm_range_lit[q][v][0];
          if( t!=v ){
            std::vector< Node > elements_tmp;
            elements_tmp.insert( elements_tmp.end(), elements.begin(), elements.end() );
            elements.clear();
            for( unsigned i=0; i<elements_tmp.size(); i++ ){
              //do matching to determine v -> u
              Node u = matchBoundVar( v, t, elements_tmp[i] );
              Trace("bound-int-rsi-debug") << "  unification : " << elements_tmp[i] << " = " << t << " yields " << v << " -> " << u << std::endl;
              if( !u.isNull() ){
                elements.push_back( u );
              }
            }
          }
        }
        return true;
      }
    }else if( bvt==BOUND_FIXED_SET ){
      std::map< Node, std::vector< Node > >::iterator it = d_fixed_set_gr_range[q].find( v );
      if( it!=d_fixed_set_gr_range[q].end() ){
        for( unsigned i=0; i<it->second.size(); i++ ){
          elements.push_back( it->second[i] );
        }
      }
      it = d_fixed_set_ngr_range[q].find( v );
      if( it!=d_fixed_set_ngr_range[q].end() ){
        std::vector< Node > vars;
        std::vector< Node > subs;
        if( getRsiSubsitution( q, v, vars, subs, rsi ) ){
          for( unsigned i=0; i<it->second.size(); i++ ){
            Node t = it->second[i].substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
            elements.push_back( t );
          }
          return true;
        }else{
          return false;
        }
      }else{
        return true;
      }
    }else{
      return false;
    }
  }else{
    //no change required
    return true;
  }
}
