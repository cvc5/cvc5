/*********************                                                        */
/*! \file datatypes_sygus.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus utilities for theory of datatypes
 **
 ** Implementation of sygus utilities for theory of datatypes
 **/

#include "theory/datatypes/datatypes_sygus.h"

#include "expr/node_manager.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/datatypes/theory_datatypes.h"
#include "theory/quantifiers/sygus/sygus_explain.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_model.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

SygusSymBreakNew::SygusSymBreakNew(TheoryDatatypes* td,
                                   QuantifiersEngine* qe,
                                   context::Context* c)
    : d_td(td),
      d_tds(qe->getTermDatabaseSygus()),
      d_ssb(qe),
      d_testers(c),
      d_testers_exp(c),
      d_active_terms(c),
      d_currTermSize(c)
{
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_true = NodeManager::currentNM()->mkConst(true);
}

SygusSymBreakNew::~SygusSymBreakNew() {

}

/** add tester */
void SygusSymBreakNew::assertTester( int tindex, TNode n, Node exp, std::vector< Node >& lemmas ) {
  registerTerm( n, lemmas );
  // check if this is a relevant (sygus) term
  if( d_term_to_anchor.find( n )!=d_term_to_anchor.end() ){
    Trace("sygus-sb-debug2") << "Sygus : process tester : " << exp << std::endl;
    // if not already active (may have duplicate calls for the same tester)
    if( d_active_terms.find( n )==d_active_terms.end() ) {
      d_testers[n] = tindex;
      d_testers_exp[n] = exp;
      
      // check if parent is active
      bool do_add = true;
      if( options::sygusSymBreakLazy() ){
        if( n.getKind()==kind::APPLY_SELECTOR_TOTAL ){
          NodeSet::const_iterator it = d_active_terms.find( n[0] );
          if( it==d_active_terms.end() ){
            do_add = false;
          }else{
            //this must be a proper selector
            IntMap::const_iterator itt = d_testers.find( n[0] );
            Assert( itt!=d_testers.end() );
            int ptindex = (*itt).second;
            TypeNode ptn = n[0].getType();
            const Datatype& pdt = ((DatatypeType)ptn.toType()).getDatatype();
            int sindex_in_parent = pdt[ptindex].getSelectorIndexInternal( n.getOperator().toExpr() );
            // the tester is irrelevant in this branch
            if( sindex_in_parent==-1 ){
              do_add = false;
            }
          }
        }
      }
      if( do_add ){
        assertTesterInternal( tindex, n, exp, lemmas );
      }else{
        Trace("sygus-sb-debug2") << "...ignore inactive tester : " << exp << std::endl;
      }
    }else{
      Trace("sygus-sb-debug2") << "...ignore repeated tester : " << exp << std::endl;
    }
  }else{
    Trace("sygus-sb-debug2") << "...ignore non-sygus tester : " << exp << std::endl;
  }
}

void SygusSymBreakNew::assertFact( Node n, bool polarity, std::vector< Node >& lemmas ) {
  if (n.getKind() == kind::DT_SYGUS_BOUND)
  {
    Node m = n[0];
    Trace("sygus-fair") << "Have sygus bound : " << n << ", polarity=" << polarity << " on measure " << m << std::endl;
    registerMeasureTerm( m );
    if( options::sygusFair()==SYGUS_FAIR_DT_SIZE ){
      std::map<Node, std::unique_ptr<SygusSizeDecisionStrategy>>::iterator its =
          d_szinfo.find(m);
      Assert( its!=d_szinfo.end() );
      Node mt = its->second->getOrMkMeasureValue(lemmas);
      //it relates the measure term to arithmetic
      Node blem = n.eqNode( NodeManager::currentNM()->mkNode( kind::LEQ, mt, n[1] ) );
      lemmas.push_back( blem );
    }
    if( polarity ){
      unsigned s = n[1].getConst<Rational>().getNumerator().toUnsignedInt();
      notifySearchSize( m, s, n, lemmas );
    }
  }else if( n.getKind() == kind::DT_HEIGHT_BOUND || n.getKind()==DT_SIZE_BOUND ){
    //reduce to arithmetic TODO ?

  }
}

Node SygusSymBreakNew::getTermOrderPredicate( Node n1, Node n2 ) {
  NodeManager* nm = NodeManager::currentNM();
  std::vector< Node > comm_disj;
  // (1) size of left is greater than size of right
  Node sz_less =
      nm->mkNode(GT, nm->mkNode(DT_SIZE, n1), nm->mkNode(DT_SIZE, n2));
  comm_disj.push_back( sz_less );
  // (2) ...or sizes are equal and first child is less by term order
  std::vector<Node> sz_eq_cases;
  Node sz_eq =
      nm->mkNode(EQUAL, nm->mkNode(DT_SIZE, n1), nm->mkNode(DT_SIZE, n2));
  sz_eq_cases.push_back( sz_eq );
  if( options::sygusOpt1() ){
    TypeNode tnc = n1.getType();
    const Datatype& cdt = ((DatatypeType)(tnc).toType()).getDatatype();
    for( unsigned j=0; j<cdt.getNumConstructors(); j++ ){
      std::vector<Node> case_conj;
      for (unsigned k = 0; k < j; k++)
      {
        case_conj.push_back(DatatypesRewriter::mkTester(n2, k, cdt).negate());
      }
      if (!case_conj.empty())
      {
        Node corder = nm->mkNode(
            kind::OR,
            DatatypesRewriter::mkTester(n1, j, cdt).negate(),
            case_conj.size() == 1 ? case_conj[0]
                                  : nm->mkNode(kind::AND, case_conj));
        sz_eq_cases.push_back(corder);
      }
    }
  }
  Node sz_eqc = sz_eq_cases.size() == 1 ? sz_eq_cases[0]
                                        : nm->mkNode(kind::AND, sz_eq_cases);
  comm_disj.push_back( sz_eqc );

  return nm->mkNode(kind::OR, comm_disj);
}

void SygusSymBreakNew::registerTerm( Node n, std::vector< Node >& lemmas ) {
  if( d_is_top_level.find( n )==d_is_top_level.end() ){
    d_is_top_level[n] = false;
    TypeNode tn = n.getType();
    unsigned d = 0;
    bool is_top_level = false;
    bool success = false;
    if( n.getKind()==kind::APPLY_SELECTOR_TOTAL ){
      registerTerm( n[0], lemmas );
      std::unordered_map<Node, Node, NodeHashFunction>::iterator it =
          d_term_to_anchor.find(n[0]);
      if( it!=d_term_to_anchor.end() ) {
        d_term_to_anchor[n] = it->second;
        unsigned sel_weight =
            d_tds->getSelectorWeight(n[0].getType(), n.getOperator());
        d = d_term_to_depth[n[0]] + sel_weight;
        is_top_level = computeTopLevel( tn, n[0] );
        success = true;
      }
    }else if( n.isVar() ){
      registerSizeTerm( n, lemmas );
      if( d_register_st[n] ){
        d_term_to_anchor[n] = n;
        d_anchor_to_conj[n] = d_tds->getConjectureForEnumerator(n);
        // this assertion fails if we have a sygus term in the search that is unmeasured
        Assert(d_anchor_to_conj[n] != NULL);
        d = 0;
        is_top_level = true;
        success = true;
      }
    }
    if( success ){
      Trace("sygus-sb-debug") << "Register : " << n << ", depth : " << d << ", top level = " << is_top_level << ", type = " << ((DatatypeType)tn.toType()).getDatatype().getName() << std::endl;
      d_term_to_depth[n] = d;
      d_is_top_level[n] = is_top_level;
      registerSearchTerm( tn, d, n, is_top_level, lemmas );
    }else{
      Trace("sygus-sb-debug2") << "Term " << n << " is not part of sygus search." << std::endl;
    }
  }
}

bool SygusSymBreakNew::computeTopLevel( TypeNode tn, Node n ){
  if( n.getType()==tn ){
    return false;
  }else if( n.getKind()==kind::APPLY_SELECTOR_TOTAL ){
    return computeTopLevel( tn, n[0] );
  }else{
    return true;
  }
}

void SygusSymBreakNew::assertTesterInternal( int tindex, TNode n, Node exp, std::vector< Node >& lemmas ) {
  TypeNode ntn = n.getType();
  if (!ntn.isDatatype())
  {
    // nothing to do for non-datatype types
    return;
  }
  const Datatype& dt = static_cast<DatatypeType>(ntn.toType()).getDatatype();
  if (!dt.isSygus())
  {
    // nothing to do for non-sygus-datatype type
    return;
  }
  d_active_terms.insert(n);
  Trace("sygus-sb-debug2") << "Sygus : activate term : " << n << " : " << exp
                           << std::endl;

  // get the search size for this
  Assert( d_term_to_anchor.find( n )!=d_term_to_anchor.end() );
  Node a = d_term_to_anchor[n];
  Assert( d_anchor_to_measure_term.find( a )!=d_anchor_to_measure_term.end() );
  Node m = d_anchor_to_measure_term[a];
  std::map<Node, std::unique_ptr<SygusSizeDecisionStrategy>>::iterator itsz =
      d_szinfo.find(m);
  Assert( itsz!=d_szinfo.end() );
  unsigned ssz = itsz->second->d_curr_search_size;
  
  if( options::sygusFair()==SYGUS_FAIR_DIRECT ){
    if( dt[tindex].getNumArgs()>0 ){
      quantifiers::SygusTypeInfo& nti = d_tds->getTypeInfo(ntn);
      // consider lower bounds for size of types
      unsigned lb_add = nti.getMinConsTermSize(tindex);
      unsigned lb_rem = n == a ? 0 : nti.getMinTermSize();
      Assert( lb_add>=lb_rem );
      d_currTermSize[a].set( d_currTermSize[a].get() + ( lb_add - lb_rem ) );
    }
    if( (unsigned)d_currTermSize[a].get()>ssz ){
      if( Trace.isOn("sygus-sb-fair") ){
        std::map< TypeNode, int > var_count;
        Node templ = getCurrentTemplate( a, var_count );
        Trace("sygus-sb-fair") << "FAIRNESS : we have " <<  d_currTermSize[a].get() << " at search size " << ssz << ", template is " << templ << std::endl;
      }
      // conflict
      std::vector< Node > conflict;
      for( NodeSet::const_iterator its = d_active_terms.begin(); its != d_active_terms.end(); ++its ){
        Node x = *its;
        Node xa = d_term_to_anchor[x];
        if( xa==a ){
          IntMap::const_iterator ittv = d_testers.find( x );
          Assert( ittv != d_testers.end() );
          int tindex = (*ittv).second;
          const Datatype& dti = ((DatatypeType)x.getType().toType()).getDatatype();
          if( dti[tindex].getNumArgs()>0 ){
            NodeMap::const_iterator itt = d_testers_exp.find( x );
            Assert( itt != d_testers_exp.end() );
            conflict.push_back( (*itt).second );
          }
        }
      }
      Assert( conflict.size()==(unsigned)d_currTermSize[a].get() );
      Assert( itsz->second->d_search_size_exp.find( ssz )!=itsz->second->d_search_size_exp.end() );
      conflict.push_back( itsz->second->d_search_size_exp[ssz] );
      Node conf = NodeManager::currentNM()->mkNode( kind::AND, conflict );
      Trace("sygus-sb-fair") << "Conflict is : " << conf << std::endl;
      lemmas.push_back( conf.negate() );
      return;
    }
  }

  // now, add all applicable symmetry breaking lemmas for this term
  Assert( d_term_to_depth.find( n )!=d_term_to_depth.end() );
  unsigned d = d_term_to_depth[n];
  Trace("sygus-sb-fair-debug") << "Tester " << exp << " is for depth " << d << " term in search size " << ssz << std::endl;
  //Assert( d<=ssz );
  if( options::sygusSymBreakLazy() ){
    // dynamic symmetry breaking
    addSymBreakLemmasFor( ntn, n, d, lemmas );
  }

  Trace("sygus-sb-debug") << "Get simple symmetry breaking predicates...\n";
  unsigned max_depth = ssz>=d ? ssz-d : 0;
  unsigned min_depth = d_simple_proc[exp];
  NodeManager* nm = NodeManager::currentNM();
  if( min_depth<=max_depth ){
    TNode x = getFreeVar( ntn );
    std::vector<Node> sb_lemmas;
    // symmetry breaking lemmas requiring predicate elimination
    std::map<Node, bool> sb_elim_pred;
    bool usingSymCons = d_tds->usingSymbolicConsForEnumerator(m);
    bool isVarAgnostic = d_tds->isVariableAgnosticEnumerator(m);
    for (unsigned ds = 0; ds <= max_depth; ds++)
    {
      // static conjecture-independent symmetry breaking
      Trace("sygus-sb-debug") << "  simple symmetry breaking...\n";
      Node ipred = getSimpleSymBreakPred(
          m, ntn, tindex, ds, usingSymCons, isVarAgnostic);
      if (!ipred.isNull())
      {
        sb_lemmas.push_back(ipred);
        if (ds == 0 && isVarAgnostic)
        {
          sb_elim_pred[ipred] = true;
        }
      }
      // static conjecture-dependent symmetry breaking
      Trace("sygus-sb-debug")
          << "  conjecture-dependent symmetry breaking...\n";
      std::map<Node, quantifiers::SynthConjecture*>::iterator itc =
          d_anchor_to_conj.find(a);
      if (itc != d_anchor_to_conj.end())
      {
        quantifiers::SynthConjecture* conj = itc->second;
        Assert(conj != NULL);
        Node dpred = conj->getSymmetryBreakingPredicate(x, a, ntn, tindex, ds);
        if (!dpred.isNull())
        {
          sb_lemmas.push_back(dpred);
        }
      }
    }

    // add the above symmetry breaking predicates to lemmas
    std::unordered_map<TNode, TNode, TNodeHashFunction> cache;
    Node rlv = getRelevancyCondition(n);
    for (const Node& slem : sb_lemmas)
    {
      Node sslem = slem.substitute(x, n, cache);
      // if we require predicate elimination
      if (sb_elim_pred.find(slem) != sb_elim_pred.end())
      {
        Trace("sygus-sb-tp") << "Eliminate traversal predicates: start "
                             << sslem << std::endl;
        sslem = eliminateTraversalPredicates(sslem);
        Trace("sygus-sb-tp") << "Eliminate traversal predicates: finish "
                             << sslem << std::endl;
      }
      if (!rlv.isNull())
      {
        sslem = nm->mkNode(OR, rlv, sslem);
      }
      lemmas.push_back(sslem);
    }
  }
  d_simple_proc[exp] = max_depth + 1;

  // now activate the children those testers were previously asserted in this
  // context and are awaiting activation, if they exist.
  if( options::sygusSymBreakLazy() ){
    Trace("sygus-sb-debug") << "Do lazy symmetry breaking...\n";
    for( unsigned j=0; j<dt[tindex].getNumArgs(); j++ ){
      Node sel = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[tindex].getSelectorInternal( ntn.toType(), j ) ), n );
      Trace("sygus-sb-debug2") << "  activate child sel : " << sel << std::endl;
      Assert( d_active_terms.find( sel )==d_active_terms.end() );
      IntMap::const_iterator itt = d_testers.find( sel );
      if( itt != d_testers.end() ){
        Assert( d_testers_exp.find( sel ) != d_testers_exp.end() );
        assertTesterInternal( (*itt).second, sel, d_testers_exp[sel], lemmas );
      }
    }
    Trace("sygus-sb-debug") << "...finished" << std::endl;
  }
}

Node SygusSymBreakNew::getRelevancyCondition( Node n ) {
  std::map< Node, Node >::iterator itr = d_rlv_cond.find( n );
  if( itr==d_rlv_cond.end() ){
    Node cond;
    if( n.getKind()==APPLY_SELECTOR_TOTAL && options::sygusSymBreakRlv() ){
      TypeNode ntn = n[0].getType();
      Type nt = ntn.toType();
      const Datatype& dt = ((DatatypeType)nt).getDatatype();
      Expr selExpr = n.getOperator().toExpr();
      if( options::dtSharedSelectors() ){
        std::vector< Node > disj;
        bool excl = false;
        for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
          int sindexi = dt[i].getSelectorIndexInternal(selExpr);
          if (sindexi != -1)
          {
            disj.push_back(DatatypesRewriter::mkTester(n[0], i, dt).negate());
          }
          else
          {
            excl = true;
          }
        }
        Assert( !disj.empty() );
        if( excl ){
          cond = disj.size() == 1 ? disj[0] : NodeManager::currentNM()->mkNode(
                                                  kind::AND, disj);
        }
      }else{
        int sindex = Datatype::cindexOf( selExpr );
        Assert( sindex!=-1 );
        cond = DatatypesRewriter::mkTester(n[0], sindex, dt).negate();
      }
      Node c1 = getRelevancyCondition( n[0] );
      if( cond.isNull() ){
        cond = c1;
      }else if( !c1.isNull() ){
        cond = NodeManager::currentNM()->mkNode(kind::OR, cond, c1);
      }
    }
    Trace("sygus-sb-debug2") << "Relevancy condition for " << n << " is " << cond << std::endl;
    d_rlv_cond[n] = cond;
    return cond;
  }else{
    return itr->second;
  }
}

Node SygusSymBreakNew::getTraversalPredicate(TypeNode tn, Node n, bool isPre)
{
  unsigned index = isPre ? 0 : 1;
  std::map<Node, Node>::iterator itt = d_traversal_pred[index][tn].find(n);
  if (itt != d_traversal_pred[index][tn].end())
  {
    return itt->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  std::vector<TypeNode> types;
  types.push_back(tn);
  TypeNode ptn = nm->mkPredicateType(types);
  Node pred = nm->mkSkolem(isPre ? "pre" : "post", ptn);
  d_traversal_pred[index][tn][n] = pred;
  return pred;
}

Node SygusSymBreakNew::eliminateTraversalPredicates(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::map<Node, Node>::iterator ittb;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      if (cur.getKind() == APPLY_UF)
      {
        Assert(cur.getType().isBoolean());
        Assert(cur.getNumChildren() == 1
               && (cur[0].isVar() || cur[0].getKind() == APPLY_SELECTOR_TOTAL));
        ittb = d_traversal_bool.find(cur);
        Node ret;
        if (ittb == d_traversal_bool.end())
        {
          std::stringstream ss;
          ss << "v_" << cur;
          ret = nm->mkSkolem(ss.str(), cur.getType());
          d_traversal_bool[cur] = ret;
        }
        else
        {
          ret = ittb->second;
        }
        visited[cur] = ret;
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node SygusSymBreakNew::getSimpleSymBreakPred(Node e,
                                             TypeNode tn,
                                             int tindex,
                                             unsigned depth,
                                             bool usingSymCons,
                                             bool isVarAgnostic)
{
  // Compute the tuple of expressions we hash the predicate for.

  // The hash value in d_simple_sb_pred for the given options
  unsigned optHashVal = usingSymCons ? 1 : 0;
  if (isVarAgnostic && depth == 0)
  {
    // variable agnostic symmetry breaking only applies at depth 0
    optHashVal = optHashVal + 2;
  }
  else
  {
    // enumerator is only specific to variable agnostic symmetry breaking
    e = Node::null();
  }
  std::map<unsigned, Node>& ssbCache =
      d_simple_sb_pred[e][tn][tindex][optHashVal];
  std::map<unsigned, Node>::iterator it = ssbCache.find(depth);
  if (it != ssbCache.end())
  {
    return it->second;
  }
  // this function is only called on sygus datatype types
  Assert(tn.isDatatype());
  NodeManager* nm = NodeManager::currentNM();
  Node n = getFreeVar(tn);
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  Assert(dt.isSygus());
  Assert(tindex >= 0 && tindex < static_cast<int>(dt.getNumConstructors()));

  Trace("sygus-sb-simple-debug")
      << "Simple symmetry breaking for " << dt.getName() << ", constructor "
      << dt[tindex].getName() << ", at depth " << depth << std::endl;

  quantifiers::SygusTypeInfo& ti = d_tds->getTypeInfo(tn);
  // get the sygus operator
  Node sop = Node::fromExpr(dt[tindex].getSygusOp());
  // get the kind of the constructor operator
  Kind nk = ti.getConsNumKind(tindex);
  // is this the any-constant constructor?
  bool isAnyConstant = sop.getAttribute(SygusAnyConstAttribute());

  // conjunctive conclusion of lemma
  std::vector<Node> sbp_conj;

  // the number of (sygus) arguments
  // Notice if this is an any-constant constructor, its child is not a
  // sygus child, hence we set to 0 here.
  unsigned dt_index_nargs = isAnyConstant ? 0 : dt[tindex].getNumArgs();

  // builtin type
  TypeNode tnb = TypeNode::fromType(dt.getSygusType());
  // get children
  std::vector<Node> children;
  for (unsigned j = 0; j < dt_index_nargs; j++)
  {
    Node sel = nm->mkNode(
        APPLY_SELECTOR_TOTAL,
        Node::fromExpr(dt[tindex].getSelectorInternal(tn.toType(), j)),
        n);
    Assert(sel.getType().isDatatype());
    children.push_back(sel);
  }

  if (depth == 0)
  {
    Trace("sygus-sb-simple-debug") << "  Size..." << std::endl;
    // fairness
    if (options::sygusFair() == SYGUS_FAIR_DT_SIZE && !isAnyConstant)
    {
      Node szl = nm->mkNode(DT_SIZE, n);
      Node szr =
          nm->mkNode(DT_SIZE, DatatypesRewriter::getInstCons(n, dt, tindex));
      szr = Rewriter::rewrite(szr);
      sbp_conj.push_back(szl.eqNode(szr));
    }
    if (isVarAgnostic)
    {
      // Enforce symmetry breaking lemma template for each x_i:
      // template z.
      //   is-x_i( z ) => pre_{x_{i-1}}( z )
      //   for args a = 1...n
      //      // pre-definition
      //      pre_{x_i}( z.a ) = a=0 ? pre_{x_i}( z ) : post_{x_i}( z.{a-1} )
      //   post_{x_i}( z ) = post_{x_i}( z.n ) OR is-x_i( z )

      // Notice that we are constructing a symmetry breaking template
      // under the condition that is-C( z ) holds in this method, where C
      // is the tindex^{th} constructor of dt. Thus, is-x_i( z ) is either
      // true or false below.

      Node svl = Node::fromExpr(dt.getSygusVarList());
      // for each variable
      Assert(!e.isNull());
      TypeNode etn = e.getType();
      // for each variable in the sygus type
      for (const Node& var : svl)
      {
        quantifiers::SygusTypeInfo& eti = d_tds->getTypeInfo(etn);
        unsigned sc = eti.getSubclassForVar(var);
        if (eti.getNumSubclassVars(sc) == 1)
        {
          // unique variable in singleton subclass, skip
          continue;
        }
        // Compute the "predecessor" variable in the subclass of var.
        Node predVar;
        unsigned scindex = 0;
        if (eti.getIndexInSubclassForVar(var, scindex))
        {
          if (scindex > 0)
          {
            predVar = eti.getVarSubclassIndex(sc, scindex - 1);
          }
        }
        Node preParentOp = getTraversalPredicate(tn, var, true);
        Node preParent = nm->mkNode(APPLY_UF, preParentOp, n);
        Node prev = preParent;
        // for each child
        for (const Node& child : children)
        {
          TypeNode ctn = child.getType();
          // my pre is equal to the previous
          Node preCurrOp = getTraversalPredicate(ctn, var, true);
          Node preCurr = nm->mkNode(APPLY_UF, preCurrOp, child);
          // definition of pre, for each argument
          sbp_conj.push_back(preCurr.eqNode(prev));
          Node postCurrOp = getTraversalPredicate(ctn, var, false);
          prev = nm->mkNode(APPLY_UF, postCurrOp, child);
        }
        Node postParent = getTraversalPredicate(tn, var, false);
        Node finish = nm->mkNode(APPLY_UF, postParent, n);
        // check if we are constructing the symmetry breaking predicate for the
        // variable in question. If so, is-{x_i}( z ) is true.
        int varCn = ti.getOpConsNum(var);
        if (varCn == static_cast<int>(tindex))
        {
          // the post value is true
          prev = d_true;
          // requirement : If I am the variable, I must have seen
          // the variable before this one in its type class.
          if (!predVar.isNull())
          {
            Node preParentPredVarOp = getTraversalPredicate(tn, predVar, true);
            Node preParentPredVar = nm->mkNode(APPLY_UF, preParentPredVarOp, n);
            sbp_conj.push_back(preParentPredVar);
          }
        }
        // definition of post
        sbp_conj.push_back(finish.eqNode(prev));
      }
    }
  }

  // if we are the "any constant" constructor, we do no symmetry breaking
  // only do simple symmetry breaking up to depth 2
  bool doSymBreak = options::sygusSymBreak();
  if (isAnyConstant || depth > 2)
  {
    doSymBreak = false;
  }
  // symmetry breaking
  if (doSymBreak)
  {
    // direct solving for children
    //   for instance, we may want to insist that the LHS of MINUS is 0
    Trace("sygus-sb-simple-debug") << "  Solve children..." << std::endl;
    std::map<unsigned, unsigned> children_solved;
    for (unsigned j = 0; j < dt_index_nargs; j++)
    {
      int i = d_ssb.solveForArgument(tn, tindex, j);
      if (i >= 0)
      {
        children_solved[j] = i;
        TypeNode ctn = children[j].getType();
        const Datatype& cdt =
            static_cast<DatatypeType>(ctn.toType()).getDatatype();
        Assert(i < static_cast<int>(cdt.getNumConstructors()));
        sbp_conj.push_back(DatatypesRewriter::mkTester(children[j], i, cdt));
      }
    }

    // depth 1 symmetry breaking : talks about direct children
    if (depth == 1)
    {
      if (nk != UNDEFINED_KIND)
      {
        Trace("sygus-sb-simple-debug")
            << "  Equality reasoning about children..." << std::endl;
        // commutative operators
        if (quantifiers::TermUtil::isComm(nk))
        {
          if (children.size() == 2
              && children[0].getType() == children[1].getType())
          {
            Node order_pred = getTermOrderPredicate(children[0], children[1]);
            sbp_conj.push_back(order_pred);
          }
        }
        // operators whose arguments are non-additive (e.g. should be different)
        std::vector<unsigned> deq_child[2];
        if (children.size() == 2 && children[0].getType() == tn)
        {
          bool argDeq = false;
          if (quantifiers::TermUtil::isNonAdditive(nk))
          {
            argDeq = true;
          }
          else
          {
            // other cases of rewriting x k x -> x'
            Node req_const;
            if (nk == GT || nk == LT || nk == XOR || nk == MINUS
                || nk == BITVECTOR_SUB || nk == BITVECTOR_XOR
                || nk == BITVECTOR_UREM_TOTAL)
            {
              // must have the zero element
              req_const = quantifiers::TermUtil::mkTypeValue(tnb, 0);
            }
            else if (nk == EQUAL || nk == LEQ || nk == GEQ
                     || nk == BITVECTOR_XNOR)
            {
              req_const = quantifiers::TermUtil::mkTypeMaxValue(tnb);
            }
            // cannot do division since we have to consider when both are zero
            if (!req_const.isNull())
            {
              if (ti.hasConst(req_const))
              {
                argDeq = true;
              }
            }
          }
          if (argDeq)
          {
            deq_child[0].push_back(0);
            deq_child[1].push_back(1);
          }
        }
        if (nk == ITE || nk == STRING_STRREPL || nk == STRING_STRREPLALL)
        {
          deq_child[0].push_back(1);
          deq_child[1].push_back(2);
        }
        if (nk == STRING_STRREPL || nk == STRING_STRREPLALL)
        {
          deq_child[0].push_back(0);
          deq_child[1].push_back(1);
        }
        // this code adds simple symmetry breaking predicates of the form
        // d.i != d.j, for example if we are considering an ITE constructor,
        // we enforce that d.1 != d.2 since otherwise the ITE can be
        // simplified.
        for (unsigned i = 0, size = deq_child[0].size(); i < size; i++)
        {
          unsigned c1 = deq_child[0][i];
          unsigned c2 = deq_child[1][i];
          TypeNode tnc = children[c1].getType();
          // we may only apply this symmetry breaking scheme (which introduces
          // disequalities) if the types are infinite.
          if (tnc == children[c2].getType() && !tnc.isInterpretedFinite())
          {
            Node sym_lem_deq = children[c1].eqNode(children[c2]).negate();
            // notice that this symmetry breaking still allows for
            //   ite( C, any_constant(x), any_constant(y) )
            // since any_constant takes a builtin argument.
            sbp_conj.push_back(sym_lem_deq);
          }
        }

        Trace("sygus-sb-simple-debug") << "  Redundant operators..."
                                       << std::endl;
        // singular arguments (e.g. 0 for mult)
        // redundant arguments (e.g. 0 for plus, 1 for mult)
        // right-associativity
        // simple rewrites
        // explanation of why not all children of this are constant
        std::vector<Node> exp_not_all_const;
        // is the above explanation valid? This is set to false if
        // one child does not have a constant, hence making the explanation
        // false.
        bool exp_not_all_const_valid = dt_index_nargs > 0;
        // does the parent have an any constant constructor?
        bool usingAnyConstCons =
            usingSymCons && (ti.getAnyConstantConsNum() != -1);
        for (unsigned j = 0; j < dt_index_nargs; j++)
        {
          Node nc = children[j];
          // if not already solved
          if (children_solved.find(j) != children_solved.end())
          {
            continue;
          }
          TypeNode tnc = nc.getType();
          quantifiers::SygusTypeInfo& cti = d_tds->getTypeInfo(tnc);
          int anyc_cons_num = cti.getAnyConstantConsNum();
          const Datatype& cdt =
              static_cast<DatatypeType>(tnc.toType()).getDatatype();
          std::vector<Node> exp_const;
          for (unsigned k = 0, ncons = cdt.getNumConstructors(); k < ncons; k++)
          {
            Kind nck = cti.getConsNumKind(k);
            bool red = false;
            Node tester = DatatypesRewriter::mkTester(nc, k, cdt);
            // check if the argument is redundant
            if (static_cast<int>(k) == anyc_cons_num)
            {
              exp_const.push_back(tester);
            }
            else if (nck != UNDEFINED_KIND)
            {
              Trace("sygus-sb-simple-debug") << "  argument " << j << " " << k
                                             << " is : " << nck << std::endl;
              red = !d_ssb.considerArgKind(tnc, tn, nck, nk, j);
            }
            else
            {
              Node cc = cti.getConsNumConst(k);
              if (!cc.isNull())
              {
                Trace("sygus-sb-simple-debug")
                    << "  argument " << j << " " << k << " is constant : " << cc
                    << std::endl;
                red = !d_ssb.considerConst(tnc, tn, cc, nk, j);
                if (usingAnyConstCons)
                {
                  // we only consider concrete constant constructors
                  // of children if we have the "any constant" constructor
                  // otherwise, we would disallow solutions for grammars
                  // like the following:
                  //   A -> B+B
                  //   B -> 4 | 8 | 100
                  // where A allows all constants but is not using the
                  // any constant constructor.
                  exp_const.push_back(tester);
                }
              }
              else
              {
                // defined function?
              }
            }
            if (red)
            {
              Trace("sygus-sb-simple-debug") << "  ...redundant." << std::endl;
              sbp_conj.push_back(tester.negate());
            }
          }
          if (exp_const.empty())
          {
            exp_not_all_const_valid = false;
          }
          else
          {
            Node ecn = exp_const.size() == 1 ? exp_const[0]
                                             : nm->mkNode(OR, exp_const);
            exp_not_all_const.push_back(ecn.negate());
          }
        }
        // explicitly handle constants and "any constant" constructors
        // if this type admits any constant, then at least one of my
        // children must not be a constant or the "any constant" constructor
        if (dt.getSygusAllowConst() && exp_not_all_const_valid)
        {
          Assert(!exp_not_all_const.empty());
          Node expaan = exp_not_all_const.size() == 1
                            ? exp_not_all_const[0]
                            : nm->mkNode(OR, exp_not_all_const);
          Trace("sygus-sb-simple-debug")
              << "Ensure not all constant: " << expaan << std::endl;
          sbp_conj.push_back(expaan);
        }
      }
      else
      {
        // defined function?
      }
    }
    else if (depth == 2)
    {
      // commutative operators
      if (quantifiers::TermUtil::isComm(nk) && children.size() == 2
          && children[0].getType() == tn && children[1].getType() == tn)
      {
        // chainable
        Node child11 = nm->mkNode(
            APPLY_SELECTOR_TOTAL,
            Node::fromExpr(dt[tindex].getSelectorInternal(tn.toType(), 1)),
            children[0]);
        Assert(child11.getType() == children[1].getType());
        Node order_pred_trans = nm->mkNode(
            OR,
            DatatypesRewriter::mkTester(children[0], tindex, dt).negate(),
            getTermOrderPredicate(child11, children[1]));
        sbp_conj.push_back(order_pred_trans);
      }
    }
  }

  Node sb_pred;
  if (!sbp_conj.empty())
  {
    sb_pred =
        sbp_conj.size() == 1 ? sbp_conj[0] : nm->mkNode(kind::AND, sbp_conj);
    Trace("sygus-sb-simple")
        << "Simple predicate for " << tn << " index " << tindex << " (" << nk
        << ") at depth " << depth << " : " << std::endl;
    Trace("sygus-sb-simple") << "   " << sb_pred << std::endl;
    sb_pred = nm->mkNode(
        kind::OR, DatatypesRewriter::mkTester(n, tindex, dt).negate(), sb_pred);
  }
  d_simple_sb_pred[e][tn][tindex][optHashVal][depth] = sb_pred;
  return sb_pred;
}

TNode SygusSymBreakNew::getFreeVar( TypeNode tn ) {
  return d_tds->getFreeVar(tn, 0);
}

void SygusSymBreakNew::registerSearchTerm( TypeNode tn, unsigned d, Node n, bool topLevel, std::vector< Node >& lemmas ) {
  //register this term
  std::unordered_map<Node, Node, NodeHashFunction>::iterator ita =
      d_term_to_anchor.find(n);
  Assert( ita != d_term_to_anchor.end() );
  Node a = ita->second;
  Assert( !a.isNull() );
  if( std::find( d_cache[a].d_search_terms[tn][d].begin(), d_cache[a].d_search_terms[tn][d].end(), n )==d_cache[a].d_search_terms[tn][d].end() ){
    Trace("sygus-sb-debug") << "  register search term : " << n << " at depth " << d << ", type=" << tn << ", tl=" << topLevel << std::endl;
    d_cache[a].d_search_terms[tn][d].push_back( n );
    if( !options::sygusSymBreakLazy() ){
      addSymBreakLemmasFor( tn, n, d, lemmas );
    }
  }
}

Node SygusSymBreakNew::registerSearchValue(Node a,
                                           Node n,
                                           Node nv,
                                           unsigned d,
                                           std::vector<Node>& lemmas,
                                           bool isVarAgnostic,
                                           bool doSym)
{
  Assert(n.getType().isComparableTo(nv.getType()));
  TypeNode tn = n.getType();
  if (!tn.isDatatype())
  {
    // don't register non-datatype terms, instead we return the
    // selector chain n.
    return n;
  }
  const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
  if (!dt.isSygus())
  {
    // don't register non-sygus-datatype terms
    return n;
  }
  Assert(nv.getKind() == APPLY_CONSTRUCTOR);
  NodeManager* nm = NodeManager::currentNM();
  // we call the body of this function in a bottom-up fashion
  // this ensures that the "abstraction" of the model value is available
  if( nv.getNumChildren()>0 ){
    unsigned cindex = DatatypesRewriter::indexOf(nv.getOperator());
    std::vector<Node> rcons_children;
    rcons_children.push_back(nv.getOperator());
    bool childrenChanged = false;
    for (unsigned i = 0, nchild = nv.getNumChildren(); i < nchild; i++)
    {
      Node sel = nm->mkNode(
          APPLY_SELECTOR_TOTAL,
          Node::fromExpr(dt[cindex].getSelectorInternal(tn.toType(), i)),
          n);
      Node nvc = registerSearchValue(a,
                                     sel,
                                     nv[i],
                                     d + 1,
                                     lemmas,
                                     isVarAgnostic,
                                     doSym && (!isVarAgnostic || i == 0));
      if (nvc.isNull())
      {
        return Node::null();
      }
      rcons_children.push_back(nvc);
      childrenChanged = childrenChanged || nvc != nv[i];
    }
    // reconstruct the value, which may be a skeleton
    if (childrenChanged)
    {
      nv = nm->mkNode(APPLY_CONSTRUCTOR, rcons_children);
    }
  }
  if (!doSym)
  {
    return nv;
  }
  Trace("sygus-sb-debug2") << "Registering search value " << n << " -> " << nv << std::endl;
  std::map<TypeNode, int> var_count;
  Node cnv = d_tds->canonizeBuiltin(nv, var_count);
  Trace("sygus-sb-debug") << "  ...canonized value is " << cnv << std::endl;
  // must do this for all nodes, regardless of top-level
  if (d_cache[a].d_search_val_proc.find(cnv)
      == d_cache[a].d_search_val_proc.end())
  {
    d_cache[a].d_search_val_proc.insert(cnv);
    // get the root (for PBE symmetry breaking)
    Assert(d_anchor_to_conj.find(a) != d_anchor_to_conj.end());
    quantifiers::SynthConjecture* aconj = d_anchor_to_conj[a];
    Assert(aconj != NULL);
    Trace("sygus-sb-debug") << "  ...register search value " << cnv
                            << ", type=" << tn << std::endl;
    Node bv = d_tds->sygusToBuiltin(cnv, tn);
    Trace("sygus-sb-debug") << "  ......builtin is " << bv << std::endl;
    Node bvr = d_tds->getExtRewriter()->extendedRewrite(bv);
    Trace("sygus-sb-debug") << "  ......search value rewrites to " << bvr << std::endl;
    Trace("dt-sygus") << "  * DT builtin : " << n << " -> " << bvr << std::endl;
    unsigned sz = d_tds->getSygusTermSize( nv );      
    if( d_tds->involvesDivByZero( bvr ) ){
      quantifiers::DivByZeroSygusInvarianceTest dbzet;
      Trace("sygus-sb-mexp-debug") << "Minimize explanation for div-by-zero in "
                                   << bv << std::endl;
      registerSymBreakLemmaForValue(
          a, nv, dbzet, Node::null(), var_count, lemmas);
      return Node::null();
    }else{
      std::unordered_map<Node, Node, NodeHashFunction>::iterator itsv =
          d_cache[a].d_search_val[tn].find(bvr);
      Node bad_val_bvr;
      bool by_examples = false;
      if( itsv==d_cache[a].d_search_val[tn].end() ){
        // TODO (github #1210) conjecture-specific symmetry breaking
        // this should be generalized and encapsulated within the
        // SynthConjecture class.
        // Is it equivalent under examples?
        Node bvr_equiv;
        if (options::sygusSymBreakPbe())
        {
          if (aconj->getPbe()->hasExamples(a))
          {
            bvr_equiv = aconj->getPbe()->addSearchVal(tn, a, bvr);
          }
        }
        if( !bvr_equiv.isNull() ){
          if( bvr_equiv!=bvr ){
            Trace("sygus-sb-debug") << "......adding search val for " << bvr << " returned " << bvr_equiv << std::endl;
            Assert( d_cache[a].d_search_val[tn].find( bvr_equiv )!=d_cache[a].d_search_val[tn].end() );
            Trace("sygus-sb-debug") << "......search value was " << d_cache[a].d_search_val[tn][bvr_equiv] << std::endl;
            if( Trace.isOn("sygus-sb-exc") ){
              Node prev = d_tds->sygusToBuiltin( d_cache[a].d_search_val[tn][bvr_equiv], tn );
              Trace("sygus-sb-exc") << "  ......programs " << prev << " and " << bv << " are equivalent up to examples." << std::endl;
            }
            bad_val_bvr = bvr_equiv;
            by_examples = true;
          }
        }
        //store rewritten values, regardless of whether it will be considered
        d_cache[a].d_search_val[tn][bvr] = nv;
        d_cache[a].d_search_val_sz[tn][bvr] = sz;
      }else{
        bad_val_bvr = bvr;
        if( Trace.isOn("sygus-sb-exc") ){
          Node prev_bv = d_tds->sygusToBuiltin( itsv->second, tn );
          Trace("sygus-sb-exc") << "  ......programs " << prev_bv << " and " << bv << " rewrite to " << bvr << "." << std::endl;
        } 
      }

      if (options::sygusRewVerify())
      {
        if (bv != bvr)
        {
          // add to the sampler database object
          std::map<TypeNode, quantifiers::SygusSampler>::iterator its =
              d_sampler[a].find(tn);
          if (its == d_sampler[a].end())
          {
            d_sampler[a][tn].initializeSygus(
                d_tds, nv, options::sygusSamples(), false);
            its = d_sampler[a].find(tn);
          }
          // check equivalent
          its->second.checkEquivalent(bv, bvr);
        }
      }

      if( !bad_val_bvr.isNull() ){
        Node bad_val = nv;
        Node bad_val_o = d_cache[a].d_search_val[tn][bad_val_bvr];
        Assert( d_cache[a].d_search_val_sz[tn].find( bad_val_bvr )!=d_cache[a].d_search_val_sz[tn].end() );
        unsigned prev_sz = d_cache[a].d_search_val_sz[tn][bad_val_bvr];
        bool doFlip = (prev_sz > sz);
        if (doFlip)
        {
          //swap : the excluded value is the previous
          d_cache[a].d_search_val_sz[tn][bad_val_bvr] = sz;
          bad_val = d_cache[a].d_search_val[tn][bad_val_bvr];
          bad_val_o = nv;
          if (Trace.isOn("sygus-sb-exc"))
          {
            Trace("sygus-sb-exc") << "Flip : exclude ";
            quantifiers::TermDbSygus::toStreamSygus("sygus-sb-exc", bad_val);
            Trace("sygus-sb-exc") << " instead of ";
            quantifiers::TermDbSygus::toStreamSygus("sygus-sb-exc", bad_val_o);
            Trace("sygus-sb-exc") << ", since its size is " << sz << " < "
                                  << prev_sz << std::endl;
          }
          sz = prev_sz;
        }
        if( Trace.isOn("sygus-sb-exc") ){
          Node bad_val_bv = d_tds->sygusToBuiltin( bad_val, tn );
          Trace("sygus-sb-exc") << "  ........exclude : " << bad_val_bv;
          if( by_examples ){
            Trace("sygus-sb-exc") << " (by examples)";
          }
          Trace("sygus-sb-exc") << std::endl;
        } 
        Assert( d_tds->getSygusTermSize( bad_val )==sz );

        // generalize the explanation for why the analog of bad_val
        // is equivalent to bvr
        quantifiers::EquivSygusInvarianceTest eset;
        eset.init(d_tds, tn, aconj, a, bvr);

        Trace("sygus-sb-mexp-debug") << "Minimize explanation for eval[" << d_tds->sygusToBuiltin( bad_val ) << "] = " << bvr << std::endl;
        registerSymBreakLemmaForValue(
            a, bad_val, eset, bad_val_o, var_count, lemmas);

        // other generalization criteria go here

        // If the exclusion was flipped, we are excluding a previous value
        // instead of the current one. Hence, the current value is a legal
        // value that we will consider.
        if (!doFlip)
        {
          return Node::null();
        }
      }
    }
  }
  return nv;
}

void SygusSymBreakNew::registerSymBreakLemmaForValue(
    Node a,
    Node val,
    quantifiers::SygusInvarianceTest& et,
    Node valr,
    std::map<TypeNode, int>& var_count,
    std::vector<Node>& lemmas)
{
  TypeNode tn = val.getType();
  Node x = getFreeVar(tn);
  unsigned sz = d_tds->getSygusTermSize(val);
  std::vector<Node> exp;
  d_tds->getExplain()->getExplanationFor(x, val, exp, et, valr, var_count, sz);
  Node lem =
      exp.size() == 1 ? exp[0] : NodeManager::currentNM()->mkNode(AND, exp);
  lem = lem.negate();
  Trace("sygus-sb-exc") << "  ........exc lemma is " << lem << ", size = " << sz
                        << std::endl;
  registerSymBreakLemma(tn, lem, sz, a, lemmas);
}

void SygusSymBreakNew::registerSymBreakLemma( TypeNode tn, Node lem, unsigned sz, Node a, std::vector< Node >& lemmas ) {
  // lem holds for all terms of type tn, and is applicable to terms of size sz
  Trace("sygus-sb-debug") << "  register sym break lemma : " << lem
                          << std::endl;
  Trace("sygus-sb-debug") << "     anchor : " << a << std::endl;
  Trace("sygus-sb-debug") << "     type : " << tn << std::endl;
  Trace("sygus-sb-debug") << "     size : " << sz << std::endl;
  Assert( !a.isNull() );
  d_cache[a].d_sb_lemmas[tn][sz].push_back( lem );
  TNode x = getFreeVar( tn );
  unsigned csz = getSearchSizeForAnchor( a );
  int max_depth = ((int)csz)-((int)sz);
  NodeManager* nm = NodeManager::currentNM();
  for( int d=0; d<=max_depth; d++ ){
    std::map< unsigned, std::vector< Node > >::iterator itt = d_cache[a].d_search_terms[tn].find( d );
    if( itt!=d_cache[a].d_search_terms[tn].end() ){
      for (const TNode& t : itt->second)
      {
        if (!options::sygusSymBreakLazy()
            || d_active_terms.find(t) != d_active_terms.end())
        {
          Node slem = lem.substitute(x, t);
          Node rlv = getRelevancyCondition(t);
          if (!rlv.isNull())
          {
            slem = nm->mkNode(OR, rlv, slem);
          }
          lemmas.push_back(slem);
        }
      }
    }
  }
}
void SygusSymBreakNew::addSymBreakLemmasFor( TypeNode tn, Node t, unsigned d, std::vector< Node >& lemmas ) {
  Assert( d_term_to_anchor.find( t )!=d_term_to_anchor.end() );
  Node a = d_term_to_anchor[t];
  addSymBreakLemmasFor( tn, t, d, a, lemmas );
}

void SygusSymBreakNew::addSymBreakLemmasFor( TypeNode tn, Node t, unsigned d, Node a, std::vector< Node >& lemmas ) {
  Assert( t.getType()==tn );
  Assert( !a.isNull() );
  Trace("sygus-sb-debug2") << "add sym break lemmas for " << t << " " << d
                           << " " << a << std::endl;
  std::map< TypeNode, std::map< unsigned, std::vector< Node > > >::iterator its = d_cache[a].d_sb_lemmas.find( tn );
  Node rlv = getRelevancyCondition(t);
  NodeManager* nm = NodeManager::currentNM();
  if( its != d_cache[a].d_sb_lemmas.end() ){
    TNode x = getFreeVar( tn );
    //get symmetry breaking lemmas for this term 
    unsigned csz = getSearchSizeForAnchor( a );
    int max_sz = ((int)csz) - ((int)d);
    Trace("sygus-sb-debug2")
        << "add lemmas up to size " << max_sz << ", which is (search_size) "
        << csz << " - (depth) " << d << std::endl;
    std::unordered_map<TNode, TNode, TNodeHashFunction> cache;
    for( std::map< unsigned, std::vector< Node > >::iterator it = its->second.begin(); it != its->second.end(); ++it ){
      if( (int)it->first<=max_sz ){
        for (const Node& lem : it->second)
        {
          Node slem = lem.substitute(x, t, cache);
          // add the relevancy condition for t
          if (!rlv.isNull())
          {
            slem = nm->mkNode(OR, rlv, slem);
          }
          lemmas.push_back(slem);
        }
      }
    }
  }
  Trace("sygus-sb-debug2") << "...finished." << std::endl;
}

void SygusSymBreakNew::preRegisterTerm( TNode n, std::vector< Node >& lemmas  ) {
  if( n.isVar() ){
    Trace("sygus-sb-debug") << "Pre-register variable : " << n << std::endl;
    registerSizeTerm( n, lemmas );
  }
}

void SygusSymBreakNew::registerSizeTerm(Node e, std::vector<Node>& lemmas)
{
  if (d_register_st.find(e) != d_register_st.end())
  {
    // already registered
    return;
  }
  TypeNode etn = e.getType();
  if (!etn.isDatatype())
  {
    // not a datatype term
    d_register_st[e] = false;
    return;
  }
  const Datatype& dt = etn.getDatatype();
  if (!dt.isSygus())
  {
    // not a sygus datatype term
    d_register_st[e] = false;
    return;
  }
  if (!d_tds->isEnumerator(e))
  {
    // not sure if it is a size term or not (may be registered later?)
    return;
  }
  d_register_st[e] = true;
  Node ag = d_tds->getActiveGuardForEnumerator(e);
  if (!ag.isNull())
  {
    d_anchor_to_active_guard[e] = ag;
    std::map<Node, std::unique_ptr<DecisionStrategy>>::iterator itaas =
        d_anchor_to_ag_strategy.find(e);
    if (itaas == d_anchor_to_ag_strategy.end())
    {
      d_anchor_to_ag_strategy[e].reset(
          new DecisionStrategySingleton("sygus_enum_active",
                                        ag,
                                        d_td->getSatContext(),
                                        d_td->getValuation()));
    }
    d_td->getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_DT_SYGUS_ENUM_ACTIVE,
        d_anchor_to_ag_strategy[e].get());
  }
  Node m;
  if (!ag.isNull())
  {
    // if it has an active guard (it is an enumerator), use itself as measure
    // term. This will enforce fairness on it independently.
    m = e;
  }
  else
  {
    // otherwise we enforce fairness in a unified way for all
    if (d_generic_measure_term.isNull())
    {
      // choose e as master for all future terms
      d_generic_measure_term = e;
    }
    m = d_generic_measure_term;
  }
  Trace("sygus-sb") << "Sygus : register size term : " << e << " with measure "
                    << m << std::endl;
  registerMeasureTerm(m);
  d_szinfo[m]->d_anchors.push_back(e);
  d_anchor_to_measure_term[e] = m;
  NodeManager* nm = NodeManager::currentNM();
  if (options::sygusFair() == SYGUS_FAIR_DT_SIZE)
  {
    // update constraints on the measure term
    Node slem;
    if (options::sygusFairMax())
    {
      Node ds = nm->mkNode(DT_SIZE, e);
      slem = nm->mkNode(LEQ, ds, d_szinfo[m]->getOrMkMeasureValue(lemmas));
    }else{
      Node mt = d_szinfo[m]->getOrMkActiveMeasureValue(lemmas);
      Node new_mt = d_szinfo[m]->getOrMkActiveMeasureValue(lemmas, true);
      Node ds = nm->mkNode(DT_SIZE, e);
      slem = mt.eqNode(nm->mkNode(PLUS, new_mt, ds));
    }
    Trace("sygus-sb") << "...size lemma : " << slem << std::endl;
    lemmas.push_back(slem);
  }
  if (d_tds->isVariableAgnosticEnumerator(e))
  {
    // if it is variable agnostic, enforce top-level constraint that says no
    // variables occur pre-traversal at top-level
    Node varList = Node::fromExpr(dt.getSygusVarList());
    std::vector<Node> constraints;
    quantifiers::SygusTypeInfo& eti = d_tds->getTypeInfo(etn);
    for (const Node& v : varList)
    {
      unsigned sc = eti.getSubclassForVar(v);
      // no symmetry breaking occurs for variables in singleton subclasses
      if (eti.getNumSubclassVars(sc) > 1)
      {
        Node preRootOp = getTraversalPredicate(etn, v, true);
        Node preRoot = nm->mkNode(APPLY_UF, preRootOp, e);
        constraints.push_back(preRoot.negate());
      }
    }
    if (!constraints.empty())
    {
      Node preNoVar = constraints.size() == 1 ? constraints[0]
                                              : nm->mkNode(AND, constraints);
      Node preNoVarProc = eliminateTraversalPredicates(preNoVar);
      Trace("sygus-sb") << "...variable order : " << preNoVarProc << std::endl;
      Trace("sygus-sb-tp") << "...variable order : " << preNoVarProc
                           << std::endl;
      lemmas.push_back(preNoVarProc);
    }
  }
}

void SygusSymBreakNew::registerMeasureTerm( Node m ) {
  std::map<Node, std::unique_ptr<SygusSizeDecisionStrategy>>::iterator it =
      d_szinfo.find(m);
  if( it==d_szinfo.end() ){
    Trace("sygus-sb") << "Sygus : register measure term : " << m << std::endl;
    d_szinfo[m].reset(new SygusSizeDecisionStrategy(
        m, d_td->getSatContext(), d_td->getValuation()));
    // register this as a decision strategy
    d_td->getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_DT_SYGUS_ENUM_SIZE, d_szinfo[m].get());
  }
}

void SygusSymBreakNew::notifySearchSize( Node m, unsigned s, Node exp, std::vector< Node >& lemmas ) {
  std::map<Node, std::unique_ptr<SygusSizeDecisionStrategy>>::iterator its =
      d_szinfo.find(m);
  Assert( its!=d_szinfo.end() );
  if( its->second->d_search_size.find( s )==its->second->d_search_size.end() ){
    its->second->d_search_size[s] = true;
    its->second->d_search_size_exp[s] = exp;
    Assert( s==0 || its->second->d_search_size.find( s-1 )!=its->second->d_search_size.end() );
    Trace("sygus-fair") << "SygusSymBreakNew:: now considering term measure : " << s << " for " << m << std::endl;
    Assert( s>=its->second->d_curr_search_size );
    while( s>its->second->d_curr_search_size ){
      incrementCurrentSearchSize( m, lemmas );
    }
    Trace("sygus-fair") << "...finish increment for term measure : " << s << std::endl;
    /*
    //re-add all testers (some may now be relevant) TODO
    for( IntMap::const_iterator it = d_testers.begin(); it != d_testers.end(); ++it ){
      Node n = (*it).first;
      NodeMap::const_iterator itx = d_testers_exp.find( n );
      if( itx!=d_testers_exp.end() ){
        int tindex = (*it).second;
        Node exp = (*itx).second;
        assertTester( tindex, n, exp, lemmas );
      }else{
        Assert( false );
      }
    }
    */
  }
}

unsigned SygusSymBreakNew::getSearchSizeFor( Node n ) {
  Trace("sygus-sb-debug2") << "get search size for term : " << n << std::endl;
  std::unordered_map<Node, Node, NodeHashFunction>::iterator ita =
      d_term_to_anchor.find(n);
  Assert( ita != d_term_to_anchor.end() );
  return getSearchSizeForAnchor( ita->second );
}

unsigned SygusSymBreakNew::getSearchSizeForAnchor( Node a ) {
  Trace("sygus-sb-debug2") << "get search size for anchor : " << a << std::endl;
  std::map< Node, Node >::iterator it = d_anchor_to_measure_term.find( a );
  Assert( it!=d_anchor_to_measure_term.end() );
  return getSearchSizeForMeasureTerm(it->second);
}

unsigned SygusSymBreakNew::getSearchSizeForMeasureTerm(Node m)
{
  Trace("sygus-sb-debug2") << "get search size for measure : " << m << std::endl;
  std::map<Node, std::unique_ptr<SygusSizeDecisionStrategy>>::iterator its =
      d_szinfo.find(m);
  Assert( its!=d_szinfo.end() );
  return its->second->d_curr_search_size;
}
  
void SygusSymBreakNew::incrementCurrentSearchSize( Node m, std::vector< Node >& lemmas ) {
  std::map<Node, std::unique_ptr<SygusSizeDecisionStrategy>>::iterator itsz =
      d_szinfo.find(m);
  Assert( itsz!=d_szinfo.end() );
  itsz->second->d_curr_search_size++;
  Trace("sygus-fair") << "  register search size " << itsz->second->d_curr_search_size << " for " << m << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for( std::map< Node, SearchCache >::iterator itc = d_cache.begin(); itc != d_cache.end(); ++itc ){
    Node a = itc->first;
    Trace("sygus-fair-debug") << "  look at anchor " << a << "..." << std::endl;
    // check whether a is bounded by m
    Assert( d_anchor_to_measure_term.find( a )!=d_anchor_to_measure_term.end() );
    if( d_anchor_to_measure_term[a]==m ){
      for( std::map< TypeNode, std::map< unsigned, std::vector< Node > > >::iterator its = itc->second.d_sb_lemmas.begin();
           its != itc->second.d_sb_lemmas.end(); ++its ){
        TypeNode tn = its->first;
        TNode x = getFreeVar( tn );
        for( std::map< unsigned, std::vector< Node > >::iterator it = its->second.begin(); it != its->second.end(); ++it ){
          unsigned sz = it->first;
          int new_depth = ((int)itsz->second->d_curr_search_size) - ((int)sz);
          std::map< unsigned, std::vector< Node > >::iterator itt = itc->second.d_search_terms[tn].find( new_depth );
          if( itt!=itc->second.d_search_terms[tn].end() ){
            for (const TNode& t : itt->second)
            {
              if (!options::sygusSymBreakLazy()
                  || (d_active_terms.find(t) != d_active_terms.end()
                      && !it->second.empty()))
              {
                Node rlv = getRelevancyCondition(t);
                std::unordered_map<TNode, TNode, TNodeHashFunction> cache;
                for (const Node& lem : it->second)
                {
                  Node slem = lem.substitute(x, t, cache);
                  slem = nm->mkNode(OR, rlv, slem);
                  lemmas.push_back(slem);
                }
              }
            }
          }
        }
      }
    }
  }
}

void SygusSymBreakNew::check( std::vector< Node >& lemmas ) {
  Trace("sygus-sb") << "SygusSymBreakNew::check" << std::endl;

  // check for externally registered symmetry breaking lemmas
  std::vector<Node> anchors;
  if (d_tds->hasSymBreakLemmas(anchors))
  {
    for (const Node& a : anchors)
    {
      // is this a registered enumerator?
      if (d_register_st.find(a) != d_register_st.end())
      {
        // symmetry breaking lemmas should only be for enumerators
        Assert(d_register_st[a]);
        // If this is a non-basic enumerator, process its symmetry breaking
        // clauses. Since this class is not responsible for basic enumerators,
        // their symmetry breaking clauses are ignored.
        if (!d_tds->isBasicEnumerator(a))
        {
          std::vector<Node> sbl;
          d_tds->getSymBreakLemmas(a, sbl);
          for (const Node& lem : sbl)
          {
            if (d_tds->isSymBreakLemmaTemplate(lem))
            {
              // register the lemma template
              TypeNode tn = d_tds->getTypeForSymBreakLemma(lem);
              unsigned sz = d_tds->getSizeForSymBreakLemma(lem);
              registerSymBreakLemma(tn, lem, sz, a, lemmas);
            }
            else
            {
              Trace("dt-sygus-debug")
                  << "DT sym break lemma : " << lem << std::endl;
              // it is a normal lemma
              lemmas.push_back(lem);
            }
          }
          d_tds->clearSymBreakLemmas(a);
        }
      }
    }
    if (!lemmas.empty())
    {
      return;
    }
  }

  // register search values, add symmetry breaking lemmas if applicable
  std::vector<Node> es;
  d_tds->getEnumerators(es);
  bool needsRecheck = false;
  // for each enumerator registered to d_tds
  for (Node& prog : es)
  {
    if (d_register_st.find(prog) == d_register_st.end())
    {
      // not yet registered, do so now
      registerSizeTerm(prog, lemmas);
      needsRecheck = true;
    }
    else
    {
      Trace("dt-sygus-debug") << "Checking model value of " << prog << "..."
                              << std::endl;
      Assert(prog.getType().isDatatype());
      Node progv = d_td->getValuation().getModel()->getValue( prog );
      if (Trace.isOn("dt-sygus"))
      {
        Trace("dt-sygus") << "* DT model : " << prog << " -> ";
        std::stringstream ss;
        Printer::getPrinter(options::outputLanguage())
            ->toStreamSygus(ss, progv);
        Trace("dt-sygus") << ss.str() << std::endl;
      }
      // first check that the value progv for prog is what we expected
      bool isExc = true;
      if (checkValue(prog, progv, 0, lemmas))
      {
        isExc = false;
        //debugging : ensure fairness was properly handled
        if( options::sygusFair()==SYGUS_FAIR_DT_SIZE ){  
          Node prog_sz = NodeManager::currentNM()->mkNode( kind::DT_SIZE, prog );
          Node prog_szv = d_td->getValuation().getModel()->getValue( prog_sz );
          Node progv_sz = NodeManager::currentNM()->mkNode( kind::DT_SIZE, progv );
            
          Trace("sygus-sb") << "  Mv[" << prog << "] = " << progv << ", size = " << prog_szv << std::endl;
          if( prog_szv.getConst<Rational>().getNumerator().toUnsignedInt() > getSearchSizeForAnchor( prog ) ){
            AlwaysAssert( false );
            Node szlem = NodeManager::currentNM()->mkNode( kind::OR, prog.eqNode( progv ).negate(),
                                                                     prog_sz.eqNode( progv_sz ) );
            Trace("sygus-sb-warn") << "SygusSymBreak : WARNING : adding size correction : " << szlem << std::endl;
            lemmas.push_back(szlem);
            isExc = true;
          }
        }

        // register the search value ( prog -> progv ), this may invoke symmetry
        // breaking
        if (!isExc && options::sygusSymBreakDynamic())
        {
          bool isVarAgnostic = d_tds->isVariableAgnosticEnumerator(prog);
          // check that it is unique up to theory-specific rewriting and
          // conjecture-specific symmetry breaking.
          Node rsv = registerSearchValue(
              prog, prog, progv, 0, lemmas, isVarAgnostic, true);
          if (rsv.isNull())
          {
            isExc = true;
            Trace("sygus-sb") << "  SygusSymBreakNew::check: ...added new symmetry breaking lemma for " << prog << "." << std::endl;
          }
          else
          {
            Trace("dt-sygus") << "  ...success." << std::endl;
          }
        }
      }
      SygusSymBreakOkAttribute ssbo;
      prog.setAttribute(ssbo, !isExc);
    }
  }
  Trace("sygus-sb") << "SygusSymBreakNew::check: finished." << std::endl;
  if (needsRecheck)
  {
    Trace("sygus-sb") << " SygusSymBreakNew::rechecking..." << std::endl;
    return check(lemmas);
  }

  if (Trace.isOn("cegqi-engine") && !d_szinfo.empty())
  {
    if (lemmas.empty())
    {
      Trace("cegqi-engine") << "*** Sygus : passed datatypes check. term size(s) : ";
      for (std::pair<const Node, std::unique_ptr<SygusSizeDecisionStrategy>>&
               p : d_szinfo)
      {
        SygusSizeDecisionStrategy* s = p.second.get();
        Trace("cegqi-engine") << s->d_curr_search_size << " ";
      }
      Trace("cegqi-engine") << std::endl;
    }
    else
    {
      Trace("cegqi-engine")
          << "*** Sygus : produced symmetry breaking lemmas" << std::endl;
      for (const Node& lem : lemmas)
      {
        Trace("cegqi-engine-debug") << "  " << lem << std::endl;
      }
    }
  }
}

bool SygusSymBreakNew::checkValue(Node n,
                                  Node vn,
                                  int ind,
                                  std::vector<Node>& lemmas)
{
  if (vn.getKind() != kind::APPLY_CONSTRUCTOR)
  {
    // all datatype terms should be constant here
    Assert(!vn.getType().isDatatype());
    return true;
  }
  NodeManager* nm = NodeManager::currentNM();
  if (Trace.isOn("sygus-sb-check-value"))
  {
    Node prog_sz = nm->mkNode(DT_SIZE, n);
    Node prog_szv = d_td->getValuation().getModel()->getValue( prog_sz );
    for( int i=0; i<ind; i++ ){
      Trace("sygus-sb-check-value") << "  ";
    }
    Trace("sygus-sb-check-value") << n << " : " << vn << " : " << prog_szv
                                  << std::endl;
  }
  TypeNode tn = n.getType();
  const Datatype& dt = tn.getDatatype();
  Assert(dt.isSygus());

  // ensure that the expected size bound is met
  int cindex = DatatypesRewriter::indexOf(vn.getOperator());
  Node tst = DatatypesRewriter::mkTester( n, cindex, dt );
  bool hastst = d_td->getEqualityEngine()->hasTerm(tst);
  Node tstrep;
  if (hastst)
  {
    tstrep = d_td->getEqualityEngine()->getRepresentative(tst);
  }
  if (!hastst || tstrep != d_true)
  {
    Trace("sygus-check-value") << "- has tester : " << tst << " : "
                               << (hastst ? "true" : "false");
    Trace("sygus-check-value") << ", value=" << tstrep << std::endl;
    if( !hastst ){
      // This should not happen generally, it is caused by a sygus term not
      // being assigned a tester.
      Node split = DatatypesRewriter::mkSplit(n, dt);
      Trace("sygus-sb") << "  SygusSymBreakNew::check: ...WARNING: considered "
                           "missing split for "
                        << n << "." << std::endl;
      Assert( !split.isNull() );
      lemmas.push_back( split );
      return false;
    }
  }
  for( unsigned i=0; i<vn.getNumChildren(); i++ ){
    Node sel = nm->mkNode(
        APPLY_SELECTOR_TOTAL,
        Node::fromExpr(dt[cindex].getSelectorInternal(tn.toType(), i)),
        n);
    if (!checkValue(sel, vn[i], ind + 1, lemmas))
    {
      return false;
    }
  }
  return true;
}

Node SygusSymBreakNew::getCurrentTemplate( Node n, std::map< TypeNode, int >& var_count ) {
  if( d_active_terms.find( n )!=d_active_terms.end() ){
    TypeNode tn = n.getType();
    IntMap::const_iterator it = d_testers.find( n );
    Assert( it != d_testers.end() );
    const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
    int tindex = (*it).second;
    Assert( tindex>=0 );
    Assert( tindex<(int)dt.getNumConstructors() );
    std::vector< Node > children;
    children.push_back( Node::fromExpr( dt[tindex].getConstructor() ) );
    for( unsigned i=0; i<dt[tindex].getNumArgs(); i++ ){
      Node sel = NodeManager::currentNM()->mkNode( kind::APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[tindex].getSelectorInternal( tn.toType(), i ) ), n );
      Node cc = getCurrentTemplate( sel, var_count );
      children.push_back( cc );
    }
    return NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, children );
  }else{
    return d_tds->getFreeVarInc( n.getType(), var_count );
  }
}

Node SygusSymBreakNew::SygusSizeDecisionStrategy::getOrMkMeasureValue(
    std::vector<Node>& lemmas)
{
  if (d_measure_value.isNull())
  {
    d_measure_value = NodeManager::currentNM()->mkSkolem(
        "mt", NodeManager::currentNM()->integerType());
    lemmas.push_back(NodeManager::currentNM()->mkNode(
        kind::GEQ,
        d_measure_value,
        NodeManager::currentNM()->mkConst(Rational(0))));
  }
  return d_measure_value;
}

Node SygusSymBreakNew::SygusSizeDecisionStrategy::getOrMkActiveMeasureValue(
    std::vector<Node>& lemmas, bool mkNew)
{
  if (mkNew)
  {
    Node new_mt = NodeManager::currentNM()->mkSkolem(
        "mt", NodeManager::currentNM()->integerType());
    lemmas.push_back(NodeManager::currentNM()->mkNode(
        kind::GEQ, new_mt, NodeManager::currentNM()->mkConst(Rational(0))));
    d_measure_value_active = new_mt;
  }
  else if (d_measure_value_active.isNull())
  {
    d_measure_value_active = getOrMkMeasureValue(lemmas);
  }
  return d_measure_value_active;
}

Node SygusSymBreakNew::SygusSizeDecisionStrategy::mkLiteral(unsigned s)
{
  if (options::sygusFair() == SYGUS_FAIR_NONE)
  {
    return Node::null();
  }
  if (options::sygusAbortSize() != -1
      && static_cast<int>(s) > options::sygusAbortSize())
  {
    std::stringstream ss;
    ss << "Maximum term size (" << options::sygusAbortSize()
       << ") for enumerative SyGuS exceeded.";
    throw LogicException(ss.str());
  }
  Assert(!d_this.isNull());
  NodeManager* nm = NodeManager::currentNM();
  Trace("cegqi-engine") << "******* Sygus : allocate size literal " << s
                        << " for " << d_this << std::endl;
  return nm->mkNode(DT_SYGUS_BOUND, d_this, nm->mkConst(Rational(s)));
}

int SygusSymBreakNew::getGuardStatus( Node g ) {
  bool value;
  if( d_td->getValuation().hasSatValue( g, value ) ) {
    if( value ){
      return 1;
    }else{
      return -1;
    }
  }else{
    return 0;
  }
}

