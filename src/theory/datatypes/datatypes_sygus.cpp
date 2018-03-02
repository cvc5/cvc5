/*********************                                                        */
/*! \file datatypes_sygus.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus/sygus_explain.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/theory_model.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

SygusSymBreakNew::SygusSymBreakNew(TheoryDatatypes* td,
                                   quantifiers::TermDbSygus* tds,
                                   context::Context* c)
    : d_td(td),
      d_tds(tds),
      d_testers(c),
      d_is_const(c),
      d_testers_exp(c),
      d_active_terms(c),
      d_currTermSize(c) {
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
}

SygusSymBreakNew::~SygusSymBreakNew() {
  for( std::map< Node, SearchSizeInfo * >::iterator it = d_szinfo.begin(); it != d_szinfo.end(); ++it ){
    delete it->second;
  }
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
  if( n.getKind()==kind::DT_SYGUS_TERM_ORDER ){
    if( polarity ){
      Trace("sygus-sb-torder") << "Sygus term order : " << n[0] << " < " << n[1] << std::endl;
      Node comm_sb = getTermOrderPredicate( n[0], n[1] );
      Node comm_lem = NodeManager::currentNM()->mkNode( kind::OR, n.negate(), comm_sb );
      lemmas.push_back( comm_lem );
    }
  }else if( n.getKind()==kind::DT_SYGUS_BOUND ){
    Node m = n[0];
    Trace("sygus-fair") << "Have sygus bound : " << n << ", polarity=" << polarity << " on measure " << m << std::endl;
    registerMeasureTerm( m );
    if( options::sygusFair()==SYGUS_FAIR_DT_SIZE ){
      std::map< Node, SearchSizeInfo * >::iterator its = d_szinfo.find( m );
      Assert( its!=d_szinfo.end() );
      Node mt = its->second->getOrMkSygusMeasureTerm( lemmas );
      //it relates the measure term to arithmetic
      Node blem = n.eqNode( NodeManager::currentNM()->mkNode( kind::LEQ, mt, n[1] ) );
      lemmas.push_back( blem );
    }
    if( polarity ){
      unsigned s = n[1].getConst<Rational>().getNumerator().toUnsignedInt();
      notifySearchSize( m, s, n, lemmas );
    }
  }else if( n.getKind() == kind::DT_SYGUS_IS_CONST ){
    assertIsConst( n[0], polarity, lemmas );
  }else if( n.getKind() == kind::DT_HEIGHT_BOUND || n.getKind()==DT_SIZE_BOUND ){
    //reduce to arithmetic TODO ?

  }
}

void SygusSymBreakNew::assertIsConst( Node n, bool polarity, std::vector< Node >& lemmas ) {
  if( d_active_terms.find( n )!=d_active_terms.end() ) {
    // what kind of constructor is n?
    IntMap::const_iterator itt = d_testers.find( n );
    Assert( itt!=d_testers.end() );
    int tindex = (*itt).second;
    TypeNode tn = n.getType();
    const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
    Node lem;
    if( dt[tindex].getNumArgs()==0 ){
      // is this a constant?
      Node sygus_op = Node::fromExpr( dt[tindex].getSygusOp() );
      if( sygus_op.isConst()!=polarity ){
        lem = NodeManager::currentNM()->mkNode( kind::DT_SYGUS_IS_CONST, n );
        if( polarity ){
          lem.negate();
        }
      }
    }else{
      // reduce
      std::vector< Node > child_conj;
      for( unsigned j=0; j<dt[tindex].getNumArgs(); j++ ){
        Node sel = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[tindex].getSelectorInternal( tn.toType(), j ) ), n );
        child_conj.push_back( NodeManager::currentNM()->mkNode( kind::DT_SYGUS_IS_CONST, sel ) );
      }
      lem = child_conj.size()==1 ? child_conj[0] : NodeManager::currentNM()->mkNode( kind::AND, child_conj );
      // only an implication (TODO : strengthen?)
      lem = NodeManager::currentNM()->mkNode( kind::OR, lem.negate(), NodeManager::currentNM()->mkNode( kind::DT_SYGUS_IS_CONST, n ) );
    }
    if( !lem.isNull() ){
      Trace("sygus-isc") << "Sygus is-const lemma : " << lem << std::endl;
      Node rlv = getRelevancyCondition( n );
      if( !rlv.isNull() ){
        lem = NodeManager::currentNM()->mkNode( kind::OR, rlv.negate(), lem );
      }
      lemmas.push_back( lem );
    }
  }else{
    // lazy
    d_is_const[n] = polarity ? 1 : -1;
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
      std::map< Node, Node >::iterator it = d_term_to_anchor.find( n[0] );
      if( it!=d_term_to_anchor.end() ) {
        d_term_to_anchor[n] = it->second;
        d_term_to_anchor_conj[n] = d_term_to_anchor_conj[n[0]];
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
        d_term_to_anchor_conj[n] = d_tds->getConjectureForEnumerator(n);
        // this assertion fails if we have a sygus term in the search that is unmeasured
        Assert(d_term_to_anchor_conj[n] != NULL);
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
  d_active_terms.insert( n );
  Trace("sygus-sb-debug2") << "Sygus : activate term : " << n << " : " << exp << std::endl;  
  
  /* TODO
  IntMap::const_iterator itisc = d_is_const.find( n );
  if( itisc != d_is_const.end() ){
    assertIsConst( n, (*itisc).second==1, lemmas );
  }
  */
  
  TypeNode ntn = n.getType();
  const Datatype& dt = ((DatatypeType)ntn.toType()).getDatatype();
  
  // get the search size for this
  Assert( d_term_to_anchor.find( n )!=d_term_to_anchor.end() );
  Node a = d_term_to_anchor[n];
  Assert( d_anchor_to_measure_term.find( a )!=d_anchor_to_measure_term.end() );
  Node m = d_anchor_to_measure_term[a];
  std::map< Node, SearchSizeInfo * >::iterator itsz = d_szinfo.find( m );
  Assert( itsz!=d_szinfo.end() );
  unsigned ssz = itsz->second->d_curr_search_size;
  
  if( options::sygusFair()==SYGUS_FAIR_DIRECT ){
    if( dt[tindex].getNumArgs()>0 ){
      // consider lower bounds for size of types
      unsigned lb_add = d_tds->getMinConsTermSize( ntn, tindex );
      unsigned lb_rem = n==a ? 0 : d_tds->getMinTermSize( ntn );
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

  unsigned max_depth = ssz>=d ? ssz-d : 0;
  unsigned min_depth = d_simple_proc[exp];
  if( min_depth<=max_depth ){
    TNode x = getFreeVar( ntn );
    std::vector<Node> sb_lemmas;
    for (unsigned ds = 0; ds <= max_depth; ds++)
    {
      // static conjecture-independent symmetry breaking
      Node ipred = getSimpleSymBreakPred(ntn, tindex, ds);
      if (!ipred.isNull())
      {
        sb_lemmas.push_back(ipred);
      }
      // static conjecture-dependent symmetry breaking
      std::map<Node, quantifiers::CegConjecture*>::iterator itc =
          d_term_to_anchor_conj.find(n);
      if (itc != d_term_to_anchor_conj.end())
      {
        quantifiers::CegConjecture* conj = itc->second;
        Assert(conj != NULL);
        Node dpred = conj->getSymmetryBreakingPredicate(x, a, ntn, tindex, ds);
        if (!dpred.isNull())
        {
          sb_lemmas.push_back(dpred);
        }
      }
    }

    // add the above symmetry breaking predicates to lemmas
    Node rlv = getRelevancyCondition(n);
    for (unsigned i = 0; i < sb_lemmas.size(); i++)
    {
      Node pred = sb_lemmas[i].substitute(x, n);
      if (!rlv.isNull())
      {
        pred = NodeManager::currentNM()->mkNode(kind::OR, rlv.negate(), pred);
      }
      lemmas.push_back(pred);
    }
  }
  d_simple_proc[exp] = max_depth + 1;

  // now activate the children those testers were previously asserted in this
  // context and are awaiting activation, if they exist.
  if( options::sygusSymBreakLazy() ){
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
            disj.push_back(DatatypesRewriter::mkTester(n[0], i, dt));
          }
          else
          {
            excl = true;
          }
        }
        Assert( !disj.empty() );
        if( excl ){
          cond = disj.size()==1 ? disj[0] : NodeManager::currentNM()->mkNode( kind::OR, disj );
        }
      }else{
        int sindex = Datatype::cindexOf( selExpr );
        Assert( sindex!=-1 );
        cond = DatatypesRewriter::mkTester( n[0], sindex, dt );
      }
      Node c1 = getRelevancyCondition( n[0] );
      if( cond.isNull() ){
        cond = c1;
      }else if( !c1.isNull() ){
        cond = NodeManager::currentNM()->mkNode( kind::AND, cond, c1 );
      }
    }
    Trace("sygus-sb-debug2") << "Relevancy condition for " << n << " is " << cond << std::endl;
    d_rlv_cond[n] = cond;
    return cond;
  }else{
    return itr->second;
  }
}

Node SygusSymBreakNew::getSimpleSymBreakPred( TypeNode tn, int tindex, unsigned depth ) {
  std::map< unsigned, Node >::iterator it = d_simple_sb_pred[tn][tindex].find( depth );
  if( it==d_simple_sb_pred[tn][tindex].end() ){
    Node n = getFreeVar( tn );
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    Assert( tindex>=0 && tindex<(int)dt.getNumConstructors() ); 
    //conjunctive conclusion of lemma
    std::vector< Node > sbp_conj;
    
    if( depth==0 ){
      //fairness
      if( options::sygusFair()==SYGUS_FAIR_DT_SIZE ){
        Node szl = NodeManager::currentNM()->mkNode( DT_SIZE, n );
        Node szr = NodeManager::currentNM()->mkNode( DT_SIZE, DatatypesRewriter::getInstCons( n, dt, tindex ) );
        szr = Rewriter::rewrite( szr );
        sbp_conj.push_back( szl.eqNode( szr ) );
        //sbp_conj.push_back( NodeManager::currentNM()->mkNode( kind::GEQ, szl, NodeManager::currentNM()->mkConst( Rational(0) ) ) );
      }
    }
    
    //symmetry breaking
    Kind nk = d_tds->getConsNumKind( tn, tindex );
    if( options::sygusSymBreak() ){
      // if less than the maximum depth we consider
      if( depth<2 ){
        //get children
        std::vector< Node > children;
        for( unsigned j=0; j<dt[tindex].getNumArgs(); j++ ){
          Node sel = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[tindex].getSelectorInternal( tn.toType(), j ) ), n );
          Assert( sel.getType().isDatatype() );
          Assert( ((DatatypeType)sel.getType().toType()).getDatatype().isSygus() );
          children.push_back( sel );
          d_tds->registerSygusType( sel.getType() );
        }
        //builtin type
        TypeNode tnb = TypeNode::fromType( dt.getSygusType() );
        
        // direct solving for children
        //   for instance, we may want to insist that the LHS of MINUS is 0
        std::map< unsigned, unsigned > children_solved;
        for( unsigned j=0; j<dt[tindex].getNumArgs(); j++ ){
          int i = d_tds->solveForArgument( tn, tindex, j );
          if( i>=0 ){
            children_solved[j] = i;
            TypeNode ctn = children[j].getType();
            const Datatype& cdt = ((DatatypeType)(ctn).toType()).getDatatype();
            Assert( i<(int)cdt.getNumConstructors() );
            sbp_conj.push_back( DatatypesRewriter::mkTester( children[j], i, cdt ) );
          }
        }
        
        // depth 1 symmetry breaking : talks about direct children
        if( depth==1 ){
          if( nk!=UNDEFINED_KIND ){
            // commutative operators 
            if( quantifiers::TermUtil::isComm( nk ) ){
              if( children.size()==2 ){
                if( children[0].getType()==children[1].getType() ){
  #if 0
                  Node order_pred = NodeManager::currentNM()->mkNode( DT_SYGUS_TERM_ORDER, children[0], children[1] );
                  sbp_conj.push_back( order_pred );
                  Node child11 = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[tindex].getSelectorInternal( tn.toType(), 1 ) ), children[0] );
                  Assert( child11.getType()==children[1].getType() );
                  //chainable
                  if( children[0].getType()==tn ){
                    Node order_pred_trans = NodeManager::currentNM()->mkNode( OR, DatatypesRewriter::mkTester( children[0], tindex, dt ).negate(),
                                                                              NodeManager::currentNM()->mkNode( DT_SYGUS_TERM_ORDER, child11, children[1] ) );
                    sbp_conj.push_back( order_pred_trans );
                  }
  #else   
                  Node order_pred = getTermOrderPredicate( children[0], children[1] );
                  sbp_conj.push_back( order_pred );
  #endif
                }
              }
            }
            // operators whose arguments are non-additive (e.g. should be different)
            std::vector< unsigned > deq_child[2];
            if( children.size()==2 && children[0].getType()==tn ){
              bool argDeq = false;
              if( quantifiers::TermUtil::isNonAdditive( nk ) ){
                argDeq = true;
              }else{
                //other cases of rewriting x k x -> x'
                Node req_const;
                if( nk==GT || nk==LT || nk==XOR || nk==MINUS || nk==BITVECTOR_SUB || nk==BITVECTOR_XOR || nk==BITVECTOR_UREM_TOTAL ){
                  //must have the zero element
                  req_const = quantifiers::TermUtil::mkTypeValue(tnb, 0);
                }else if( nk==EQUAL || nk==LEQ || nk==GEQ || nk==BITVECTOR_XNOR ){
                  req_const = quantifiers::TermUtil::mkTypeMaxValue(tnb);
                }
                // cannot do division since we have to consider when both are zero
                if( !req_const.isNull() ){
                  if( d_tds->hasConst( tn, req_const ) ){
                    argDeq = true;
                  }
                }
              }
              if( argDeq ){
                deq_child[0].push_back( 0 );deq_child[1].push_back( 1 );
              }
            }
            if( nk==ITE || nk==STRING_STRREPL ){
              deq_child[0].push_back( 1 );deq_child[1].push_back( 2 );
            }
            if( nk==STRING_STRREPL ){
              deq_child[0].push_back( 0 );deq_child[1].push_back( 1 );
            }
            for( unsigned i=0; i<deq_child[0].size(); i++ ){
              unsigned c1 = deq_child[0][i];
              unsigned c2 = deq_child[1][i];
              if( children[c1].getType()==children[c2].getType() ){
                if( !children[c1].getType().getCardinality().isOne() ){
                  sbp_conj.push_back( children[c1].eqNode( children[c2] ).negate() );
                }
              }
            }
            
            /*
            // division by zero  TODO ?
            if( nk==DIVISION || nk==DIVISION_TOTAL || nk==INTS_DIVISION || nk==INTS_DIVISION_TOTAL || 
                nk==INTS_MODULUS || nk==INTS_MODULUS_TOTAL ){
              Assert( children.size()==2 );
              // do not consider non-constant denominators ?
              sbp_conj.push_back( NodeManager::currentNM()->mkNode( kind::DT_SYGUS_IS_CONST, children[1] ) );
              // do not consider zero denominator
              Node tzero = d_tds->getTypeValue( tnb, 0 );
              int zero_arg = d_tds->getConstConsNum( children[1].getType(), tzero );
              if( zero_arg!=-1 ){
                
              }else{
                // semantic skolem for zero?
              }
            }else if( nk==BITVECTOR_UDIV_TOTAL || nk==BITVECTOR_UDIV || nk==BITVECTOR_SDIV || nk==BITVECTOR_UREM || nk==BITVECTOR_UREM_TOTAL ){

            }
            */
            
            Trace("sygus-sb-simple-debug") << "Process arguments for " << tn << " : " << nk << " : " << std::endl;
            // singular arguments (e.g. 0 for mult) 
            // redundant arguments (e.g. 0 for plus, 1 for mult)
            // right-associativity
            // simple rewrites
            for( unsigned j=0; j<dt[tindex].getNumArgs(); j++ ){
              Node nc = children[j];
              // if not already solved
              if( children_solved.find( j )==children_solved.end() ){
                TypeNode tnc = nc.getType();
                const Datatype& cdt = ((DatatypeType)(tnc).toType()).getDatatype();
                for( unsigned k=0; k<cdt.getNumConstructors(); k++ ){
                  Kind nck = d_tds->getConsNumKind(tnc, k);
                  bool red = false;
                  // check if the argument is redundant
                  if (nck != UNDEFINED_KIND)
                  {
                    Trace("sygus-sb-simple-debug")
                        << "  argument " << j << " " << k << " is : " << nck
                        << std::endl;
                    red = !d_tds->considerArgKind(tnc, tn, nck, nk, j);
                  }
                  else
                  {
                    Node cc = d_tds->getConsNumConst(tnc, k);
                    if (!cc.isNull())
                    {
                      Trace("sygus-sb-simple-debug")
                          << "  argument " << j << " " << k
                          << " is constant : " << cc << std::endl;
                      red = !d_tds->considerConst(tnc, tn, cc, nk, j);
                    }else{
                      // defined function?
                    }
                  }
                  if (red)
                  {
                    Trace("sygus-sb-simple-debug")
                        << "  ...redundant." << std::endl;
                    sbp_conj.push_back(
                        DatatypesRewriter::mkTester(nc, k, cdt).negate());
                  }
                }
              }
            }
          }else{
            // defined function?
          }
        }else if( depth==2 ){
          if( nk!=UNDEFINED_KIND ){
            // commutative operators 
            if( quantifiers::TermUtil::isComm( nk ) ){
              if( children.size()==2 ){
                if( children[0].getType()==children[1].getType() ){
                  //chainable
                  // TODO : this is depth 2
                  if( children[0].getType()==tn ){
                    Node child11 = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[tindex].getSelectorInternal( tn.toType(), 1 ) ), children[0] );
                    Assert( child11.getType()==children[1].getType() );
                    Node order_pred_trans = NodeManager::currentNM()->mkNode( OR, DatatypesRewriter::mkTester( children[0], tindex, dt ).negate(),
                                                                              getTermOrderPredicate( child11, children[1] ) );

                    sbp_conj.push_back( order_pred_trans );
                  }
                }
              }
            }
          }
        }
      }
    }
    
    Node sb_pred;
    if( !sbp_conj.empty() ){
      sb_pred = sbp_conj.size()==1 ? sbp_conj[0] : NodeManager::currentNM()->mkNode( kind::AND, sbp_conj );
      Trace("sygus-sb-simple") << "Simple predicate for " << tn << " index " << tindex << " (" << nk << ") at depth " << depth << " : " << std::endl;
      Trace("sygus-sb-simple") << "   " << sb_pred << std::endl;
      sb_pred = NodeManager::currentNM()->mkNode( kind::OR, DatatypesRewriter::mkTester( n, tindex, dt ).negate(), sb_pred );
    }
    d_simple_sb_pred[tn][tindex][depth] = sb_pred;
    return sb_pred;
  }else{
    return it->second;
  }
}

TNode SygusSymBreakNew::getFreeVar( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_free_var.find( tn );
  if( it==d_free_var.end() ){
    Node x = NodeManager::currentNM()->mkSkolem( "x", tn );
    d_free_var[tn] = x;
    return x;
  }else{
    return it->second;
  }
}

unsigned SygusSymBreakNew::processSelectorChain( Node n, std::map< TypeNode, Node >& top_level, std::map< Node, unsigned >& tdepth, std::vector< Node >& lemmas ) {
  unsigned ret = 0;
  if( n.getKind()==APPLY_SELECTOR_TOTAL ){
    ret = processSelectorChain( n[0], top_level, tdepth, lemmas );
  }
  TypeNode tn = n.getType();
  if( top_level.find( tn )==top_level.end() ){
    top_level[tn] = n;
    //tdepth[n] = ret;
    registerSearchTerm( tn, ret, n, true, lemmas );
  }else{
    registerSearchTerm( tn, ret, n, false, lemmas );
  }
  tdepth[n] = ret;
  return ret+1;
}

void SygusSymBreakNew::registerSearchTerm( TypeNode tn, unsigned d, Node n, bool topLevel, std::vector< Node >& lemmas ) {
  //register this term
  std::map< Node, Node >::iterator ita = d_term_to_anchor.find( n );
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

bool SygusSymBreakNew::registerSearchValue( Node a, Node n, Node nv, unsigned d, std::vector< Node >& lemmas ) {
  Assert( n.getType()==nv.getType() );
  Assert( nv.getKind()==APPLY_CONSTRUCTOR );
  TypeNode tn = n.getType(); 
  // currently bottom-up, could be top-down?
  if( nv.getNumChildren()>0 ){
    const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
    unsigned cindex = Datatype::indexOf( nv.getOperator().toExpr() );
    for( unsigned i=0; i<nv.getNumChildren(); i++ ){
      Node sel = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[cindex].getSelectorInternal( tn.toType(), i ) ), n );
      if( !registerSearchValue( a, sel, nv[i], d+1, lemmas ) ){
        return false;
      }
    }
  }
  Trace("sygus-sb-debug2") << "Registering search value " << n << " -> " << nv << std::endl;
  // must do this for all nodes, regardless of top-level
  if( d_cache[a].d_search_val_proc.find( nv )==d_cache[a].d_search_val_proc.end() ){
    d_cache[a].d_search_val_proc[nv] = true;
    // get the root (for PBE symmetry breaking)
    Assert(d_term_to_anchor_conj.find(a) != d_term_to_anchor_conj.end());
    quantifiers::CegConjecture* aconj = d_term_to_anchor_conj[a];
    Assert(aconj != NULL);
    Trace("sygus-sb-debug") << "  ...register search value " << nv << ", type=" << tn << std::endl;
    Node bv = d_tds->sygusToBuiltin( nv, tn );
    Trace("sygus-sb-debug") << "  ......builtin is " << bv << std::endl;
    Node bvr = d_tds->getExtRewriter()->extendedRewrite(bv);
    Trace("sygus-sb-debug") << "  ......rewrites to " << bvr << std::endl;
    Trace("dt-sygus") << "  * DT builtin : " << n << " -> " << bvr << std::endl;
    unsigned sz = d_tds->getSygusTermSize( nv );      
    std::vector< Node > exp;
    bool do_exclude = false;
    if( d_tds->involvesDivByZero( bvr ) ){
      Node x = getFreeVar( tn );
      quantifiers::DivByZeroSygusInvarianceTest dbzet;
      Trace("sygus-sb-mexp-debug") << "Minimize explanation for div-by-zero in " << d_tds->sygusToBuiltin( nv ) << std::endl;
      d_tds->getExplain()->getExplanationFor(
          x, nv, exp, dbzet, Node::null(), sz);
      do_exclude = true;
    }else{
      std::map< Node, Node >::iterator itsv = d_cache[a].d_search_val[tn].find( bvr );
      Node bad_val_bvr;
      bool by_examples = false;
      if( itsv==d_cache[a].d_search_val[tn].end() ){
        // TODO (github #1210) conjecture-specific symmetry breaking
        // this should be generalized and encapsulated within the CegConjecture
        // class
        // is it equivalent under examples?
        Node bvr_equiv;
        if (aconj->getPbe()->hasExamples(a)) {
          bvr_equiv = aconj->getPbe()->addSearchVal(tn, a, bvr);
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
        // add to the sampler database object
        std::map<TypeNode, quantifiers::SygusSampler>::iterator its =
            d_sampler[a].find(tn);
        if (its == d_sampler[a].end())
        {
          d_sampler[a][tn].initializeSygus(
              d_tds, nv, options::sygusSamples(), false);
          its = d_sampler[a].find(tn);
        }
        Node bvr_sample_ret;
        std::map<Node, Node>::iterator itsv =
            d_cache[a].d_search_val_sample[tn].find(bvr);
        if (itsv == d_cache[a].d_search_val_sample[tn].end())
        {
          // initialize the sampler for the rewritten form of this node
          bvr_sample_ret = its->second.registerTerm(bvr);
          d_cache[a].d_search_val_sample[tn][bvr] = bvr_sample_ret;
        }
        else
        {
          bvr_sample_ret = itsv->second;
        }

        // register the current node with the sampler
        Node sample_ret = its->second.registerTerm(bv);

        // bv and bvr should be equivalent under examples
        if (sample_ret != bvr_sample_ret)
        {
          // we have detected unsoundness in the rewriter
          Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
          std::ostream* out = nodeManagerOptions.getOut();
          (*out) << "(unsound-rewrite " << bv << " " << bvr << ")" << std::endl;
          // debugging information
          if (Trace.isOn("sygus-rr-debug"))
          {
            int pt_index = its->second.getDiffSamplePointIndex(bv, bvr);
            if (pt_index >= 0)
            {
              Trace("sygus-rr-debug")
                  << "; unsound: are not equivalent for : " << std::endl;
              std::vector<Node> vars;
              std::vector<Node> pt;
              its->second.getSamplePoint(pt_index, vars, pt);
              Assert(vars.size() == pt.size());
              for (unsigned i = 0, size = pt.size(); i < size; i++)
              {
                Trace("sygus-rr-debug") << "; unsound:    " << vars[i] << " -> "
                                        << pt[i] << std::endl;
              }
              Node bv_e = its->second.evaluate(bv, pt_index);
              Node pbv_e = its->second.evaluate(bvr, pt_index);
              Assert(bv_e != pbv_e);
              Trace("sygus-rr-debug") << "; unsound: where they evaluate to "
                                      << pbv_e << " and " << bv_e << std::endl;
            }
            else
            {
              Assert(false);
            }
          }
        }
      }

      if( !bad_val_bvr.isNull() ){
        Node bad_val = nv;
        Node bad_val_o = d_cache[a].d_search_val[tn][bad_val_bvr];
        Assert( d_cache[a].d_search_val_sz[tn].find( bad_val_bvr )!=d_cache[a].d_search_val_sz[tn].end() );
        unsigned prev_sz = d_cache[a].d_search_val_sz[tn][bad_val_bvr];
        if( prev_sz>sz ){
          //swap : the excluded value is the previous
          d_cache[a].d_search_val_sz[tn][bad_val_bvr] = sz;
          bad_val = d_cache[a].d_search_val[tn][bad_val_bvr];
          bad_val_o = nv;
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

        Node x = getFreeVar( tn );
        
        // do analysis of the evaluation  FIXME: does not work (evaluation is non-constant)
        quantifiers::EquivSygusInvarianceTest eset;
        eset.init(d_tds, tn, aconj, a, bvr);
        Trace("sygus-sb-mexp-debug") << "Minimize explanation for eval[" << d_tds->sygusToBuiltin( bad_val ) << "] = " << bvr << std::endl;
        d_tds->getExplain()->getExplanationFor(
            x, bad_val, exp, eset, bad_val_o, sz);
        do_exclude = true;
      }
    }
    if( do_exclude ){
      Node lem = exp.size()==1 ? exp[0] : NodeManager::currentNM()->mkNode( kind::AND, exp );
      lem = lem.negate();
      /*  add min type depth to size : TODO?
      Assert( d_term_to_anchor.find( n )!=d_term_to_anchor.end() );
      TypeNode atype = d_term_to_anchor[n].getType();
      if( atype!=tn ){
        unsigned min_type_depth = d_tds->getMinTypeDepth( atype, tn );
        if( min_type_depth>0 ){
          Trace("sygus-sb-exc") << "  ........min type depth for " << ((DatatypeType)tn.toType()).getDatatype().getName() << " in ";
          Trace("sygus-sb-exc") << ((DatatypeType)atype.toType()).getDatatype().getName() << " is " << min_type_depth << std::endl;
          sz = sz + min_type_depth;
        }
      }
      */
      Trace("sygus-sb-exc") << "  ........exc lemma is " << lem << ", size = " << sz << std::endl;
      registerSymBreakLemma( tn, lem, sz, a, lemmas );
      Trace("dt-sygus")
          << "  ...excluded by dynamic symmetry breaking, based on " << n
          << " == " << bvr << std::endl;
      return false;
    }
  }
  return true;
}



void SygusSymBreakNew::registerSymBreakLemma( TypeNode tn, Node lem, unsigned sz, Node a, std::vector< Node >& lemmas ) {
  // lem holds for all terms of type tn, and is applicable to terms of size sz
  Trace("sygus-sb-debug") << "  register sym break lemma : " << lem << ", size " << sz << std::endl;
  Assert( !a.isNull() );
  d_cache[a].d_sb_lemmas[tn][sz].push_back( lem );
  TNode x = getFreeVar( tn );
  unsigned csz = getSearchSizeForAnchor( a );
  int max_depth = ((int)csz)-((int)sz);
  for( int d=0; d<=max_depth; d++ ){
    std::map< unsigned, std::vector< Node > >::iterator itt = d_cache[a].d_search_terms[tn].find( d );
    if( itt!=d_cache[a].d_search_terms[tn].end() ){
      for( unsigned k=0; k<itt->second.size(); k++ ){
        TNode t = itt->second[k];  
        if( !options::sygusSymBreakLazy() || d_active_terms.find( t )!=d_active_terms.end() ){
          addSymBreakLemma( tn, lem, x, t, sz, d, lemmas );
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
  std::map< TypeNode, std::map< unsigned, std::vector< Node > > >::iterator its = d_cache[a].d_sb_lemmas.find( tn );
  if( its != d_cache[a].d_sb_lemmas.end() ){
    TNode x = getFreeVar( tn );
    //get symmetry breaking lemmas for this term 
    unsigned csz = getSearchSizeForAnchor( a );
    int max_sz = ((int)csz) - ((int)d);
    for( std::map< unsigned, std::vector< Node > >::iterator it = its->second.begin(); it != its->second.end(); ++it ){
      if( (int)it->first<=max_sz ){
        for( unsigned k=0; k<it->second.size(); k++ ){
          Node lem = it->second[k];
          addSymBreakLemma( tn, lem, x, t, it->first, d, lemmas );
        }
      }
    }
  }
}

void SygusSymBreakNew::addSymBreakLemma( TypeNode tn, Node lem, TNode x, TNode n, unsigned lem_sz, unsigned n_depth, std::vector< Node >& lemmas ) {
  Assert( !options::sygusSymBreakLazy() || d_active_terms.find( n )!=d_active_terms.end() );
  // apply lemma
  Node slem = lem.substitute( x, n );
  Trace("sygus-sb-exc-debug") << "SymBreak lemma : " << slem << std::endl;
  Node rlv = getRelevancyCondition( n );
  if( !rlv.isNull() ){
    slem = NodeManager::currentNM()->mkNode( kind::OR, rlv.negate(), slem );
  }
  lemmas.push_back( slem );
}
  
void SygusSymBreakNew::preRegisterTerm( TNode n, std::vector< Node >& lemmas  ) {
  if( n.isVar() ){
    Trace("sygus-sb-debug") << "Pre-register variable : " << n << std::endl;
    registerSizeTerm( n, lemmas );
  }
}

void SygusSymBreakNew::registerSizeTerm( Node e, std::vector< Node >& lemmas ) {
  if( d_register_st.find( e )==d_register_st.end() ){
    if( e.getType().isDatatype() ){
      const Datatype& dt = ((DatatypeType)(e.getType()).toType()).getDatatype();
      if( dt.isSygus() ){
        if (d_tds->isEnumerator(e))
        {
          d_register_st[e] = true;
          Node ag = d_tds->getActiveGuardForEnumerator(e);
          if( !ag.isNull() ){
            d_anchor_to_active_guard[e] = ag;
          }
          Node m;
          if( !ag.isNull() ){
            // if it has an active guard (it is an enumerator), use itself as measure term. This will enforce fairness on it independently.
            m = e;
          }else{
            // otherwise we enforce fairness in a unified way for all
            if( d_generic_measure_term.isNull() ){
              // choose e as master for all future terms
              d_generic_measure_term = e;
            }
            m = d_generic_measure_term;
          }
          Trace("sygus-sb") << "Sygus : register size term : " << e << " with measure " << m << std::endl;
          registerMeasureTerm( m );
          d_szinfo[m]->d_anchors.push_back( e );
          d_anchor_to_measure_term[e] = m;
          if( options::sygusFair()==SYGUS_FAIR_DT_SIZE ){
            // update constraints on the measure term
            if( options::sygusFairMax() ){
              if( options::sygusFair()==SYGUS_FAIR_DT_SIZE ){
                Node ds = NodeManager::currentNM()->mkNode( kind::DT_SIZE, e );
                Node slem = NodeManager::currentNM()->mkNode( kind::LEQ, ds, d_szinfo[m]->getOrMkSygusMeasureTerm( lemmas ) );
                lemmas.push_back( slem );
              }
            }else{
              Node mt = d_szinfo[m]->getOrMkSygusActiveMeasureTerm( lemmas );
              Node new_mt = NodeManager::currentNM()->mkSkolem( "mt", NodeManager::currentNM()->integerType() );
              lemmas.push_back( NodeManager::currentNM()->mkNode( kind::GEQ, new_mt, d_zero ) );
              if( options::sygusFair()==SYGUS_FAIR_DT_SIZE ){
                Node ds = NodeManager::currentNM()->mkNode( kind::DT_SIZE, e );
                lemmas.push_back( mt.eqNode( NodeManager::currentNM()->mkNode( kind::PLUS, new_mt, ds ) ) );
                //lemmas.push_back( NodeManager::currentNM()->mkNode( kind::GEQ, ds, d_zero ) );
              }
              d_szinfo[m]->d_sygus_measure_term_active = new_mt;
            }
          }
        }else{
          // not sure if it is a size term or not (may be registered later?)
        }
      }else{
        d_register_st[e] = false;
      }
    }else{
      d_register_st[e] = false;
    }
  }
}

void SygusSymBreakNew::registerMeasureTerm( Node m ) {
  std::map< Node, SearchSizeInfo * >::iterator it = d_szinfo.find( m );
  if( it==d_szinfo.end() ){
    Trace("sygus-sb") << "Sygus : register measure term : " << m << std::endl;
    d_szinfo[m] = new SearchSizeInfo( m, d_td->getSatContext() );
  }
}

void SygusSymBreakNew::notifySearchSize( Node m, unsigned s, Node exp, std::vector< Node >& lemmas ) {
  std::map< Node, SearchSizeInfo * >::iterator its = d_szinfo.find( m );
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
  std::map< Node, Node >::iterator ita = d_term_to_anchor.find( n );
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
  std::map< Node, SearchSizeInfo * >::iterator its = d_szinfo.find( m );
  Assert( its!=d_szinfo.end() );
  return its->second->d_curr_search_size;
}
  
void SygusSymBreakNew::incrementCurrentSearchSize( Node m, std::vector< Node >& lemmas ) {
  std::map< Node, SearchSizeInfo * >::iterator itsz = d_szinfo.find( m );
  Assert( itsz!=d_szinfo.end() );
  itsz->second->d_curr_search_size++;
  Trace("sygus-fair") << "  register search size " << itsz->second->d_curr_search_size << " for " << m << std::endl;
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
            for( unsigned k=0; k<itt->second.size(); k++ ){
              TNode t = itt->second[k];
              if( !options::sygusSymBreakLazy() || d_active_terms.find( t )!=d_active_terms.end() ){
                for( unsigned j=0; j<it->second.size(); j++ ){
                  Node lem = it->second[j];
                  addSymBreakLemma( tn, lem, x, t, sz, new_depth, lemmas );
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
  for( std::map< Node, bool >::iterator it = d_register_st.begin(); it != d_register_st.end(); ++it ){
    if( it->second ){
      Node prog = it->first;
      Node progv = d_td->getValuation().getModel()->getValue( prog );
      if (Trace.isOn("dt-sygus"))
      {
        Trace("dt-sygus") << "* DT model : " << prog << " -> ";
        std::stringstream ss;
        Printer::getPrinter(options::outputLanguage())
            ->toStreamSygus(ss, progv);
        Trace("dt-sygus") << ss.str() << std::endl;
      }
      // TODO : remove this step (ensure there is no way a sygus term cannot be assigned a tester before this point)
      if( !debugTesters( prog, progv, 0, lemmas ) ){
        Trace("sygus-sb") << "  SygusSymBreakNew::check: ...WARNING: considered missing split for " << prog << "." << std::endl;
        // this should not happen generally, it is caused by a sygus term not being assigned a tester
        //Assert( false );
      }else{
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
            lemmas.push_back( szlem );                                                     
            return;
          }
        }
        
        // register the search value ( prog -> progv ), this may invoke symmetry breaking 
        if( options::sygusSymBreakDynamic() ){
          if( !registerSearchValue( prog, prog, progv, 0, lemmas ) ){
            Trace("sygus-sb") << "  SygusSymBreakNew::check: ...added new symmetry breaking lemma for " << prog << "." << std::endl;
          }
          else
          {
            Trace("dt-sygus") << "  ...success." << std::endl;
          }
        }
      }
    }
  }
  //register any measured terms that we haven't encountered yet (should only be invoked on first call to check
  std::vector< Node > mts;
  d_tds->getEnumerators(mts);
  for( unsigned i=0; i<mts.size(); i++ ){
    registerSizeTerm( mts[i], lemmas );
  }
  Trace("sygus-sb") << " SygusSymBreakNew::check: finished." << std::endl;
  
  if( Trace.isOn("cegqi-engine") ){
    if( lemmas.empty() ){
      Trace("cegqi-engine") << "*** Sygus : passed datatypes check. term size(s) : ";
      for( std::map< Node, SearchSizeInfo * >::iterator it = d_szinfo.begin(); it != d_szinfo.end(); ++it ){
        SearchSizeInfo * s = it->second;
        Trace("cegqi-engine") << s->d_curr_search_size << " ";
      }
      Trace("cegqi-engine") << std::endl;
    }
  }
}

bool SygusSymBreakNew::debugTesters( Node n, Node vn, int ind, std::vector< Node >& lemmas ) {
  Assert( vn.getKind()==kind::APPLY_CONSTRUCTOR );
  if( Trace.isOn("sygus-sb-warn") ){
    Node prog_sz = NodeManager::currentNM()->mkNode( kind::DT_SIZE, n );
    Node prog_szv = d_td->getValuation().getModel()->getValue( prog_sz );
    for( int i=0; i<ind; i++ ){
      Trace("sygus-sb-warn") << "  ";
    }
    Trace("sygus-sb-warn") << n << " : " << vn << " : " << prog_szv << std::endl;
  }
  TypeNode tn = n.getType();
  const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
  int cindex = Datatype::indexOf( vn.getOperator().toExpr() );
  Node tst = DatatypesRewriter::mkTester( n, cindex, dt );
  bool hastst = d_td->getValuation().getModel()->hasTerm( tst );
  Node tstrep = d_td->getValuation().getModel()->getRepresentative( tst );
  if( !hastst || tstrep!=NodeManager::currentNM()->mkConst( true ) ){
    Trace("sygus-sb-warn") << "- has tester : " << tst << " : " << ( hastst ? "true" : "false" );
    Trace("sygus-sb-warn") << ", value=" << tstrep << std::endl;
    if( !hastst ){
      Node split = DatatypesRewriter::mkSplit(n, dt);
      Assert( !split.isNull() );
      lemmas.push_back( split );
      return false;
    }
  }
  for( unsigned i=0; i<vn.getNumChildren(); i++ ){
    Node sel = NodeManager::currentNM()->mkNode( kind::APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[cindex].getSelectorInternal( tn.toType(), i ) ), n );
    if( !debugTesters( sel, vn[i], ind+1, lemmas ) ){
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

Node SygusSymBreakNew::SearchSizeInfo::getOrMkSygusMeasureTerm( std::vector< Node >& lemmas ) {
  if( d_sygus_measure_term.isNull() ){
    d_sygus_measure_term = NodeManager::currentNM()->mkSkolem( "mt", NodeManager::currentNM()->integerType() );
    lemmas.push_back( NodeManager::currentNM()->mkNode( kind::GEQ, d_sygus_measure_term, NodeManager::currentNM()->mkConst( Rational(0) ) ) );
  }
  return d_sygus_measure_term;
}

Node SygusSymBreakNew::SearchSizeInfo::getOrMkSygusActiveMeasureTerm( std::vector< Node >& lemmas ) {
  if( d_sygus_measure_term_active.isNull() ){
    d_sygus_measure_term_active = getOrMkSygusMeasureTerm( lemmas );
  }
  return d_sygus_measure_term_active;
}

Node SygusSymBreakNew::SearchSizeInfo::getFairnessLiteral( unsigned s, TheoryDatatypes * d, std::vector< Node >& lemmas ) {
  if( options::sygusFair()!=SYGUS_FAIR_NONE ){
    std::map< unsigned, Node >::iterator it = d_lits.find( s );
    if( it==d_lits.end() ){
      if (options::sygusAbortSize() != -1 &&
          static_cast<int>(s) > options::sygusAbortSize()) {
        Message() << "Maximum term size (" << options::sygusAbortSize()
                  << ") for enumerative SyGuS exceeded." << std::endl;
        exit(1);
      }
      Assert( !d_this.isNull() );
      Node c = NodeManager::currentNM()->mkConst( Rational( s ) );
      Node lit = NodeManager::currentNM()->mkNode( DT_SYGUS_BOUND, d_this, c );
      lit = d->getValuation().ensureLiteral( lit );
      
      Trace("sygus-fair") << "******* Sygus : allocate size literal " << s << " for " << d_this << " : " << lit << std::endl;
      Trace("cegqi-engine") << "******* Sygus : allocate size literal " << s << " for " << d_this << std::endl;
      Node lem = NodeManager::currentNM()->mkNode( kind::OR, lit, lit.negate() );
      Trace("sygus-dec") << "Sygus : Fairness split : " << lem << std::endl;
      lemmas.push_back( lem );
      d->getOutputChannel().requirePhase( lit, true );
    
      d_lits[s] = lit;
      return lit;
    }else{
      return it->second;
    }
  }else{
    return Node::null();
  }
}

Node SygusSymBreakNew::getNextDecisionRequest( unsigned& priority, std::vector< Node >& lemmas ) {
  Trace("sygus-dec-debug") << "SygusSymBreakNew: Get next decision " << std::endl;
  for( std::map< Node, Node >::iterator it = d_anchor_to_active_guard.begin(); it != d_anchor_to_active_guard.end(); ++it ){
    if( getGuardStatus( it->second )==0 ){
      Trace("sygus-dec") << "Sygus : Decide next on active guard : " << it->second << "..." << std::endl;
      priority = 1;
      return it->second;
    }
  }
  for( std::map< Node, SearchSizeInfo * >::iterator it = d_szinfo.begin(); it != d_szinfo.end(); ++it ){
    SearchSizeInfo * s = it->second;
    std::vector< Node > new_lit;
    Node c_lit = s->getCurrentFairnessLiteral( d_td, lemmas );
    Assert( !c_lit.isNull() );
    int gstatus = getGuardStatus( c_lit );
    if( gstatus==-1 ){
      s->incrementCurrentLiteral();
      c_lit = s->getCurrentFairnessLiteral( d_td, lemmas );
      Assert( !c_lit.isNull() );
      Trace("sygus-dec") << "Sygus : Decide on next lit : " << c_lit << "..." << std::endl;
      priority = 1;
      return c_lit;
    }else if( gstatus==0 ){
      Trace("sygus-dec") << "Sygus : Decide on current lit : " << c_lit << "..." << std::endl;
      priority = 1;
      return c_lit;
    }
  }
  return Node::null();
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

