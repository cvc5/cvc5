/*********************                                                        */
/*! \file datatypes_rewriter.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewriter for the theory of inductive datatypes
 **
 ** Rewriter for the theory of inductive datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H
#define __CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H

#include "expr/node_manager_attributes.h"
#include "options/datatypes_options.h"
#include "theory/rewriter.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class DatatypesRewriter {

public:

  static RewriteResponse postRewrite(TNode in) {
    Trace("datatypes-rewrite-debug") << "post-rewriting " << in << std::endl;

    if(in.getKind() == kind::APPLY_CONSTRUCTOR ){
      Type t = in.getType().toType();
      DatatypeType dt = DatatypeType(t);
      //check for parametric datatype constructors
      // to ensure a normal form, all parameteric datatype constructors must have a type ascription
      if( dt.isParametric() ){
        if( in.getOperator().getKind()!=kind::APPLY_TYPE_ASCRIPTION ){
          Trace("datatypes-rewrite-debug") << "Ascribing type to parametric datatype constructor " << in << std::endl;
          Node op = in.getOperator();
          //get the constructor object
          const DatatypeConstructor& dtc = Datatype::datatypeOf(op.toExpr())[Datatype::indexOf(op.toExpr())];
          //create ascribed constructor type
          Node tc = NodeManager::currentNM()->mkConst(AscriptionType(dtc.getSpecializedConstructorType(t)));
          Node op_new = NodeManager::currentNM()->mkNode( kind::APPLY_TYPE_ASCRIPTION, tc, op );
          //make new node
          std::vector< Node > children;
          children.push_back( op_new );
          children.insert( children.end(), in.begin(), in.end() );
          Node inr = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, children );
          Trace("datatypes-rewrite-debug") << "Created " << inr << std::endl;
          return RewriteResponse(REWRITE_DONE, inr);
        }
      }
      if( in.isConst() ){
        Trace("datatypes-rewrite-debug") << "Normalizing constant " << in << std::endl;
        Node inn = normalizeConstant( in );
        //constant may be a subterm of another constant, so cannot assume that this will succeed for codatatypes
        //Assert( !inn.isNull() );
        if( !inn.isNull() && inn!=in ){
          Trace("datatypes-rewrite") << "Normalized constant " << in << " -> " << inn << std::endl;
          return RewriteResponse(REWRITE_DONE, inn);
        }else{
          return RewriteResponse(REWRITE_DONE, in);
        }
      }
    }

    if(in.getKind() == kind::APPLY_TESTER) {
      if(in[0].getKind() == kind::APPLY_CONSTRUCTOR) {
        bool result = Datatype::indexOf(in.getOperator().toExpr()) == Datatype::indexOf(in[0].getOperator().toExpr());
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                   << "Rewrite trivial tester " << in
                                   << " " << result << std::endl;
        return RewriteResponse(REWRITE_DONE,
                               NodeManager::currentNM()->mkConst(result));
      } else {
        const Datatype& dt = DatatypeType(in[0].getType().toType()).getDatatype();
        if(dt.getNumConstructors() == 1) {
          // only one constructor, so it must be
          Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                     << "only one ctor for " << dt.getName()
                                     << " and that is " << dt[0].getName()
                                     << std::endl;
          return RewriteResponse(REWRITE_DONE,
                                 NodeManager::currentNM()->mkConst(true));
        }
      }
    }
    if(in.getKind() == kind::TUPLE_SELECT && in[0].getKind() == kind::APPLY_CONSTRUCTOR) {
      return RewriteResponse(REWRITE_DONE, in[0][in.getOperator().getConst<TupleSelect>().getIndex()]);
    }
    if(in.getKind() == kind::RECORD_SELECT && in[0].getKind() == kind::APPLY_CONSTRUCTOR) {
      const Record& rec = in[0].getType().getAttribute(expr::DatatypeRecordAttr()).getConst<Record>();
      return RewriteResponse(REWRITE_DONE, in[0][rec.getIndex(in.getOperator().getConst<RecordSelect>().getField())]);
    }
    if(in.getKind() == kind::APPLY_SELECTOR_TOTAL &&
       (in[0].getKind() == kind::TUPLE || in[0].getKind() == kind::RECORD)) {
      // These strange (half-tuple-converted) terms can be created by
      // the system if you have something like "foo.1" for a tuple
      // term foo.  The select is rewritten to "select_1(foo)".  If
      // foo gets a value in the model from the TypeEnumerator, you
      // then have a select of a tuple, and we should flatten that
      // here.  Ditto for records, below.
      Expr selectorExpr = in.getOperator().toExpr();
      const Datatype& dt CVC4_UNUSED = Datatype::datatypeOf(selectorExpr);
      TypeNode dtt CVC4_UNUSED = TypeNode::fromType(dt.getDatatypeType());
      size_t selectorIndex = Datatype::indexOf(selectorExpr);
      Debug("tuprec") << "looking at " << in << ", got selector index " << selectorIndex << std::endl;
#ifdef CVC4_ASSERTIONS
      // sanity checks: tuple- and record-converted datatypes should have one constructor
      Assert(NodeManager::currentNM()->getDatatypeForTupleRecord(in[0].getType()) == dtt);
      if(in[0].getKind() == kind::TUPLE) {
        Assert(dtt.hasAttribute(expr::DatatypeTupleAttr()));
        Assert(dtt.getAttribute(expr::DatatypeTupleAttr()) == in[0].getType());
      } else {
        Assert(dtt.hasAttribute(expr::DatatypeRecordAttr()));
        Assert(dtt.getAttribute(expr::DatatypeRecordAttr()) == in[0].getType());
      }
      Assert(dt.getNumConstructors() == 1);
      Assert(dt[0].getNumArgs() > selectorIndex);
      Assert(dt[0][selectorIndex].getSelector() == selectorExpr);
#endif /* CVC4_ASSERTIONS */
      Debug("tuprec") << "==> returning " << in[0][selectorIndex] << std::endl;
      return RewriteResponse(REWRITE_DONE, in[0][selectorIndex]);
    }
    if(in.getKind() == kind::APPLY_SELECTOR_TOTAL &&
       in[0].getKind() == kind::APPLY_CONSTRUCTOR) {
      // Have to be careful not to rewrite well-typed expressions
      // where the selector doesn't match the constructor,
      // e.g. "pred(zero)".
      TNode selector = in.getOperator();
      TNode constructor = in[0].getOperator();
      Expr selectorExpr = selector.toExpr();
      Expr constructorExpr = constructor.toExpr();
      size_t selectorIndex = Datatype::indexOf(selectorExpr);
      size_t constructorIndex = Datatype::indexOf(constructorExpr);
      const Datatype& dt = Datatype::datatypeOf(constructorExpr);
      const DatatypeConstructor& c = dt[constructorIndex];
      if(c.getNumArgs() > selectorIndex &&
         c[selectorIndex].getSelector() == selectorExpr) {
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                   << "Rewrite trivial selector " << in
                                   << std::endl;
        return RewriteResponse(REWRITE_DONE, in[0][selectorIndex]);
      }else{
        //typically should not be called
        TypeNode tn = in.getType();
        Node gt;
        if( tn.isSort() ){
          TypeEnumerator te(tn);
          gt = *te;
        }else{
          //check whether well-founded
          //bool isWf = true;
          //if( isTypeDatatype( tn ) ){
          //  const Datatype& dta = ((DatatypeType)(tn).toType()).getDatatype();
          //  isWf = dta.isWellFounded();
          //}
          //if( isWf || in[0].isConst() ){
          gt = tn.mkGroundTerm();
          //}
        }
        if( !gt.isNull() ){
          //Assert( gtt.isDatatype() || gtt.isParametricDatatype() );
          if( tn.isDatatype() && !tn.isInstantiatedDatatype() ){
            gt = NodeManager::currentNM()->mkNode(kind::APPLY_TYPE_ASCRIPTION,
                                                  NodeManager::currentNM()->mkConst(AscriptionType(tn.toType())), gt);
          }
          Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                     << "Rewrite trivial selector " << in
                                     << " to distinguished ground term "
                                     << gt << std::endl;
          return RewriteResponse(REWRITE_DONE,gt );
        }
      }
    }
    if(in.getKind() == kind::DT_SIZE ){
      if( in[0].getKind()==kind::APPLY_CONSTRUCTOR ){
        std::vector< Node > children;
        for( unsigned i=0; i<in[0].getNumChildren(); i++ ){
          if( in[0][i].getType().isDatatype() ){
            children.push_back( NodeManager::currentNM()->mkNode( kind::DT_SIZE, in[0][i] ) );
          }
        }
        Node res;
        if( !children.empty() ){
          children.push_back( NodeManager::currentNM()->mkConst( Rational(1) ) );
          res = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( kind::PLUS, children );
        }else{
          res = NodeManager::currentNM()->mkConst( Rational(0) );
        }
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: rewrite size " << in << " to " << res << std::endl;
        return RewriteResponse(REWRITE_AGAIN_FULL, res );
      }
    }else if(in.getKind() == kind::DT_HEIGHT_BOUND ){
      if( in[0].getKind()==kind::APPLY_CONSTRUCTOR ){
        std::vector< Node > children;
        Node res;
        Rational r = in[1].getConst<Rational>();
        Rational rmo = Rational( r-Rational(1) );
        for( unsigned i=0; i<in[0].getNumChildren(); i++ ){
          if( in[0][i].getType().isDatatype() ){
            if( r.isZero() ){
              res = NodeManager::currentNM()->mkConst(false);
              break;
            }else{
              children.push_back( NodeManager::currentNM()->mkNode( kind::DT_HEIGHT_BOUND, in[0][i], NodeManager::currentNM()->mkConst(rmo) ) );
            }
          }
        }
        if( res.isNull() ){
          res = children.size()==0 ? NodeManager::currentNM()->mkConst(true) : ( children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( kind::AND, children ) );
        }
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: rewrite height " << in << " to " << res << std::endl;
        return RewriteResponse(REWRITE_AGAIN_FULL, res );
      }
    }
    if(in.getKind() == kind::TUPLE_SELECT &&
       in[0].getKind() == kind::TUPLE) {
      return RewriteResponse(REWRITE_DONE, in[0][in.getOperator().getConst<TupleSelect>().getIndex()]);
    }
    if(in.getKind() == kind::TUPLE_UPDATE &&
       in[0].getKind() == kind::TUPLE) {
      size_t ix = in.getOperator().getConst<TupleUpdate>().getIndex();
      NodeBuilder<> b(kind::TUPLE);
      for(TNode::const_iterator i = in[0].begin(); i != in[0].end(); ++i, --ix) {
        if(ix == 0) {
          b << in[1];
        } else {
          b << *i;
        }
      }
      Node n = b;
      Assert(n.getType().isSubtypeOf(in.getType()));
      return RewriteResponse(REWRITE_DONE, n);
    }
    if(in.getKind() == kind::RECORD_SELECT &&
       in[0].getKind() == kind::RECORD) {
      return RewriteResponse(REWRITE_DONE, in[0][in[0].getOperator().getConst<Record>().getIndex(in.getOperator().getConst<RecordSelect>().getField())]);
    }
    if(in.getKind() == kind::RECORD_UPDATE &&
       in[0].getKind() == kind::RECORD) {
      size_t ix = in[0].getOperator().getConst<Record>().getIndex(in.getOperator().getConst<RecordUpdate>().getField());
      NodeBuilder<> b(kind::RECORD);
      b << in[0].getOperator();
      for(TNode::const_iterator i = in[0].begin(); i != in[0].end(); ++i, --ix) {
        if(ix == 0) {
          b << in[1];
        } else {
          b << *i;
        }
      }
      Node n = b;
      Assert(n.getType().isSubtypeOf(in.getType()));
      return RewriteResponse(REWRITE_DONE, n);
    }

    if(in.getKind() == kind::EQUAL && in[0] == in[1]) {
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(true));
    }
    if(in.getKind() == kind::EQUAL ) {
      std::vector< Node > rew;
      if( checkClash(in[0], in[1], rew) ){
        Trace("datatypes-rewrite") << "Rewrite clashing equality " << in << " to false" << std::endl;
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }else if( rew.size()==1 && rew[0]!=in ){
        Trace("datatypes-rewrite") << "Rewrite equality " << in << " to " << rew[0] << std::endl;
        return RewriteResponse(REWRITE_AGAIN_FULL, rew[0] );
      }else{
        Trace("datatypes-rewrite-debug") << "Did not rewrite equality " << in << " " << in[0].getKind() << " " << in[1].getKind() << std::endl;
      }
    }

    return RewriteResponse(REWRITE_DONE, in);
  }

  static RewriteResponse preRewrite(TNode in) {
    Trace("datatypes-rewrite-debug") << "pre-rewriting " << in << std::endl;
    return RewriteResponse(REWRITE_DONE, in);
  }

  static inline void init() {}
  static inline void shutdown() {}

  static bool checkClash( Node n1, Node n2, std::vector< Node >& rew ) {
    Trace("datatypes-rewrite-debug") << "Check clash : " << n1 << " " << n2 << std::endl;
    if( (n1.getKind() == kind::APPLY_CONSTRUCTOR && n2.getKind() == kind::APPLY_CONSTRUCTOR) ||
        (n1.getKind() == kind::TUPLE && n2.getKind() == kind::TUPLE) ||
        (n1.getKind() == kind::RECORD && n2.getKind() == kind::RECORD) ) {
      //n1.getKind()==kind::APPLY_CONSTRUCTOR
      if( n1.getOperator() != n2.getOperator() ) {
        Trace("datatypes-rewrite-debug") << "Clash operators : " << n1 << " " << n2 << " " << n1.getOperator() << " " << n2.getOperator() << std::endl;
        return true;
      } else {
        Assert( n1.getNumChildren() == n2.getNumChildren() );
        for( int i=0; i<(int)n1.getNumChildren(); i++ ) {
          if( checkClash( n1[i], n2[i], rew ) ) {
            return true;
          }
        }
      }
    }else if( n1!=n2 ){
      if( n1.isConst() && n2.isConst() ){
        Trace("datatypes-rewrite-debug") << "Clash constants : " << n1 << " " << n2 << std::endl;
        return true;
      }else{
        Node eq = NodeManager::currentNM()->mkNode( n1.getType().isBoolean() ? kind::IFF : kind::EQUAL, n1, n2 );
        rew.push_back( eq );
      }
    }
    return false;
  }
  /** get instantiate cons */
  static Node getInstCons( Node n, const Datatype& dt, int index ) {
    Type tspec;
    if( dt.isParametric() ){
      tspec = dt[index].getSpecializedConstructorType(n.getType().toType());
    }
    std::vector< Node > children;
    children.push_back( Node::fromExpr( dt[index].getConstructor() ) );
    for( int i=0; i<(int)dt[index].getNumArgs(); i++ ){
      Node nc = NodeManager::currentNM()->mkNode( kind::APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[index][i].getSelector() ), n );
      children.push_back( nc );
    }
    Node n_ic = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, children );
    //add type ascription for ambiguous constructor types
    if(!n_ic.getType().isComparableTo(n.getType())) {
      Assert( dt.isParametric() );
      Debug("datatypes-parametric") << "DtInstantiate: ambiguous type for " << n_ic << ", ascribe to " << n.getType() << std::endl;
      Debug("datatypes-parametric") << "Constructor is " << dt[index] << std::endl;
      Type tspec = dt[index].getSpecializedConstructorType(n.getType().toType());
      Debug("datatypes-parametric") << "Type specification is " << tspec << std::endl;
      children[0] = NodeManager::currentNM()->mkNode(kind::APPLY_TYPE_ASCRIPTION,
                                                     NodeManager::currentNM()->mkConst(AscriptionType(tspec)), children[0] );
      n_ic = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, children );
      Assert( n_ic.getType()==n.getType() );
    }
    Assert( isInstCons( n_ic, dt, index ) );
    //n_ic = Rewriter::rewrite( n_ic );
    return n_ic;
  }
  static bool isInstCons( Node n, const Datatype& dt, int index ){
    if( n.getKind()==kind::APPLY_CONSTRUCTOR ){
      const DatatypeConstructor& c = dt[index];
      if( n.getOperator()==Node::fromExpr( c.getConstructor() ) ){
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          if( n[i].getKind()!=kind::APPLY_SELECTOR_TOTAL ||
              n[i].getOperator()!=Node::fromExpr( c[i].getSelector() ) ){
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }
  static Node mkTester( Node n, int i, const Datatype& dt ){
    //Node ret = n.eqNode( DatatypesRewriter::getInstCons( n, dt, i ) );
    //Assert( isTester( ret )==i );
    Node ret = NodeManager::currentNM()->mkNode( kind::APPLY_TESTER, Node::fromExpr( dt[i].getTester() ), n );
    return ret;
  }
  static bool isNullaryApplyConstructor( Node n ){
    Assert( n.getKind()==kind::APPLY_CONSTRUCTOR );
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( n[i].getType().isDatatype() ){
        return false;
      }
    }
    return true;
  }
  static bool isNullaryConstructor( const DatatypeConstructor& c ){
    for( unsigned j=0; j<c.getNumArgs(); j++ ){
      if( c[j].getType().getRangeType().isDatatype() ){
        return false;
      }
    }
    return true;
  }

  /** is this term a datatype */
  static bool isTermDatatype( TNode n ){
    TypeNode tn = n.getType();
    return tn.isDatatype() || tn.isParametricDatatype() ||
           tn.isTuple() || tn.isRecord();
  }
  static bool isTypeDatatype( TypeNode tn ){
    return tn.isDatatype() || tn.isParametricDatatype() ||
           tn.isTuple() || tn.isRecord();
  }
private:
  static Node collectRef( Node n, std::vector< Node >& sk, std::map< Node, Node >& rf, std::vector< Node >& rf_pending,
                          std::vector< Node >& terms, std::map< Node, bool >& cdts ){
    Assert( n.isConst() );
    TypeNode tn = n.getType();
    Node ret = n;
    bool isCdt = false;
    if( tn.isDatatype() ){
      if( !tn.isCodatatype() ){
        //nested datatype within codatatype : can be normalized independently since all loops should be self-contained
        ret = normalizeConstant( n );
      }else{
        isCdt = true;
        if( n.getKind()==kind::APPLY_CONSTRUCTOR ){
          sk.push_back( n );
          rf_pending.push_back( Node::null() );
          std::vector< Node > children;
          children.push_back( n.getOperator() );
          bool childChanged = false;
          for( unsigned i=0; i<n.getNumChildren(); i++ ){
            Node nc = collectRef( n[i], sk, rf, rf_pending, terms, cdts );
            if( nc.isNull() ){
              return Node::null();
            }
            childChanged = nc!=n[i] || childChanged;
            children.push_back( nc );
          }
          sk.pop_back();
          if( childChanged ){
            ret = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, children );
            if( !rf_pending.back().isNull() ){
              rf[rf_pending.back()] = ret;
            }
          }else{
            Assert( rf_pending.back().isNull() );
          }
          rf_pending.pop_back();
        }else{
          //a loop
          const Integer& i = n.getConst<UninterpretedConstant>().getIndex();
          uint32_t index = i.toUnsignedInt();
          if( index>=sk.size() ){
            return Node::null();
          }else{
            Assert( sk.size()==rf_pending.size() );
            Node r = rf_pending[ rf_pending.size()-1-index ];
            if( r.isNull() ){
              r = NodeManager::currentNM()->mkBoundVar( sk[ rf_pending.size()-1-index ].getType() );
              rf_pending[ rf_pending.size()-1-index ] = r;
            }
            return r;
          }
        }
      }
    }
    Trace("dt-nconst-debug") << "Return term : " << ret << " from " << n << std::endl;
    if( std::find( terms.begin(), terms.end(), ret )==terms.end() ){
      terms.push_back( ret );
      Assert( ret.getType()==tn );
      cdts[ret] = isCdt;
    }
    return ret;
  }
  //eqc_stack stores depth
  static Node normalizeCodatatypeConstantEqc( Node n, std::map< int, int >& eqc_stack, std::map< Node, int >& eqc, int depth ){
    Assert( eqc.find( n )!=eqc.end() );
    int e = eqc[n];
    std::map< int, int >::iterator it = eqc_stack.find( e );
    if( it!=eqc_stack.end() ){
      int debruijn = depth - it->second - 1;
      return NodeManager::currentNM()->mkConst(UninterpretedConstant(n.getType().toType(), debruijn));
    }else{
      std::vector< Node > children;
      bool childChanged = false;
      eqc_stack[e] = depth;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node nc = normalizeCodatatypeConstantEqc( n[i], eqc_stack, eqc, depth+1 );
        children.push_back( nc );
        childChanged = childChanged || nc!=n[i];
      }
      eqc_stack.erase(e);
      if( childChanged ){
        Assert( n.getKind()==kind::APPLY_CONSTRUCTOR );
        children.insert( children.begin(), n.getOperator() );
        return NodeManager::currentNM()->mkNode( n.getKind(), children );
      }else{
        return n;
      }
    }
  }
public:
  static Node normalizeCodatatypeConstant( Node n ){
    Trace("dt-nconst") << "Normalize " << n << std::endl;
    std::map< Node, Node > rf;
    std::vector< Node > sk;
    std::vector< Node > rf_pending;
    std::vector< Node > terms;
    std::map< Node, bool > cdts;
    Node s = collectRef( n, sk, rf, rf_pending, terms, cdts );
    if( !s.isNull() ){
      Trace("dt-nconst") << "...symbolic normalized is : " << s << std::endl;
      for( std::map< Node, Node >::iterator it = rf.begin(); it != rf.end(); ++it ){
        Trace("dt-nconst") << "  " << it->first << " = " << it->second << std::endl;
      }
      //now run DFA minimization on term structure
      Trace("dt-nconst") << "  " << terms.size() << " total subterms :" << std::endl;
      int eqc_count = 0;
      std::map< Node, int > eqc_op_map;
      std::map< Node, int > eqc;
      std::map< int, std::vector< Node > > eqc_nodes;
      //partition based on top symbol
      for( unsigned j=0; j<terms.size(); j++ ){
        Node t = terms[j];
        Trace("dt-nconst") << "    " << t << ", cdt=" << cdts[t] << std::endl;
        int e;
        if( cdts[t] ){
          Assert( t.getKind()==kind::APPLY_CONSTRUCTOR );
          Node op = t.getOperator();
          std::map< Node, int >::iterator it = eqc_op_map.find( op );
          if( it==eqc_op_map.end() ){
            e = eqc_count;
            eqc_op_map[op] = eqc_count;
            eqc_count++;
          }else{
            e = it->second;
          }
        }else{
          e = eqc_count;
          eqc_count++;
        }
        eqc[t] = e;
        eqc_nodes[e].push_back( t );
      }
      //partition until fixed point
      int eqc_curr = 0;
      bool success = true;
      while( success ){
        success = false;
        int eqc_end = eqc_count;
        while( eqc_curr<eqc_end ){
          if( eqc_nodes[eqc_curr].size()>1 ){
            //look at all nodes in this equivalence class
            unsigned nchildren = eqc_nodes[eqc_curr][0].getNumChildren();
            std::map< int, std::vector< Node > > prt;
            for( unsigned j=0; j<nchildren; j++ ){
              prt.clear();
              //partition based on children : for the first child that causes a split, break
              for( unsigned k=0; k<eqc_nodes[eqc_curr].size(); k++ ){
                Node t = eqc_nodes[eqc_curr][k];
                Assert( t.getNumChildren()==nchildren );
                Node tc = t[j];
                //refer to loops
                std::map< Node, Node >::iterator itr = rf.find( tc );
                if( itr!=rf.end() ){
                  tc = itr->second;
                }
                Assert( eqc.find( tc)!=eqc.end() );
                prt[eqc[tc]].push_back( t );
              }
              if( prt.size()>1 ){
                success = true;
                break;
              }
            }
            //move into new eqc(s)
            for( std::map< int, std::vector< Node > >::iterator it = prt.begin(); it != prt.end(); ++it ){
              int e = eqc_count;
              for( unsigned j=0; j<it->second.size(); j++ ){
                Node t = it->second[j];
                eqc[t] = e;
                eqc_nodes[e].push_back( t );
              }
              eqc_count++;
            }
          }
          eqc_nodes.erase( eqc_curr );
          eqc_curr++;
        }
      }
      //add in already occurring loop variables
      for( std::map< Node, Node >::iterator it = rf.begin(); it != rf.end(); ++it ){
        Trace("dt-nconst-debug") << "Mapping equivalence class of " << it->first << " -> " << it->second << std::endl;
        Assert( eqc.find(it->second)!=eqc.end() );
        eqc[it->first] = eqc[it->second];
      }
      //we now have a partition of equivalent terms
      Trace("dt-nconst") << "Equivalence classes ids : " << std::endl;
      for( std::map< Node, int >::iterator it = eqc.begin(); it != eqc.end(); ++it ){
        Trace("dt-nconst") << "  " << it->first << " -> " << it->second << std::endl;
      }
      //traverse top-down based on equivalence class
      std::map< int, int > eqc_stack;
      return normalizeCodatatypeConstantEqc( s, eqc_stack, eqc, 0 );
    }else{
      Trace("dt-nconst") << "...invalid." << std::endl;
      return Node::null();
    }
  }
  //normalize constant : apply to top-level codatatype constants
  static Node normalizeConstant( Node n ){
    TypeNode tn = n.getType();
    if( tn.isDatatype() ){
      if( tn.isCodatatype() ){
        return normalizeCodatatypeConstant( n );
      }else{
        std::vector< Node > children;
        bool childrenChanged = false;
        for( unsigned i = 0; i<n.getNumChildren(); i++ ){
          Node nc = normalizeConstant( n[i] );
          children.push_back( nc );
          childrenChanged = childrenChanged || nc!=n[i];
        }
        if( childrenChanged ){
          return NodeManager::currentNM()->mkNode( n.getKind(), children );
        }else{
          return n;
        }
      }
    }else{
      return n;
    }
  }
};/* class DatatypesRewriter */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H */
