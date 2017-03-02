/*********************                                                        */
/*! \file datatypes_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(result));
      } else {
        const Datatype& dt = DatatypeType(in[0].getType().toType()).getDatatype();
        if(dt.getNumConstructors() == 1) {
          // only one constructor, so it must be
          Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                     << "only one ctor for " << dt.getName()
                                     << " and that is " << dt[0].getName()
                                     << std::endl;
          return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
        }
        //TODO : else if( dt.getNumConstructors()==2 && Datatype::indexOf(in.getOperator())==1 ){
        else if( !options::dtUseTesters() ){
          unsigned tindex = Datatype::indexOf(in.getOperator().toExpr());
          Trace("datatypes-rewrite-debug") << "Convert " << in << " to equality " << in[0] << " " << tindex << std::endl;
          Node neq = mkTester( in[0], tindex, dt );
          Assert( neq!=in );
          Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: Rewrite tester " << in << " to " << neq << std::endl;
          return RewriteResponse(REWRITE_AGAIN_FULL, neq);
        }
      }
    }
    if(in.getKind() == kind::APPLY_SELECTOR_TOTAL && in[0].getKind() == kind::APPLY_CONSTRUCTOR) {
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
      if(c.getNumArgs() > selectorIndex && c[selectorIndex].getSelector() == selectorExpr) {
        if( dt.isCodatatype() && in[0][selectorIndex].isConst() ){
          //must replace all debruijn indices with self  
          Node sub = replaceDebruijn( in[0][selectorIndex], in[0], in[0].getType(), 0 );
          Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                     << "Rewrite trivial codatatype selector " << in << " to " << sub << std::endl;
          if( sub!=in ){
            return RewriteResponse(REWRITE_AGAIN_FULL, sub );
          }
        }else{
          Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                   << "Rewrite trivial selector " << in << std::endl;
          return RewriteResponse(REWRITE_DONE, in[0][selectorIndex]);
        }
      }else{
        //typically should not be called
        TypeNode tn = in.getType();
        Node gt;
        bool useTe = true;
        //if( !tn.isSort() ){
        //  useTe = false;
        //}
        if( tn.isDatatype() ){
          const Datatype& dta = ((DatatypeType)(tn).toType()).getDatatype();
          useTe = !dta.isCodatatype();
        }
        if( useTe ){
          TypeEnumerator te(tn);
          gt = *te;
        }else{
          gt = tn.mkGroundTerm();
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

    if(in.getKind() == kind::EQUAL ) {
      if(in[0] == in[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      }else{
        std::vector< Node > rew;
        if( checkClash(in[0], in[1], rew) ){
          Trace("datatypes-rewrite") << "Rewrite clashing equality " << in << " to false" << std::endl;
          return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
        //}else if( rew.size()==1 && rew[0]!=in ){
        //  Trace("datatypes-rewrite") << "Rewrite equality " << in << " to " << rew[0] << std::endl;
        //  return RewriteResponse(REWRITE_AGAIN_FULL, rew[0] );
        }else if( in[1]<in[0] ){
          Node ins = NodeManager::currentNM()->mkNode(in.getKind(), in[1], in[0]);
          Trace("datatypes-rewrite") << "Swap equality " << in << " to " << ins << std::endl;
          return RewriteResponse(REWRITE_DONE, ins);
        }else{
          Trace("datatypes-rewrite-debug") << "Did not rewrite equality " << in << " " << in[0].getKind() << " " << in[1].getKind() << std::endl;
        }
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
    if( n1.getKind() == kind::APPLY_CONSTRUCTOR && n2.getKind() == kind::APPLY_CONSTRUCTOR ) {
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
        Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, n1, n2 );
        rew.push_back( eq );
      }
    }
    return false;
  }
  /** get instantiate cons */
  static Node getInstCons( Node n, const Datatype& dt, int index ) {
    Assert( index>=0 && index<(int)dt.getNumConstructors() );
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
    Assert( isInstCons( n, n_ic, dt )==index );
    //n_ic = Rewriter::rewrite( n_ic );
    return n_ic;
  }

  static int isInstCons( Node t, Node n, const Datatype& dt ){
    if( n.getKind()==kind::APPLY_CONSTRUCTOR ){
      int index = Datatype::indexOf( n.getOperator().toExpr() );
      const DatatypeConstructor& c = dt[index];
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( n[i].getKind()!=kind::APPLY_SELECTOR_TOTAL ||
            n[i].getOperator()!=Node::fromExpr( c[i].getSelector() ) ||
            n[i][0]!=t ){
          return -1;
        }
      }
      return index;
    }
    return -1;
  }

  static int isTester( Node n, Node& a ) {
    if( options::dtUseTesters() ){
      if( n.getKind()==kind::APPLY_TESTER ){
        a = n[0];
        return Datatype::indexOf( n.getOperator().toExpr() );
      }
    }else{
      if( n.getKind()==kind::EQUAL ){
        for( int i=1; i>=0; i-- ){
          if( n[i].getKind()==kind::APPLY_CONSTRUCTOR ){
            const Datatype& dt = Datatype::datatypeOf(n[i].getOperator().toExpr());
            int ic = isInstCons( n[1-i], n[i], dt );
            if( ic!=-1 ){
              a = n[1-i];
              return ic;
            }
          }
        }
      }
    }
    return -1;
  }
  static int isTester( Node n ) {
    if( options::dtUseTesters() ){
      if( n.getKind()==kind::APPLY_TESTER ){
        return Datatype::indexOf( n.getOperator().toExpr() );
      }
    }else{
      if( n.getKind()==kind::EQUAL ){
        for( int i=1; i>=0; i-- ){
          if( n[i].getKind()==kind::APPLY_CONSTRUCTOR ){
            const Datatype& dt = Datatype::datatypeOf(n[i].getOperator().toExpr());
            int ic = isInstCons( n[1-i], n[i], dt );
            if( ic!=-1 ){
              return ic;
            }
          }
        }
      }
    }
    return -1;
  }

  static Node mkTester( Node n, int i, const Datatype& dt ){
    if( options::dtUseTesters() ){
      return NodeManager::currentNM()->mkNode( kind::APPLY_TESTER, Node::fromExpr( dt[i].getTester() ), n );
    }else{
#ifdef CVC4_ASSERTIONS
      Node ret = n.eqNode( DatatypesRewriter::getInstCons( n, dt, i ) );
      Node a;
      int ii = isTester( ret, a );
      Assert( ii==i );
      Assert( a==n );
      return ret;
#else
      return n.eqNode( DatatypesRewriter::getInstCons( n, dt, i ) );
#endif
    }
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
    Trace("dt-nconst-debug") << "normalizeCodatatypeConstantEqc: " << n << " depth=" << depth << std::endl;
    if( eqc.find( n )==eqc.end() ){
      return n;
    }else{
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
  }
  static Node replaceDebruijn( Node n, Node orig, TypeNode orig_tn, unsigned depth ) {
    if( n.getKind()==kind::UNINTERPRETED_CONSTANT && n.getType()==orig_tn ){
      unsigned index = n.getConst<UninterpretedConstant>().getIndex().toUnsignedInt();
      if( index==depth ){
        return orig;
      }
    }else if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node nc = replaceDebruijn( n[i], orig, orig_tn, depth+1 );
        children.push_back( nc );
        childChanged = childChanged || nc!=n[i];
      }
      if( childChanged ){
        if( n.hasOperator() ){
          children.insert( children.begin(), n.getOperator() );
        }
        return NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    return n;
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
      Trace("dt-nconst") << "Computed equivalence classes ids : " << std::endl;
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
