/*********************                                                        */
/*! \file datatypes_rewriter.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

#include "theory/rewriter.h"
#include "theory/datatypes/options.h"
#include "theory/type_enumerator.h"
#include "expr/node_manager_attributes.h"

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
        Node gt;
        if( in.getType().isSort() ){
          TypeEnumerator te(in.getType());
          gt = *te;
        }else{
          gt = in.getType().mkGroundTerm();
        }
        TypeNode gtt = gt.getType();
        //Assert( gtt.isDatatype() || gtt.isParametricDatatype() );
        if( gtt.isDatatype() && !gtt.isInstantiatedDatatype() ){
          gt = NodeManager::currentNM()->mkNode(kind::APPLY_TYPE_ASCRIPTION,
                                                NodeManager::currentNM()->mkConst(AscriptionType(in.getType().toType())), gt);
        }
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                   << "Rewrite trivial selector " << in
                                   << " to distinguished ground term "
                                   << in.getType().mkGroundTerm() << std::endl;
        return RewriteResponse(REWRITE_DONE,gt );
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
    if( (n1.getKind() == kind::APPLY_CONSTRUCTOR && n2.getKind() == kind::APPLY_CONSTRUCTOR) ||
        (n1.getKind() == kind::TUPLE && n2.getKind() == kind::TUPLE) ||
        (n1.getKind() == kind::RECORD && n2.getKind() == kind::RECORD) ) {
      if( n1.getOperator() != n2.getOperator() ) {
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
        return true;        
      }else{
        Node eq = NodeManager::currentNM()->mkNode( n1.getType().isBoolean() ? kind::IFF : kind::EQUAL, n1, n2 );
        rew.push_back( eq );
      }
    }
    return false;
  }
  /** get instantiate cons */
  static Node getInstCons( Node n, const Datatype& dt, int index, bool mkVar = false ) {
    Type tspec;
    if( dt.isParametric() ){
      tspec = dt[index].getSpecializedConstructorType(n.getType().toType());
    }
    std::vector< Node > children;
    children.push_back( Node::fromExpr( dt[index].getConstructor() ) );
    for( int i=0; i<(int)dt[index].getNumArgs(); i++ ){
      Node nc = NodeManager::currentNM()->mkNode( kind::APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[index][i].getSelector() ), n );
      if( mkVar ){
        TypeNode tn = nc.getType();
        if( dt.isParametric() ){
          tn = TypeNode::fromType( tspec )[i];
        }
        nc = NodeManager::currentNM()->mkSkolem( "m", tn, "created for inst cons" );
      }
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

};/* class DatatypesRewriter */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H */

