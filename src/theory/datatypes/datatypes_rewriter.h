/*********************                                                        */
/*! \file datatypes_rewriter.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: ajreynol
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
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

namespace CVC4 {
namespace theory {
namespace datatypes {

class DatatypesRewriter {

public:

  static RewriteResponse postRewrite(TNode in) {
    Trace("datatypes-rewrite") << "post-rewriting " << in << std::endl;

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
    if(in.getKind() == kind::APPLY_SELECTOR &&
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
        if( options::dtRewriteErrorSel() ){
          Node gt = in.getType().mkGroundTerm();
          TypeNode gtt = gt.getType();
          //Assert( gtt.isDatatype() || gtt.isParametricDatatype() );
          if( !gtt.isInstantiatedDatatype() ){
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
    }

    if(in.getKind() == kind::EQUAL && in[0] == in[1]) {
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(true));
    }
    if(in.getKind() == kind::EQUAL &&
       checkClash(in[0], in[1])) {
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(false));
    }

    return RewriteResponse(REWRITE_DONE, in);
  }

  static RewriteResponse preRewrite(TNode in) {
    Trace("datatypes-rewrite") << "pre-rewriting " << in << std::endl;
    return RewriteResponse(REWRITE_DONE, in);
  }

  static inline void init() {}
  static inline void shutdown() {}

  static bool checkClash( Node n1, Node n2 ) {
    if( n1.getKind() == kind::APPLY_CONSTRUCTOR && n2.getKind() == kind::APPLY_CONSTRUCTOR ) {
      if( n1.getOperator() != n2.getOperator() ) {
        return true;
      } else {
        Assert( n1.getNumChildren() == n2.getNumChildren() );
        for( int i=0; i<(int)n1.getNumChildren(); i++ ) {
          if( checkClash( n1[i], n2[i] ) ) {
            return true;
          }
        }
      }
    }else if( !isTermDatatype( n1 ) ){
      //also check for clashes between non-datatypes
      Node eq = NodeManager::currentNM()->mkNode( n1.getType().isBoolean() ? kind::IFF : kind::EQUAL, n1, n2 );
      eq = Rewriter::rewrite( eq );
      if( eq==NodeManager::currentNM()->mkConst(false) ){
        return true;
      }
    }
    return false;
  }
  /** is this term a datatype */
  static bool isTermDatatype( Node n ){
    TypeNode tn = n.getType();
    return tn.isDatatype() || tn.isParametricDatatype();
  }

};/* class DatatypesRewriter */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__DATATYPES_REWRITER_H */

