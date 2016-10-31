/*********************                                                        */
/*! \file model_postprocessor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "smt/model_postprocessor.h"

#include "expr/node_manager_attributes.h"
#include "expr/record.h"
#include "smt/boolean_terms.h"

using namespace std;

namespace CVC4 {
namespace smt {

Node ModelPostprocessor::rewriteAs(TNode n, TypeNode asType) {
  if(n.getType().isSubtypeOf(asType)) {
    // good to go, we have the right type
    return n;
  }
  if(n.getKind() == kind::LAMBDA) {
    Assert(asType.isFunction());
    Node rhs = rewriteAs(n[1], asType[1]);
    Node out = NodeManager::currentNM()->mkNode(kind::LAMBDA, n[0], rhs);
    Debug("boolean-terms") << "rewrote " << n << " as " << out << std::endl;
    Debug("boolean-terms") << "need type " << asType << endl;
    // Assert(out.getType() == asType);
    return out;
  }
  if(!n.isConst()) {
    // we don't handle non-const right now
    return n;
  }
  if(asType.isBoolean()) {
    if(n.getType().isBitVector(1u)) {
      // type mismatch: should only happen for Boolean-term conversion under
      // datatype constructor applications; rewrite from BV(1) back to Boolean
      bool tf = (n.getConst<BitVector>().getValue() == 1);
      return NodeManager::currentNM()->mkConst(tf);
    }
    if(n.getType().isDatatype() && n.getType().hasAttribute(BooleanTermAttr())) {
      // type mismatch: should only happen for Boolean-term conversion under
      // datatype constructor applications; rewrite from datatype back to Boolean
      Assert(n.getKind() == kind::APPLY_CONSTRUCTOR);
      Assert(n.getNumChildren() == 0);
      // we assume (by construction) false is first; see boolean_terms.cpp
      bool tf = (Datatype::indexOf(n.getOperator().toExpr()) == 1);
      Debug("boolean-terms") << "+++ rewriteAs " << n << " : " << asType << " ==> " << tf << endl;
      return NodeManager::currentNM()->mkConst(tf);
    }
  }
  if(n.getType().isBoolean()) {
    bool tf = n.getConst<bool>();
    if(asType.isBitVector(1u)) {
      return NodeManager::currentNM()->mkConst(BitVector(1u, tf ? 1u : 0u));
    }
    if(asType.isDatatype() && asType.hasAttribute(BooleanTermAttr())) {
      const Datatype& asDatatype = asType.getDatatype();
      return NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, (tf ? asDatatype[0] : asDatatype[1]).getConstructor());
    }
  }
  Debug("boolean-terms") << "+++ rewriteAs " << n << " : " << asType << endl;
  if(n.getType().isArray()) {
    Assert(asType.isArray());
    if(n.getKind() == kind::STORE) {
      return NodeManager::currentNM()->mkNode(kind::STORE,
                                              rewriteAs(n[0], asType),
                                              rewriteAs(n[1], asType[0]),
                                              rewriteAs(n[2], asType[1]));
    }
    Assert(n.getKind() == kind::STORE_ALL);
    const ArrayStoreAll& asa = n.getConst<ArrayStoreAll>();
    Node val = rewriteAs(asa.getExpr(), asType[1]);
    return NodeManager::currentNM()->mkConst(ArrayStoreAll(asType.toType(), val.toExpr()));
  }
  if( n.getType().isSet() ){
    if( n.getKind()==kind::UNION ){
      std::vector< Node > children;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        children.push_back( rewriteAs( n[i], asType ) );
      }
      return NodeManager::currentNM()->mkNode(kind::UNION,children);
    }
  }
  if(n.getType().isParametricDatatype() &&
     n.getType().isInstantiatedDatatype() &&
     asType.isParametricDatatype() &&
     asType.isInstantiatedDatatype() &&
     n.getType()[0] == asType[0]) {
    // Here, we're doing something like rewriting a (Pair BV1 BV1) as a
    // (Pair Bool Bool).
    const Datatype* dt2 = &asType[0].getDatatype();
    std::vector<TypeNode> fromParams, toParams;
    for(unsigned i = 0; i < dt2->getNumParameters(); ++i) {
      fromParams.push_back(TypeNode::fromType(dt2->getParameter(i)));
      toParams.push_back(asType[i + 1]);
    }
    Assert(dt2 == &Datatype::datatypeOf(n.getOperator().toExpr()));
    size_t ctor_ix = Datatype::indexOf(n.getOperator().toExpr());
    NodeBuilder<> appctorb(kind::APPLY_CONSTRUCTOR);
    appctorb << (*dt2)[ctor_ix].getConstructor();
    for(size_t j = 0; j < n.getNumChildren(); ++j) {
      TypeNode asType = TypeNode::fromType(SelectorType((*dt2)[ctor_ix][j].getSelector().getType()).getRangeType());
      asType = asType.substitute(fromParams.begin(), fromParams.end(), toParams.begin(), toParams.end());
      appctorb << rewriteAs(n[j], asType);
    }
    Node out = appctorb;
    return out;
  }
  if(asType.getNumChildren() != n.getNumChildren() ||
     n.getMetaKind() == kind::metakind::CONSTANT) {
    return n;
  }
  NodeBuilder<> b(n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
    b << n.getOperator();
  }
  TypeNode::iterator t = asType.begin();
  for(TNode::iterator i = n.begin(); i != n.end(); ++i, ++t) {
    Assert(t != asType.end());
    b << rewriteAs(*i, *t);
  }
  Assert(t == asType.end());
  Debug("boolean-terms") << "+++ constructing " << b << endl;
  Node out = b;
  return out;
}

void ModelPostprocessor::visit(TNode current, TNode parent) {
  Debug("tuprec") << "visiting " << current << endl;
  Assert(!alreadyVisited(current, TNode::null()));
  bool rewriteChildren = false;
  if(current.getKind() == kind::APPLY_CONSTRUCTOR &&
            ( current.getOperator().hasAttribute(BooleanTermAttr()) ||
              ( current.getOperator().getKind() == kind::APPLY_TYPE_ASCRIPTION &&
                current.getOperator()[0].hasAttribute(BooleanTermAttr()) ) )) {
    NodeBuilder<> b(kind::APPLY_CONSTRUCTOR);
    Node realOp;
    if(current.getOperator().getKind() == kind::APPLY_TYPE_ASCRIPTION) {
      TNode oldAsc = current.getOperator().getOperator();
      Debug("boolean-terms") << "old asc: " << oldAsc << endl;
      Node newCons = current.getOperator()[0].getAttribute(BooleanTermAttr());
      Node newAsc = NodeManager::currentNM()->mkConst(AscriptionType(newCons.getType().toType()));
      Debug("boolean-terms") << "new asc: " << newAsc << endl;
      if(newCons.getType().getRangeType().isParametricDatatype()) {
        vector<TypeNode> oldParams = TypeNode::fromType(oldAsc.getConst<AscriptionType>().getType()).getRangeType().getParamTypes();
        vector<TypeNode> newParams = newCons.getType().getRangeType().getParamTypes();
        Assert(oldParams.size() == newParams.size() && oldParams.size() > 0);
        newAsc = NodeManager::currentNM()->mkConst(AscriptionType(newCons.getType().substitute(newParams.begin(), newParams.end(), oldParams.begin(), oldParams.end()).toType()));
      }
      realOp = NodeManager::currentNM()->mkNode(kind::APPLY_TYPE_ASCRIPTION, newAsc, newCons);
    } else {
      realOp = current.getOperator().getAttribute(BooleanTermAttr());
    }
    b << realOp;
    Debug("boolean-terms") << "+ op " << b.getOperator() << endl;
    TypeNode::iterator j = realOp.getType().begin();
    for(TNode::iterator i = current.begin(); i != current.end(); ++i, ++j) {
      Assert(j != realOp.getType().end());
      Assert(alreadyVisited(*i, TNode::null()));
      TNode repl = d_nodes[*i];
      repl = repl.isNull() ? *i : repl;
      Debug("boolean-terms") << "+ adding " << repl << " expecting " << *j << endl;
      b << rewriteAs(repl, *j);
    }
    Node n = b;
    Debug("boolean-terms") << "model-post: " << current << endl
                           << "- returning " << n << endl;
    d_nodes[current] = n;
    return;
  //all kinds with children that can occur in nodes in a model go here
  } else if(current.getKind() == kind::LAMBDA || current.getKind() == kind::SINGLETON || current.getKind() == kind::UNION || 
            current.getKind()==kind::STORE || current.getKind()==kind::STORE_ALL || current.getKind()==kind::APPLY_CONSTRUCTOR ) {
    rewriteChildren = true;
  }
  if( rewriteChildren ){
    // rewrite based on children
    bool self = true;
    for(size_t i = 0; i < current.getNumChildren(); ++i) {
      Assert(d_nodes.find(current[i]) != d_nodes.end());
      if(!d_nodes[current[i]].isNull()) {
        self = false;
        break;
      }
    }
    if(self) {
      Debug("tuprec") << "returning self for kind " << current.getKind() << endl;
      // rewrite to self
      d_nodes[current] = Node::null();
    } else {
      // rewrite based on children
      NodeBuilder<> nb(current.getKind());
      if(current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        TNode op = current.getOperator();
        Node realOp;
        if(op.getAttribute(BooleanTermAttr(), realOp)) {
          nb << realOp;
        } else {
          nb << op;
        }
      }
      for(size_t i = 0; i < current.getNumChildren(); ++i) {
        Assert(d_nodes.find(current[i]) != d_nodes.end());
        TNode rw = d_nodes[current[i]];
        if(rw.isNull()) {
          rw = current[i];
        }
        nb << rw;
      }
      d_nodes[current] = nb;
      Debug("tuprec") << "rewrote children for kind " << current.getKind() << " got " << d_nodes[current] << ", operator = " << d_nodes[current].getOperator() << endl;
    }
  } else {
    Debug("tuprec") << "returning self for kind " << current.getKind() << endl;
    // rewrite to self
    d_nodes[current] = Node::null();
  }
}/* ModelPostprocessor::visit() */

} /* namespace smt */
} /* namespace CVC4 */
