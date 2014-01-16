/*********************                                                        */
/*! \file model_postprocessor.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "smt/model_postprocessor.h"
#include "smt/boolean_terms.h"
#include "expr/node_manager_attributes.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::smt;

Node ModelPostprocessor::rewriteAs(TNode n, TypeNode asType) {
  if(n.getType().isSubtypeOf(asType)) {
    // good to go, we have the right type
    return n;
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
      const Datatype& asDatatype = asType.getConst<Datatype>();
      return NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, (tf ? asDatatype[0] : asDatatype[1]).getConstructor());
    }
  }
  if(n.getType().isRecord() && asType.isRecord()) {
    Debug("boolean-terms") << "+++ got a record - rewriteAs " << n << " : " << asType << endl;
    const Record& rec CVC4_UNUSED = n.getType().getConst<Record>();
    const Record& asRec = asType.getConst<Record>();
    Assert(rec.getNumFields() == asRec.getNumFields());
    Assert(n.getNumChildren() == asRec.getNumFields());
    NodeBuilder<> b(n.getKind());
    b << asType;
    for(size_t i = 0; i < n.getNumChildren(); ++i) {
      b << rewriteAs(n[i], TypeNode::fromType(asRec[i].second));
    }
    Node out = b;
    Debug("boolean-terms") << "+++ returning record " << out << endl;
    return out;
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
  if(current.getType().hasAttribute(expr::DatatypeTupleAttr())) {
    Assert(current.getKind() == kind::APPLY_CONSTRUCTOR);
    TypeNode expectType = current.getType().getAttribute(expr::DatatypeTupleAttr());
    NodeBuilder<> b(kind::TUPLE);
    TypeNode::iterator t = expectType.begin();
    for(TNode::iterator i = current.begin(); i != current.end(); ++i, ++t) {
      Assert(alreadyVisited(*i, TNode::null()));
      Assert(t != expectType.end());
      TNode n = d_nodes[*i];
      n = n.isNull() ? *i : n;
      if(!n.getType().isSubtypeOf(*t)) {
        Assert(n.getType().isBitVector(1u) ||
               (n.getType().isDatatype() && n.getType().hasAttribute(BooleanTermAttr())));
        Assert(n.isConst());
        Assert((*t).isBoolean());
        if(n.getType().isBitVector(1u)) {
          b << NodeManager::currentNM()->mkConst(bool(n.getConst<BitVector>().getValue() == 1));
        } else {
          // we assume (by construction) false is first; see boolean_terms.cpp
          b << NodeManager::currentNM()->mkConst(bool(Datatype::indexOf(n.getOperator().toExpr()) == 1));
        }
      } else {
        b << n;
      }
    }
    Assert(t == expectType.end());
    d_nodes[current] = b;
    Debug("tuprec") << "returning " << d_nodes[current] << endl;
    Assert(d_nodes[current].getType() == expectType);
  } else if(current.getType().hasAttribute(expr::DatatypeRecordAttr())) {
    Assert(current.getKind() == kind::APPLY_CONSTRUCTOR);
    TypeNode expectType = current.getType().getAttribute(expr::DatatypeRecordAttr());
    const Record& expectRec = expectType.getConst<Record>();
    NodeBuilder<> b(kind::RECORD);
    b << current.getType().getAttribute(expr::DatatypeRecordAttr());
    Record::const_iterator t = expectRec.begin();
    for(TNode::iterator i = current.begin(); i != current.end(); ++i, ++t) {
      Assert(alreadyVisited(*i, TNode::null()));
      Assert(t != expectRec.end());
      TNode n = d_nodes[*i];
      n = n.isNull() ? *i : n;
      if(!n.getType().isSubtypeOf(TypeNode::fromType((*t).second))) {
        Assert(n.getType().isBitVector(1u) ||
               (n.getType().isDatatype() && n.getType().hasAttribute(BooleanTermAttr())));
        Assert(n.isConst());
        Assert((*t).second.isBoolean());
        if(n.getType().isBitVector(1u)) {
          b << NodeManager::currentNM()->mkConst(bool(n.getConst<BitVector>().getValue() == 1));
        } else {
          // we assume (by construction) false is first; see boolean_terms.cpp
          b << NodeManager::currentNM()->mkConst(bool(Datatype::indexOf(n.getOperator().toExpr()) == 1));
        }
      } else {
        b << n;
      }
    }
    Assert(t == expectRec.end());
    d_nodes[current] = b;
    Debug("tuprec") << "returning " << d_nodes[current] << endl;
    Assert(d_nodes[current].getType() == expectType);
  } else if(current.getKind() == kind::APPLY_CONSTRUCTOR &&
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
  } else {
    Debug("tuprec") << "returning self for kind " << current.getKind() << endl;
    // rewrite to self
    d_nodes[current] = Node::null();
  }
}/* ModelPostprocessor::visit() */
