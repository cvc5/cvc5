/*********************                                                        */
/*! \file pickler.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Kshitij Bansal, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is a "pickler" for expressions
 **
 ** This is a "pickler" for expressions.  It produces a binary
 ** serialization of an expression that can be converted back
 ** into an expression in the same or another ExprManager.
 **/

#include <iostream>
#include <sstream>
#include <string>

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "expr/pickler.h"
#include "expr/pickle_data.h"
#include "expr/expr.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/node_value.h"
#include "expr/expr_manager_scope.h"
#include "expr/variable_type_map.h"
#include "expr/kind.h"
#include "expr/metakind.h"

namespace CVC4 {
namespace expr {
namespace pickle {

class PicklerPrivate {
public:
  typedef std::stack<Node> NodeStack;
  NodeStack d_stack;

  PickleData d_current;

  Pickler& d_pickler;

  NodeManager* const d_nm;

  PicklerPrivate(Pickler& pickler, ExprManager* em) :
    d_pickler(pickler),
    d_nm(NodeManager::fromExprManager(em)) {
  }

  bool atDefaultState(){
    return d_stack.empty() && d_current.empty();
  }

  /* Helper functions for toPickle */
  void toCaseNode(TNode n);
  void toCaseVariable(TNode n);
  void toCaseConstant(TNode n);
  void toCaseOperator(TNode n);
  void toCaseString(Kind k, const std::string& s);

  /* Helper functions for toPickle */
  Node fromCaseOperator(Kind k, uint32_t nchildren);
  Node fromCaseConstant(Kind k, uint32_t nblocks);
  std::string fromCaseString(uint32_t nblocks);
  Node fromCaseVariable(Kind k);

};/* class PicklerPrivate */

static Block mkBlockBody4Chars(char a, char b, char c, char d) {
  Block newBody;
  newBody.d_body.d_data = (a << 24) | (b << 16) | (c << 8) | d;
  return newBody;
}

static char getCharBlockBody(BlockBody body, int i) {
  Assert(0 <= i && i <= 3);

  switch(i) {
  case 0: return (body.d_data & 0xff000000) >> 24;
  case 1: return (body.d_data & 0x00ff0000) >> 16;
  case 2: return (body.d_data & 0x0000ff00) >> 8;
  case 3: return (body.d_data & 0x000000ff);
  default:
    Unreachable();
  }
  return '\0';
}

static Block mkBlockBody(unsigned data) {
  Block newBody;
  newBody.d_body.d_data = data;
  return newBody;
}

static Block mkOperatorHeader(Kind k, unsigned numChildren) {
  Block newHeader;
  newHeader.d_headerOperator.d_kind = k;
  newHeader.d_headerOperator.d_nchildren = numChildren;
  return newHeader;
}

static Block mkVariableHeader(Kind k) {
  Block newHeader;
  newHeader.d_header.d_kind = k;
  return newHeader;
}

static Block mkConstantHeader(Kind k, unsigned numBlocks) {
  Block newHeader;
  newHeader.d_headerConstant.d_kind = k;
  newHeader.d_headerConstant.d_constblocks = numBlocks;
  return newHeader;
}

Pickler::Pickler(ExprManager* em) :
  d_private(new PicklerPrivate(*this, em)) {
}

Pickler::~Pickler() {
  delete d_private;
}

void Pickler::toPickle(Expr e, Pickle& p)
{
  Assert(NodeManager::fromExprManager(e.getExprManager()) == d_private->d_nm);
  Assert(d_private->atDefaultState());

  try{
    d_private->d_current.swap(*p.d_data);
    d_private->toCaseNode(e.getTNode());
    d_private->d_current.swap(*p.d_data);
  }catch(PicklingException& pe){
    d_private->d_current = PickleData();
    Assert(d_private->atDefaultState());
    throw pe;
  }

  Assert(d_private->atDefaultState());
}

void PicklerPrivate::toCaseNode(TNode n)
{
  Debug("pickler") << "toCaseNode: " << n << std::endl;
  Kind k = n.getKind();
  kind::MetaKind m = metaKindOf(k);
  switch(m) {
  case kind::metakind::CONSTANT:
    toCaseConstant(n);
    break;
  case kind::metakind::VARIABLE:
    toCaseVariable(n);
    break;
  case kind::metakind::OPERATOR:
  case kind::metakind::PARAMETERIZED:
    toCaseOperator(n);
    break;
  default:
    Unhandled(m);
  }
}

void PicklerPrivate::toCaseOperator(TNode n)
{
  Kind k = n.getKind();
  kind::MetaKind m = metaKindOf(k);
  Assert(m == kind::metakind::PARAMETERIZED || m == kind::metakind::OPERATOR);
  if(m == kind::metakind::PARAMETERIZED) {
    toCaseNode(n.getOperator());
  }
  for(TNode::iterator i = n.begin(), i_end = n.end(); i != i_end; ++i) {
    toCaseNode(*i);
  }
  d_current << mkOperatorHeader(k, n.getNumChildren());
}

void PicklerPrivate::toCaseVariable(TNode n)
{
  Kind k = n.getKind();
  Assert(metaKindOf(k) == kind::metakind::VARIABLE);

  const NodeValue* nv = n.d_nv;
  uint64_t asInt = reinterpret_cast<uint64_t>(nv);
  uint64_t mapped = d_pickler.variableToMap(asInt);

  uint32_t firstHalf = mapped >> 32;
  uint32_t secondHalf = mapped & 0xffffffff;

  d_current << mkVariableHeader(k);
  d_current << mkBlockBody(firstHalf);
  d_current << mkBlockBody(secondHalf);
}


void PicklerPrivate::toCaseConstant(TNode n) {
  Kind k = n.getKind();
  Assert(metaKindOf(k) == kind::metakind::CONSTANT);
  switch(k) {
  case kind::CONST_BOOLEAN:
    d_current << mkConstantHeader(k, 1);
    d_current << mkBlockBody(n.getConst<bool>());
    break;
  case kind::CONST_RATIONAL: {
    std::string asString;
    Assert(k == kind::CONST_RATIONAL);
    const Rational& q = n.getConst<Rational>();
    asString = q.toString(16);
    toCaseString(k, asString);
    break;
  }
  case kind::BITVECTOR_EXTRACT_OP: {
    BitVectorExtract bve = n.getConst<BitVectorExtract>();
    d_current << mkConstantHeader(k, 2);
    d_current << mkBlockBody(bve.high);
    d_current << mkBlockBody(bve.low);
    break;
  }
  case kind::CONST_BITVECTOR: {
    // irritating: we incorporate the size of the string in with the
    // size of this constant, so it appears as one big constant and
    // doesn't confuse anybody
    BitVector bv = n.getConst<BitVector>();
    std::string asString = bv.getValue().toString(16);
    d_current << mkConstantHeader(k, 2 + asString.size());
    d_current << mkBlockBody(bv.getSize());
    toCaseString(k, asString);
    break;
  }
  case  kind::BITVECTOR_SIGN_EXTEND_OP: {
    BitVectorSignExtend bvse = n.getConst<BitVectorSignExtend>();
    d_current << mkConstantHeader(k, 1);
    d_current << mkBlockBody(bvse.signExtendAmount);
    break;
  }
  default:
    Unhandled(k);
  }
}

void PicklerPrivate::toCaseString(Kind k, const std::string& s) {
  d_current << mkConstantHeader(k, s.size());

  unsigned size = s.size();
  unsigned i;
  for(i = 0; i + 4 <= size; i += 4) {
    d_current << mkBlockBody4Chars(s[i + 0], s[i + 1],s[i + 2], s[i + 3]);
  }
  switch(size % 4) {
  case 0: break;
  case 1: d_current << mkBlockBody4Chars(s[i + 0], '\0','\0', '\0'); break;
  case 2: d_current << mkBlockBody4Chars(s[i + 0], s[i + 1], '\0', '\0'); break;
  case 3: d_current << mkBlockBody4Chars(s[i + 0], s[i + 1],s[i + 2], '\0'); break;
  default:
    Unreachable();
  }

}

void Pickler::debugPickleTest(Expr e) {

  //ExprManager *em = e.getExprManager();
  //Expr e1 = mkVar("x", makeType());
  //return ;

  Pickler pickler(e.getExprManager());

  Pickle p;
  pickler.toPickle(e, p);

  uint32_t size = p.d_data->size();
  std::string str = p.d_data->toString();

  Expr from = pickler.fromPickle(p);
  ExprManagerScope ems(e);

  Debug("pickle") << "before: " << e << std::endl;
  Debug("pickle") << "after: " << from.getNode() << std::endl;
  Debug("pickle") << "pickle: (oct) "<< size << " " << str.length() << " " << str << std::endl;

  Assert(p.d_data->empty());
  Assert(e == from);
}

Expr Pickler::fromPickle(Pickle& p) {
  Assert(d_private->atDefaultState());

  d_private->d_current.swap(*p.d_data);

  while(!d_private->d_current.empty()) {
    Block front = d_private->d_current.dequeue();

    Kind k = (Kind)front.d_header.d_kind;
    kind::MetaKind m = metaKindOf(k);

    Node result = Node::null();
    switch(m) {
    case kind::metakind::VARIABLE:
      result = d_private->fromCaseVariable(k);
      break;
    case kind::metakind::CONSTANT:
      result = d_private->fromCaseConstant(k, front.d_headerConstant.d_constblocks);
      break;
    case kind::metakind::OPERATOR:
    case kind::metakind::PARAMETERIZED:
      result = d_private->fromCaseOperator(k, front.d_headerOperator.d_nchildren);
      break;
    default:
      Unhandled(m);
    }
    Assert(result != Node::null());
    d_private->d_stack.push(result);
  }

  Assert(d_private->d_current.empty());
  Assert(d_private->d_stack.size() == 1);
  Node res = d_private->d_stack.top();
  d_private->d_stack.pop();

  Assert(d_private->atDefaultState());

  return d_private->d_nm->toExpr(res);
}

Node PicklerPrivate::fromCaseVariable(Kind k) {
  Assert(metaKindOf(k) == kind::metakind::VARIABLE);

  Block firstHalf = d_current.dequeue();
  Block secondHalf = d_current.dequeue();

  uint64_t asInt = firstHalf.d_body.d_data;
  asInt = asInt << 32;
  asInt = asInt | (secondHalf.d_body.d_data);

  uint64_t mapped = d_pickler.variableFromMap(asInt);

  NodeValue* nv = reinterpret_cast<NodeValue*>(mapped);
  Node fromNodeValue(nv);

  Assert(fromNodeValue.getKind() == k);

  return fromNodeValue;
}

Node PicklerPrivate::fromCaseConstant(Kind k, uint32_t constblocks) {
  switch(k) {
  case kind::CONST_BOOLEAN: {
    Assert(constblocks == 1);
    Block val = d_current.dequeue();

    bool b= val.d_body.d_data;
    return d_nm->mkConst<bool>(b);
  }
  case kind::CONST_RATIONAL: {
    std::string s = fromCaseString(constblocks);
    Rational q(s, 16);
    return d_nm->mkConst<Rational>(q);
  }
  case kind::BITVECTOR_EXTRACT_OP: {
    Block high = d_current.dequeue();
    Block low = d_current.dequeue();
    BitVectorExtract bve(high.d_body.d_data, low.d_body.d_data);
    return d_nm->mkConst<BitVectorExtract>(bve);
  }
  case kind::CONST_BITVECTOR: {
    unsigned size = d_current.dequeue().d_body.d_data;
    Block header CVC4_UNUSED = d_current.dequeue();
    Assert(header.d_headerConstant.d_kind == kind::CONST_BITVECTOR);
    Assert(header.d_headerConstant.d_constblocks == constblocks - 2);
    Integer value(fromCaseString(constblocks - 2));
    BitVector bv(size, value);
    return d_nm->mkConst(bv);
  }
  case  kind::BITVECTOR_SIGN_EXTEND_OP: {
    Block signExtendAmount = d_current.dequeue();
    BitVectorSignExtend bvse(signExtendAmount.d_body.d_data);
    return d_nm->mkConst<BitVectorSignExtend>(bvse);
  }
  default:
    Unhandled(k);
  }
}

std::string PicklerPrivate::fromCaseString(uint32_t size) {
  std::stringstream ss;
  unsigned i;
  for(i = 0; i + 4 <= size; i += 4) {
    Block front = d_current.dequeue();
    BlockBody body = front.d_body;

    ss << getCharBlockBody(body,0)
       << getCharBlockBody(body,1)
       << getCharBlockBody(body,2)
       << getCharBlockBody(body,3);
  }
  Assert(i == size - (size%4) );
  if(size % 4 != 0) {
    Block front = d_current.dequeue();
    BlockBody body = front.d_body;
    switch(size % 4) {
    case 1:
      ss << getCharBlockBody(body,0);
      break;
    case 2:
      ss << getCharBlockBody(body,0)
         << getCharBlockBody(body,1);
      break;
    case 3:
      ss << getCharBlockBody(body,0)
         << getCharBlockBody(body,1)
         << getCharBlockBody(body,2);
      break;
    default:
      Unreachable();
    }
  }
  return ss.str();
}

Node PicklerPrivate::fromCaseOperator(Kind k, uint32_t nchildren) {
  kind::MetaKind m = metaKindOf(k);
  bool parameterized = (m == kind::metakind::PARAMETERIZED);
  uint32_t npops = nchildren + (parameterized? 1 : 0);

  NodeStack aux;
  while(npops > 0) {
    Assert(!d_stack.empty());
    Node top = d_stack.top();
    aux.push(top);
    d_stack.pop();
    --npops;
  }

  NodeBuilder<> nb(d_nm, k);
  while(!aux.empty()) {
    Node top = aux.top();
    nb << top;
    aux.pop();
  }

  return nb;
}

Pickle::Pickle() {
  d_data = new PickleData();
}

// Just copying the pointer isn't right, we have to copy the
// underlying data.  Otherwise user-level Pickles will delete the data
// twice! (once in each thread)
Pickle::Pickle(const Pickle& p) {
  d_data = new PickleData(*p.d_data);
}

Pickle& Pickle::operator = (const Pickle& other) {
  if (this != &other) {
    delete d_data;
    d_data = new PickleData(*other.d_data);
  }
  return *this;
}


Pickle::~Pickle() {
  delete d_data;
}

uint64_t MapPickler::variableFromMap(uint64_t x) const 
{
  VarMap::const_iterator i = d_fromMap.find(x);
  Assert(i != d_fromMap.end());
  return i->second;
}

}/* CVC4::expr::pickle namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */
