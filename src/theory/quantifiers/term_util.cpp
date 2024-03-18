/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of term utilities class.
 */

#include "theory/quantifiers/term_util.h"

#include "expr/array_store_all.h"
#include "expr/function_array_const.h"
#include "expr/node_algorithm.h"
#include "expr/sequence.h"
#include "expr/skolem_manager.h"
#include "theory/arith/arith_msum.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/rewriter.h"
#include "theory/strings/word.h"
#include "util/bitvector.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

size_t TermUtil::getVariableNum(Node q, Node v)
{
  Node::iterator it = std::find(q[0].begin(), q[0].end(), v);
  Assert(it != q[0].end());
  return it - q[0].begin();
}

Node TermUtil::getRemoveQuantifiers2( Node n, std::map< Node, Node >& visited ) {
  std::map< Node, Node >::iterator it = visited.find( n );
  if( it!=visited.end() ){
    return it->second;
  }else{
    Node ret = n;
    if (n.getKind() == Kind::FORALL)
    {
      ret = getRemoveQuantifiers2( n[1], visited );
    }
    else if (n.getNumChildren() > 0)
    {
      std::vector< Node > children;
      bool childrenChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node ni = getRemoveQuantifiers2( n[i], visited );
        childrenChanged = childrenChanged || ni!=n[i];
        children.push_back( ni );
      }
      if( childrenChanged ){
        if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
          children.insert( children.begin(), n.getOperator() );
        }
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    visited[n] = ret;
    return ret;
  }
}

Node TermUtil::getInstConstAttr( Node n ) {
  if (!n.hasAttribute(InstConstantAttribute()) ){
    Node q;
    if (n.hasOperator())
    {
      q = getInstConstAttr(n.getOperator());
    }
    if (q.isNull())
    {
      for (const Node& nc : n)
      {
        q = getInstConstAttr(nc);
        if (!q.isNull())
        {
          break;
        }
      }
    }
    InstConstantAttribute ica;
    n.setAttribute(ica, q);
  }
  return n.getAttribute(InstConstantAttribute());
}

bool TermUtil::hasInstConstAttr(Node n)
{
  n = SkolemManager::getOriginalForm(n);
  return !getInstConstAttr(n).isNull();
}

Node TermUtil::getBoundVarAttr( Node n ) {
  if (!n.hasAttribute(BoundVarAttribute()) ){
    Node bv;
    if (n.getKind() == Kind::BOUND_VARIABLE)
    {
      bv = n;
    }
    else
    {
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        bv = getBoundVarAttr(n[i]);
        if( !bv.isNull() ){
          break;
        }
      }
    }
    BoundVarAttribute bva;
    n.setAttribute(bva, bv);
  }
  return n.getAttribute(BoundVarAttribute());
}

bool TermUtil::hasBoundVarAttr( Node n ) {
  return !getBoundVarAttr(n).isNull();
}

//remove quantifiers
Node TermUtil::getRemoveQuantifiers( Node n ) {
  std::map< Node, Node > visited;
  return getRemoveQuantifiers2( n, visited );
}

void TermUtil::computeInstConstContains(Node n, std::vector<Node>& ics)
{
  computeVarContainsInternal(n, Kind::INST_CONSTANT, ics);
}

void TermUtil::computeVarContains(Node n, std::vector<Node>& vars)
{
  computeVarContainsInternal(n, Kind::BOUND_VARIABLE, vars);
}

void TermUtil::computeQuantContains(Node n, std::vector<Node>& quants)
{
  computeVarContainsInternal(n, Kind::FORALL, quants);
}

void TermUtil::computeVarContainsInternal(Node n,
                                          Kind k,
                                          std::vector<Node>& vars)
{
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
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
      visited.insert(cur);
      if (cur.getKind() == k)
      {
        if (std::find(vars.begin(), vars.end(), cur) == vars.end())
        {
          vars.push_back(cur);
        }
      }
      else
      {
        if (cur.hasOperator())
        {
          visit.push_back(cur.getOperator());
        }
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
  } while (!visit.empty());
}

void TermUtil::computeInstConstContainsForQuant(Node q,
                                                Node n,
                                                std::vector<Node>& vars)
{
  std::vector<Node> ics;
  computeInstConstContains(n, ics);
  for (const Node& v : ics)
  {
    if (v.getAttribute(InstConstantAttribute()) == q)
    {
      if (std::find(vars.begin(), vars.end(), v) == vars.end())
      {
        vars.push_back(v);
      }
    }
  }
}

int TermUtil::getTermDepth( Node n ) {
  if (!n.hasAttribute(TermDepthAttribute()) ){
    int maxDepth = -1;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      int depth = getTermDepth( n[i] );
      if( depth>maxDepth ){
        maxDepth = depth;
      }
    }
    TermDepthAttribute tda;
    n.setAttribute(tda,1+maxDepth);
  }
  return n.getAttribute(TermDepthAttribute());
}

bool TermUtil::containsUninterpretedConstant( Node n ) {
  if (n.hasAttribute(ContainsUConstAttribute()))
  {
    return n.getAttribute(ContainsUConstAttribute()) != 0;
  }
  bool ret = false;
  Kind k = n.getKind();
  if (k == Kind::UNINTERPRETED_SORT_VALUE)
  {
    Assert(n.getType().isUninterpretedSort());
    ret = true;
  }
  else if (k == Kind::STORE_ALL)
  {
    ret = containsUninterpretedConstant(n.getConst<ArrayStoreAll>().getValue());
  }
  else if (k == Kind::FUNCTION_ARRAY_CONST)
  {
    ret = containsUninterpretedConstant(
        n.getConst<FunctionArrayConst>().getArrayValue());
  }
  else if (k == Kind::CONST_SEQUENCE)
  {
    const std::vector<Node>& charVec = n.getConst<Sequence>().getVec();
    for (const Node& nc : charVec)
    {
      if (containsUninterpretedConstant(nc))
      {
        ret = true;
        break;
      }
    }
  }
  else
  {
    for (const Node& nc : n)
    {
      if (containsUninterpretedConstant(nc))
      {
        ret = true;
        break;
      }
    }
  }
  ContainsUConstAttribute cuca;
  n.setAttribute(cuca, ret ? 1 : 0);
  return ret;
}

Node TermUtil::simpleNegate(Node n)
{
  Assert(n.getType().isBoolean());
  NodeManager* nm = NodeManager::currentNM();
  if (n.getKind() == Kind::OR || n.getKind() == Kind::AND)
  {
    std::vector< Node > children;
    for (const Node& cn : n)
    {
      children.push_back(simpleNegate(cn));
    }
    return nm->mkNode(n.getKind() == Kind::OR ? Kind::AND : Kind::OR, children);
  }
  else if (n.isConst())
  {
    return nm->mkConst(!n.getConst<bool>());
  }
  return n.negate();
}

Node TermUtil::mkNegate(Kind notk, Node n)
{
  if (n.getKind() == notk)
  {
    return n[0];
  }
  return NodeManager::currentNM()->mkNode(notk, n);
}

bool TermUtil::isNegate(Kind k)
{
  return k == Kind::NOT || k == Kind::BITVECTOR_NOT || k == Kind::BITVECTOR_NEG
         || k == Kind::NEG;
}

bool TermUtil::isAssoc(Kind k, bool reqNAry)
{
  if (reqNAry)
  {
    if (k == Kind::SET_UNION || k == Kind::SET_INTER)
    {
      return false;
    }
  }
  return k == Kind::ADD || k == Kind::MULT || k == Kind::NONLINEAR_MULT
         || k == Kind::AND || k == Kind::OR || k == Kind::XOR
         || k == Kind::BITVECTOR_ADD || k == Kind::BITVECTOR_MULT
         || k == Kind::BITVECTOR_AND || k == Kind::BITVECTOR_OR
         || k == Kind::BITVECTOR_XOR || k == Kind::BITVECTOR_XNOR
         || k == Kind::BITVECTOR_CONCAT || k == Kind::STRING_CONCAT
         || k == Kind::SET_UNION || k == Kind::SET_INTER
         || k == Kind::RELATION_JOIN || k == Kind::RELATION_PRODUCT
         || k == Kind::SEP_STAR;
}

bool TermUtil::isComm(Kind k, bool reqNAry)
{
  if (reqNAry)
  {
    if (k == Kind::SET_UNION || k == Kind::SET_INTER)
    {
      return false;
    }
  }
  return k == Kind::EQUAL || k == Kind::ADD || k == Kind::MULT
         || k == Kind::NONLINEAR_MULT || k == Kind::AND || k == Kind::OR
         || k == Kind::XOR || k == Kind::BITVECTOR_ADD
         || k == Kind::BITVECTOR_MULT || k == Kind::BITVECTOR_AND
         || k == Kind::BITVECTOR_OR || k == Kind::BITVECTOR_XOR
         || k == Kind::BITVECTOR_XNOR || k == Kind::SET_UNION
         || k == Kind::SET_INTER || k == Kind::SEP_STAR;
}

bool TermUtil::isNonAdditive( Kind k ) {
  return k == Kind::AND || k == Kind::OR || k == Kind::BITVECTOR_AND
         || k == Kind::BITVECTOR_OR;
}

bool TermUtil::isBoolConnective( Kind k ) {
  return k == Kind::OR || k == Kind::AND || k == Kind::EQUAL || k == Kind::ITE
         || k == Kind::FORALL || k == Kind::NOT || k == Kind::SEP_STAR;
}

bool TermUtil::isBoolConnectiveTerm( TNode n ) {
  return isBoolConnective(n.getKind())
         && (n.getKind() != Kind::EQUAL || n[0].getType().isBoolean())
         && (n.getKind() != Kind::ITE || n.getType().isBoolean());
}

Node TermUtil::mkTypeValue(TypeNode tn, int32_t val)
{
  Node n;
  if (tn.isRealOrInt())
  {
    Rational c(val);
    n = NodeManager::currentNM()->mkConstRealOrInt(tn, c);
  }
  else if (tn.isBitVector())
  {
    // cast to unsigned
    uint32_t uv = static_cast<uint32_t>(val);
    BitVector bval(tn.getConst<BitVectorSize>(), uv);
    n = NodeManager::currentNM()->mkConst<BitVector>(bval);
  }
  else if (tn.isBoolean())
  {
    if (val == 0)
    {
      n = NodeManager::currentNM()->mkConst(false);
    }
  }
  else if (tn.isStringLike())
  {
    if (val == 0)
    {
      n = strings::Word::mkEmptyWord(tn);
    }
  }
  return n;
}

Node TermUtil::mkTypeMaxValue(TypeNode tn)
{
  Node n;
  if (tn.isBitVector())
  {
    n = bv::utils::mkOnes(tn.getConst<BitVectorSize>());
  }
  else if (tn.isBoolean())
  {
    n = NodeManager::currentNM()->mkConst(true);
  }
  return n;
}

Node TermUtil::mkTypeValueOffset(TypeNode tn,
                                 Node val,
                                 int32_t offset,
                                 int32_t& status)
{
  Assert(val.isConst() && val.getType() == tn);
  Node val_o;
  status = -1;
  if (tn.isRealOrInt())
  {
    Rational vval = val.getConst<Rational>();
    Rational oval(offset);
    status = 0;
    return NodeManager::currentNM()->mkConstRealOrInt(tn, vval + oval);
  }
  else if (tn.isBitVector())
  {
    BitVector vval = val.getConst<BitVector>();
    uint32_t uv = static_cast<uint32_t>(offset);
    BitVector oval(tn.getConst<BitVectorSize>(), uv);
    return NodeManager::currentNM()->mkConst(vval + oval);
  }
  return val_o;
}

Node TermUtil::mkTypeConst(TypeNode tn, bool pol)
{
  return pol ? mkTypeMaxValue(tn) : mkTypeValue(tn, 0);
}

bool TermUtil::isAntisymmetric(Kind k, Kind& dk)
{
  if (k == Kind::GT)
  {
    dk = Kind::LT;
    return true;
  }
  else if (k == Kind::GEQ)
  {
    dk = Kind::LEQ;
    return true;
  }
  else if (k == Kind::BITVECTOR_UGT)
  {
    dk = Kind::BITVECTOR_ULT;
    return true;
  }
  else if (k == Kind::BITVECTOR_UGE)
  {
    dk = Kind::BITVECTOR_ULE;
    return true;
  }
  else if (k == Kind::BITVECTOR_SGT)
  {
    dk = Kind::BITVECTOR_SLT;
    return true;
  }
  else if (k == Kind::BITVECTOR_SGE)
  {
    dk = Kind::BITVECTOR_SLE;
    return true;
  }
  return false;
}

bool TermUtil::isIdempotentArg(Node n, Kind ik, int arg)
{
  // these should all be binary operators
  // Assert( ik!=DIVISION && ik!=INTS_DIVISION && ik!=INTS_MODULUS &&
  // ik!=BITVECTOR_UDIV );
  TypeNode tn = n.getType();
  if (n == mkTypeValue(tn, 0))
  {
    if (ik == Kind::ADD || ik == Kind::OR || ik == Kind::XOR
        || ik == Kind::BITVECTOR_ADD || ik == Kind::BITVECTOR_OR
        || ik == Kind::BITVECTOR_XOR || ik == Kind::STRING_CONCAT)
    {
      return true;
    }
    else if (ik == Kind::SUB || ik == Kind::BITVECTOR_SHL
             || ik == Kind::BITVECTOR_LSHR || ik == Kind::BITVECTOR_ASHR
             || ik == Kind::BITVECTOR_SUB || ik == Kind::BITVECTOR_UREM)
    {
      return arg == 1;
    }
  }
  else if (n == mkTypeValue(tn, 1))
  {
    if (ik == Kind::MULT || ik == Kind::BITVECTOR_MULT)
    {
      return true;
    }
    else if (ik == Kind::DIVISION || ik == Kind::DIVISION_TOTAL
             || ik == Kind::INTS_DIVISION || ik == Kind::INTS_DIVISION_TOTAL
             || ik == Kind::INTS_MODULUS || ik == Kind::INTS_MODULUS_TOTAL
             || ik == Kind::BITVECTOR_UDIV || ik == Kind::BITVECTOR_SDIV)
    {
      return arg == 1;
    }
  }
  else if (n == mkTypeMaxValue(tn))
  {
    if (ik == Kind::EQUAL || ik == Kind::BITVECTOR_AND
        || ik == Kind::BITVECTOR_XNOR)
    {
      return true;
    }
  }
  return false;
}

Node TermUtil::isSingularArg(Node n, Kind ik, unsigned arg)
{
  TypeNode tn = n.getType();
  if (n == mkTypeValue(tn, 0))
  {
    if (ik == Kind::AND || ik == Kind::MULT || ik == Kind::BITVECTOR_AND
        || ik == Kind::BITVECTOR_MULT)
    {
      return n;
    }
    else if (ik == Kind::BITVECTOR_SHL || ik == Kind::BITVECTOR_LSHR
             || ik == Kind::BITVECTOR_ASHR || ik == Kind::BITVECTOR_UREM)
    {
      if (arg == 0)
      {
        return n;
      }
    }
    else if (ik == Kind::BITVECTOR_UDIV || ik == Kind::BITVECTOR_SDIV)
    {
      if (arg == 0)
      {
        return n;
      }
      else if (arg == 1)
      {
        return mkTypeMaxValue(tn);
      }
    }
    else if (ik == Kind::DIVISION || ik == Kind::DIVISION_TOTAL
             || ik == Kind::INTS_DIVISION || ik == Kind::INTS_DIVISION_TOTAL
             || ik == Kind::INTS_MODULUS || ik == Kind::INTS_MODULUS_TOTAL)
    {
      if (arg == 0)
      {
        return n;
      }
    }
    else if (ik == Kind::STRING_SUBSTR)
    {
      if (arg == 0)
      {
        return n;
      }
      else if (arg == 2)
      {
        return mkTypeValue(NodeManager::currentNM()->stringType(), 0);
      }
    }
    else if (ik == Kind::STRING_INDEXOF)
    {
      if (arg == 0 || arg == 1)
      {
        return mkTypeValue(NodeManager::currentNM()->integerType(), -1);
      }
    }
  }
  else if (n == mkTypeValue(tn, 1))
  {
    if (ik == Kind::BITVECTOR_UREM)
    {
      return mkTypeValue(tn, 0);
    }
  }
  else if (n == mkTypeMaxValue(tn))
  {
    if (ik == Kind::OR || ik == Kind::BITVECTOR_OR)
    {
      return n;
    }
  }
  else
  {
    if (n.getType().isInteger() && n.getConst<Rational>().sgn() < 0)
    {
      // negative arguments
      if (ik == Kind::STRING_SUBSTR || ik == Kind::STRING_CHARAT)
      {
        return mkTypeValue(NodeManager::currentNM()->stringType(), 0);
      }
      else if (ik == Kind::STRING_INDEXOF)
      {
        Assert(arg == 2);
        return mkTypeValue(NodeManager::currentNM()->integerType(), -1);
      }
    }
  }
  return Node::null();
}

bool TermUtil::hasOffsetArg(Kind ik, int arg, int& offset, Kind& ok)
{
  if (ik == Kind::LT)
  {
    Assert(arg == 0 || arg == 1);
    offset = arg == 0 ? 1 : -1;
    ok = Kind::LEQ;
    return true;
  }
  else if (ik == Kind::BITVECTOR_ULT)
  {
    Assert(arg == 0 || arg == 1);
    offset = arg == 0 ? 1 : -1;
    ok = Kind::BITVECTOR_ULE;
    return true;
  }
  else if (ik == Kind::BITVECTOR_SLT)
  {
    Assert(arg == 0 || arg == 1);
    offset = arg == 0 ? 1 : -1;
    ok = Kind::BITVECTOR_SLE;
    return true;
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
