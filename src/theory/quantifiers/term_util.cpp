/*********************                                                        */
/*! \file term_util.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term utilities class
 **/

#include "theory/quantifiers/term_util.h"

#include "expr/datatype.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "options/uf_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers_engine.h"
#include "theory/strings/word.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory::inst;

namespace CVC4 {
namespace theory {
namespace quantifiers {

TermUtil::TermUtil(QuantifiersEngine* qe) : d_quantEngine(qe)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
}

TermUtil::~TermUtil(){

}

void TermUtil::registerQuantifier( Node q ){
  if( d_inst_constants.find( q )==d_inst_constants.end() ){
    Debug("quantifiers-engine") << "Instantiation constants for " << q << " : " << std::endl;
    for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
      d_vars[q].push_back( q[0][i] );
      d_var_num[q][q[0][i]] = i;
      //make instantiation constants
      Node ic = NodeManager::currentNM()->mkInstConstant( q[0][i].getType() );
      d_inst_constants_map[ic] = q;
      d_inst_constants[ q ].push_back( ic );
      Debug("quantifiers-engine") << "  " << ic << std::endl;
      //set the var number attribute
      InstVarNumAttribute ivna;
      ic.setAttribute( ivna, i );
      InstConstantAttribute ica;
      ic.setAttribute( ica, q );
    }
  }
}

Node TermUtil::getRemoveQuantifiers2( Node n, std::map< Node, Node >& visited ) {
  std::map< Node, Node >::iterator it = visited.find( n );
  if( it!=visited.end() ){
    return it->second;
  }else{
    Node ret = n;
    if( n.getKind()==FORALL ){
      ret = getRemoveQuantifiers2( n[1], visited );
    }else if( n.getNumChildren()>0 ){
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

bool TermUtil::hasInstConstAttr( Node n ) {
  return !getInstConstAttr(n).isNull();
}

Node TermUtil::getBoundVarAttr( Node n ) {
  if (!n.hasAttribute(BoundVarAttribute()) ){
    Node bv;
    if( n.getKind()==BOUND_VARIABLE ){
      bv = n;
    }else{
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

//quantified simplify
Node TermUtil::getQuantSimplify( Node n ) {
  std::unordered_set<Node, NodeHashFunction> fvs;
  expr::getFreeVariables(n, fvs);
  if (fvs.empty())
  {
    return Rewriter::rewrite( n );
  }
  std::vector<Node> bvs;
  bvs.insert(bvs.end(), fvs.begin(), fvs.end());
  NodeManager* nm = NodeManager::currentNM();
  Node q = nm->mkNode(FORALL, nm->mkNode(BOUND_VAR_LIST, bvs), n);
  q = Rewriter::rewrite(q);
  return getRemoveQuantifiers(q);
}

/** get the i^th instantiation constant of q */
Node TermUtil::getInstantiationConstant( Node q, int i ) const {
  std::map< Node, std::vector< Node > >::const_iterator it = d_inst_constants.find( q );
  if( it!=d_inst_constants.end() ){
    return it->second[i];
  }else{
    return Node::null();
  }
}

/** get number of instantiation constants for q */
unsigned TermUtil::getNumInstantiationConstants( Node q ) const {
  std::map< Node, std::vector< Node > >::const_iterator it = d_inst_constants.find( q );
  if( it!=d_inst_constants.end() ){
    return it->second.size();
  }else{
    return 0;
  }
}

Node TermUtil::getInstConstantBody( Node q ){
  std::map< Node, Node >::iterator it = d_inst_const_body.find( q );
  if( it==d_inst_const_body.end() ){
    Node n = substituteBoundVariablesToInstConstants(q[1], q);
    d_inst_const_body[ q ] = n;
    return n;
  }else{
    return it->second;
  }
}

Node TermUtil::substituteBoundVariablesToInstConstants(Node n, Node q)
{
  registerQuantifier( q );
  return n.substitute( d_vars[q].begin(), d_vars[q].end(), d_inst_constants[q].begin(), d_inst_constants[q].end() );
}

Node TermUtil::substituteInstConstantsToBoundVariables(Node n, Node q)
{
  registerQuantifier( q );
  return n.substitute( d_inst_constants[q].begin(), d_inst_constants[q].end(), d_vars[q].begin(), d_vars[q].end() );
}

Node TermUtil::substituteBoundVariables(Node n,
                                        Node q,
                                        std::vector<Node>& terms)
{
  registerQuantifier(q);
  Assert(d_vars[q].size() == terms.size());
  return n.substitute( d_vars[q].begin(), d_vars[q].end(), terms.begin(), terms.end() );
}

Node TermUtil::substituteInstConstants(Node n, Node q, std::vector<Node>& terms)
{
  registerQuantifier(q);
  Assert(d_inst_constants[q].size() == terms.size());
  return n.substitute(d_inst_constants[q].begin(),
                      d_inst_constants[q].end(),
                      terms.begin(),
                      terms.end());
}

void TermUtil::computeInstConstContains(Node n, std::vector<Node>& ics)
{
  computeVarContainsInternal(n, INST_CONSTANT, ics);
}

void TermUtil::computeVarContains(Node n, std::vector<Node>& vars)
{
  computeVarContainsInternal(n, BOUND_VARIABLE, vars);
}

void TermUtil::computeQuantContains(Node n, std::vector<Node>& quants)
{
  computeVarContainsInternal(n, FORALL, quants);
}

void TermUtil::computeVarContainsInternal(Node n,
                                          Kind k,
                                          std::vector<Node>& vars)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
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

Node TermUtil::ensureType( Node n, TypeNode tn ) {
  TypeNode ntn = n.getType();
  Assert(ntn.isComparableTo(tn));
  if( ntn.isSubtypeOf( tn ) ){
    return n;
  }else{
    if( tn.isInteger() ){
      return NodeManager::currentNM()->mkNode( TO_INTEGER, n );
    }
    return Node::null();
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
  if (!n.hasAttribute(ContainsUConstAttribute()) ){
    bool ret = false;
    if( n.getKind()==UNINTERPRETED_CONSTANT ){
      ret = true;
    }else{ 
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( containsUninterpretedConstant( n[i] ) ){
          ret = true;
          break;
        }
      }
    }
    ContainsUConstAttribute cuca;
    n.setAttribute(cuca, ret ? 1 : 0);
  }
  return n.getAttribute(ContainsUConstAttribute())!=0;
}

Node TermUtil::simpleNegate(Node n)
{
  Assert(n.getType().isBoolean());
  NodeManager* nm = NodeManager::currentNM();
  if( n.getKind()==OR || n.getKind()==AND ){
    std::vector< Node > children;
    for (const Node& cn : n)
    {
      children.push_back(simpleNegate(cn));
    }
    return nm->mkNode(n.getKind() == OR ? AND : OR, children);
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
  return k == NOT || k == BITVECTOR_NOT || k == BITVECTOR_NEG || k == UMINUS;
}

bool TermUtil::isAssoc(Kind k, bool reqNAry)
{
  if (reqNAry)
  {
    if (k == UNION || k == INTERSECTION)
    {
      return false;
    }
  }
  return k == PLUS || k == MULT || k == NONLINEAR_MULT || k == AND || k == OR
         || k == XOR || k == BITVECTOR_PLUS || k == BITVECTOR_MULT
         || k == BITVECTOR_AND || k == BITVECTOR_OR || k == BITVECTOR_XOR
         || k == BITVECTOR_XNOR || k == BITVECTOR_CONCAT || k == STRING_CONCAT
         || k == UNION || k == INTERSECTION || k == JOIN || k == PRODUCT
         || k == SEP_STAR;
}

bool TermUtil::isComm(Kind k, bool reqNAry)
{
  if (reqNAry)
  {
    if (k == UNION || k == INTERSECTION)
    {
      return false;
    }
  }
  return k == EQUAL || k == PLUS || k == MULT || k == NONLINEAR_MULT || k == AND
         || k == OR || k == XOR || k == BITVECTOR_PLUS || k == BITVECTOR_MULT
         || k == BITVECTOR_AND || k == BITVECTOR_OR || k == BITVECTOR_XOR
         || k == BITVECTOR_XNOR || k == UNION || k == INTERSECTION
         || k == SEP_STAR;
}

bool TermUtil::isNonAdditive( Kind k ) {
  return k==AND || k==OR || k==BITVECTOR_AND || k==BITVECTOR_OR;
}

bool TermUtil::isBoolConnective( Kind k ) {
  return k==OR || k==AND || k==EQUAL || k==ITE || k==FORALL || k==NOT || k==SEP_STAR;
}

bool TermUtil::isBoolConnectiveTerm( TNode n ) {
  return isBoolConnective( n.getKind() ) &&
         ( n.getKind()!=EQUAL || n[0].getType().isBoolean() ) && 
         ( n.getKind()!=ITE || n.getType().isBoolean() );
}

Node TermUtil::getTypeValue(TypeNode tn, int val)
{
  std::unordered_map<int, Node>::iterator it = d_type_value[tn].find(val);
  if (it == d_type_value[tn].end())
  {
    Node n = mkTypeValue(tn, val);
    d_type_value[tn][val] = n;
    return n;
  }
  return it->second;
}

Node TermUtil::mkTypeValue(TypeNode tn, int val)
{
  Node n;
  if (tn.isInteger() || tn.isReal())
  {
    Rational c(val);
    n = NodeManager::currentNM()->mkConst(c);
  }
  else if (tn.isBitVector())
  {
    unsigned int uv = val;
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

Node TermUtil::getTypeMaxValue(TypeNode tn)
{
  std::unordered_map<TypeNode, Node, TypeNodeHashFunction>::iterator it =
      d_type_max_value.find(tn);
  if (it == d_type_max_value.end())
  {
    Node n = mkTypeMaxValue(tn);
    d_type_max_value[tn] = n;
    return n;
  }
  return it->second;
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

Node TermUtil::getTypeValueOffset(TypeNode tn,
                                  Node val,
                                  int offset,
                                  int& status)
{
  std::unordered_map<int, Node>::iterator it =
      d_type_value_offset[tn][val].find(offset);
  if (it == d_type_value_offset[tn][val].end())
  {
    Node val_o;
    Node offset_val = getTypeValue(tn, offset);
    status = -1;
    if (!offset_val.isNull())
    {
      if (tn.isInteger() || tn.isReal())
      {
        val_o = Rewriter::rewrite(
            NodeManager::currentNM()->mkNode(PLUS, val, offset_val));
        status = 0;
      }
      else if (tn.isBitVector())
      {
        val_o = Rewriter::rewrite(
            NodeManager::currentNM()->mkNode(BITVECTOR_PLUS, val, offset_val));
        // TODO : enable?  watch for overflows
      }
    }
    d_type_value_offset[tn][val][offset] = val_o;
    d_type_value_offset_status[tn][val][offset] = status;
    return val_o;
  }
  status = d_type_value_offset_status[tn][val][offset];
  return it->second;
}

Node TermUtil::mkTypeConst(TypeNode tn, bool pol)
{
  return pol ? mkTypeMaxValue(tn) : mkTypeValue(tn, 0);
}

bool TermUtil::isAntisymmetric(Kind k, Kind& dk)
{
  if (k == GT)
  {
    dk = LT;
    return true;
  }
  else if (k == GEQ)
  {
    dk = LEQ;
    return true;
  }
  else if (k == BITVECTOR_UGT)
  {
    dk = BITVECTOR_ULT;
    return true;
  }
  else if (k == BITVECTOR_UGE)
  {
    dk = BITVECTOR_ULE;
    return true;
  }
  else if (k == BITVECTOR_SGT)
  {
    dk = BITVECTOR_SLT;
    return true;
  }
  else if (k == BITVECTOR_SGE)
  {
    dk = BITVECTOR_SLE;
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
  if (n == getTypeValue(tn, 0))
  {
    if (ik == PLUS || ik == OR || ik == XOR || ik == BITVECTOR_PLUS
        || ik == BITVECTOR_OR
        || ik == BITVECTOR_XOR
        || ik == STRING_CONCAT)
    {
      return true;
    }
    else if (ik == MINUS || ik == BITVECTOR_SHL || ik == BITVECTOR_LSHR
             || ik == BITVECTOR_ASHR
             || ik == BITVECTOR_SUB
             || ik == BITVECTOR_UREM
             || ik == BITVECTOR_UREM_TOTAL)
    {
      return arg == 1;
    }
  }
  else if (n == getTypeValue(tn, 1))
  {
    if (ik == MULT || ik == BITVECTOR_MULT)
    {
      return true;
    }
    else if (ik == DIVISION || ik == DIVISION_TOTAL || ik == INTS_DIVISION
             || ik == INTS_DIVISION_TOTAL
             || ik == INTS_MODULUS
             || ik == INTS_MODULUS_TOTAL
             || ik == BITVECTOR_UDIV_TOTAL
             || ik == BITVECTOR_UDIV
             || ik == BITVECTOR_SDIV)
    {
      return arg == 1;
    }
  }
  else if (n == getTypeMaxValue(tn))
  {
    if (ik == EQUAL || ik == BITVECTOR_AND || ik == BITVECTOR_XNOR)
    {
      return true;
    }
  }
  return false;
}

Node TermUtil::isSingularArg(Node n, Kind ik, unsigned arg)
{
  TypeNode tn = n.getType();
  if (n == getTypeValue(tn, 0))
  {
    if (ik == AND || ik == MULT || ik == BITVECTOR_AND || ik == BITVECTOR_MULT)
    {
      return n;
    }
    else if (ik == BITVECTOR_SHL || ik == BITVECTOR_LSHR || ik == BITVECTOR_ASHR
             || ik == BITVECTOR_UREM
             || ik == BITVECTOR_UREM_TOTAL)
    {
      if (arg == 0)
      {
        return n;
      }
    }
    else if (ik == BITVECTOR_UDIV_TOTAL || ik == BITVECTOR_UDIV
             || ik == BITVECTOR_SDIV)
    {
      if (arg == 0)
      {
        return n;
      }
      else if (arg == 1)
      {
        return getTypeMaxValue(tn);
      }
    }
    else if (ik == DIVISION || ik == DIVISION_TOTAL || ik == INTS_DIVISION
             || ik == INTS_DIVISION_TOTAL
             || ik == INTS_MODULUS
             || ik == INTS_MODULUS_TOTAL)
    {
      if (arg == 0)
      {
        return n;
      }
    }
    else if (ik == STRING_SUBSTR)
    {
      if (arg == 0)
      {
        return n;
      }
      else if (arg == 2)
      {
        return getTypeValue(NodeManager::currentNM()->stringType(), 0);
      }
    }
    else if (ik == STRING_STRIDOF)
    {
      if (arg == 0 || arg == 1)
      {
        return getTypeValue(NodeManager::currentNM()->integerType(), -1);
      }
    }
  }
  else if (n == getTypeValue(tn, 1))
  {
    if (ik == BITVECTOR_UREM_TOTAL)
    {
      return getTypeValue(tn, 0);
    }
  }
  else if (n == getTypeMaxValue(tn))
  {
    if (ik == OR || ik == BITVECTOR_OR)
    {
      return n;
    }
  }
  else
  {
    if (n.getType().isReal() && n.getConst<Rational>().sgn() < 0)
    {
      // negative arguments
      if (ik == STRING_SUBSTR || ik == STRING_CHARAT)
      {
        return getTypeValue(NodeManager::currentNM()->stringType(), 0);
      }
      else if (ik == STRING_STRIDOF)
      {
        Assert(arg == 2);
        return getTypeValue(NodeManager::currentNM()->integerType(), -1);
      }
    }
  }
  return Node::null();
}

bool TermUtil::hasOffsetArg(Kind ik, int arg, int& offset, Kind& ok)
{
  if (ik == LT)
  {
    Assert(arg == 0 || arg == 1);
    offset = arg == 0 ? 1 : -1;
    ok = LEQ;
    return true;
  }
  else if (ik == BITVECTOR_ULT)
  {
    Assert(arg == 0 || arg == 1);
    offset = arg == 0 ? 1 : -1;
    ok = BITVECTOR_ULE;
    return true;
  }
  else if (ik == BITVECTOR_SLT)
  {
    Assert(arg == 0 || arg == 1);
    offset = arg == 0 ? 1 : -1;
    ok = BITVECTOR_SLE;
    return true;
  }
  return false;
}

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
