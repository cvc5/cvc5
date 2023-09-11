/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of ALF node conversion
 */

#include "proof/alf/alf_node_converter.h"

#include <algorithm>
#include <iomanip>
#include <sstream>

#include "expr/array_store_all.h"
#include "expr/cardinality_constraint.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/nary_term_util.h"
#include "expr/sequence.h"
#include "expr/skolem_manager.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/builtin/generic_op.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "theory/uf/function_const.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "util/bitvector.h"
#include "util/finite_field_value.h"
#include "util/floatingpoint.h"
#include "util/iand.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/indexed_root_predicate.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace proof {

AlfNodeConverter::AlfNodeConverter()
{
  NodeManager* nm = NodeManager::currentNM();
  d_sortType = nm->mkSort("sortType");
}

Node AlfNodeConverter::preConvert(Node n)
{
  // match is not supported in LFSC syntax, we eliminate it at pre-order
  // traversal, which avoids type-checking errors during conversion, since e.g.
  // match case nodes are required but cannot be preserved
  if (n.getKind() == MATCH)
  {
    return theory::datatypes::DatatypesRewriter::expandMatch(n);
  }
  return n;
}

Node AlfNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  // we eliminate MATCH at preConvert above
  Assert(k != MATCH);
  Trace("alf-term-process-debug")
      << "postConvert " << n << " " << k << std::endl;
  if (k == ASCRIPTION_TYPE || k == RAW_SYMBOL)
  {
    // dummy node, return it
    return n;
  }
  TypeNode tn = n.getType();
  if (k == SKOLEM)
  {
    // constructors/selectors are represented by skolems, which are defined
    // symbols
    if (tn.isDatatypeConstructor() || tn.isDatatypeSelector()
        || tn.isDatatypeTester() || tn.isDatatypeUpdater())
    {
      // note these are not converted to their user named (cvc.) symbols here,
      // to avoid type errors when constructing terms for postConvert
      return n;
    }
    // might be a skolem function
    Node ns = maybeMkSkolemFun(n);
    if (!ns.isNull())
    {
      return ns;
    }
    // Otherwise, it is an uncategorized skolem, must use a fresh variable.
    // This case will only apply for terms originating from places with no
    // proof support. Note it is not added as a declared variable, instead it
    // is used as (var N T) throughout.
    Node index = nm->mkConstInt(Rational(getOrAssignIndexForConst(n)));
    Node tc = typeAsNode(tn);
    return mkInternalApp("const", {index, tc}, tn);
  }
  else if (k == BOUND_VARIABLE)
  {
    // note: we always distinguish variables, to ensure they do not have
    // names that are overloaded with user names
    std::stringstream ss;
    ss << n;
    std::string sname = ss.str();
    size_t index = d_varIndex[sname];
    d_varIndex[sname]++;
    std::stringstream ssn;
    ssn << "alf." << index << "." << sname;
    return NodeManager::currentNM()->mkBoundVar(ssn.str(), tn);
  }
  else if (k == VARIABLE)
  {
    // note that we do not handle overloading here
    return n;
  }
  else if (k == APPLY_UF)
  {
    // must ensure we print higher-order function applications with "_"
    if (!n.getOperator().isVar())
    {
      std::vector<Node> args;
      args.push_back(n.getOperator());
      args.insert(args.end(), n.begin(), n.end());
      return mkInternalApp("_", args, tn);
    }
  }
  else if (k == HO_APPLY)
  {
    return mkInternalApp("_", {n[0], n[1]}, tn);
  }
  else if (k == CONST_INTEGER)
  {
    Rational r = n.getConst<Rational>();
    if (r.sgn() == -1)
    {
      Node na = nm->mkConstInt(r.abs());
      return mkInternalApp("alf.neg", {na}, tn);
    }
    return n;
  }
  else if (k == CONST_RATIONAL)
  {
    Rational r = n.getConst<Rational>();
    // ensure rationals are printed properly here using alf syntax
    // which computes the rational (alf.qdiv n d).
    Node num = nm->mkConstInt(r.getNumerator().abs());
    Node den = nm->mkConstInt(r.getDenominator());
    Node ret = mkInternalApp("alf.qdiv", {num, den}, tn);
    // negative (alf.neg .)
    if (r.sgn() == -1)
    {
      ret = mkInternalApp("alf.neg", {ret}, tn);
    }
    return ret;
  }
  else if (k == LAMBDA || k == WITNESS)
  {
    // e.g. (lambda ((x1 T1) ... (xn Tk)) P) is
    // (lambda x1 (lambda x2 ... (lambda xn P)))
    Node ret = n[1];
    TypeNode tnr = ret.getType();
    std::stringstream opName;
    opName << printer::smt2::Smt2Printer::smtKindString(k);
    for (size_t i = 0, nchild = n[0].getNumChildren(); i < nchild; i++)
    {
      size_t ii = (nchild - 1) - i;
      Node v = convert(n[0][ii]);
      // use the body return type for all terms except the last one.
      tnr = ii == 0 ? n.getType() : nm->mkFunctionType({v.getType()}, tnr);
      ret = mkInternalApp(opName.str(), {v, ret}, tnr);
    }
    return ret;
  }
  else if (n.isClosure())
  {
    // e.g. (forall ((x1 T1) ... (xn Tk)) P) is
    // (forall (@list x1 ... xn) P)
    std::vector<Node> vars;
    for (const Node& v : n[0])
    {
      vars.push_back(convert(v));
    }
    Node vl = mkList(vars);
    // notice that intentionally we drop annotations here
    std::vector<Node> args;
    args.push_back(vl);
    args.insert(args.end(), n.begin()+1, n.begin()+getNumChildrenForClosure(k));
    return mkInternalApp(
        printer::smt2::Smt2Printer::smtKindString(k), args, tn);
  }
  else if (k == STORE_ALL)
  {
    Node t = typeAsNode(tn);
    ArrayStoreAll storeAll = n.getConst<ArrayStoreAll>();
    Node val = convert(storeAll.getValue());
    return mkInternalApp("store_all", {t, val}, tn);
  }
  else if (k == SET_EMPTY || k == SET_UNIVERSE || k == BAG_EMPTY
           || k == SEP_NIL)
  {
    Node t = typeAsNode(tn);
    return mkInternalApp(printer::smt2::Smt2Printer::smtKindString(k), {t}, tn);
  }
  else if (k == SET_INSERT)
  {
    std::vector<Node> iargs(n.begin(), n.begin()+n.getNumChildren()-1);
    Node list = mkList(iargs);
    return mkInternalApp("set.insert", {list, n[n.getNumChildren()-1]}, tn);
  }
  else if (k == CONST_SEQUENCE)
  {
    if (n.getConst<Sequence>().empty())
    {
      Node t = typeAsNode(tn);
      return mkInternalApp("seq.empty", {t}, tn);
    }
    // otherwise must convert to term representation and convert
    Node cc = theory::strings::utils::mkConcatForConstSequence(n);
    return convert(cc);
  }
  else if (k == CONST_FINITE_FIELD)
  {
    const FiniteFieldValue& ffv = n.getConst<FiniteFieldValue>();
    Node v = convert(nm->mkConstInt(ffv.getValue()));
    Node fs = convert(nm->mkConstInt(ffv.getFieldSize()));
    return mkInternalApp("ff.value", {fs, v}, tn);
  }
  else if (k == FUNCTION_ARRAY_CONST)
  {
    // must convert to lambda and then run the conversion
    Node lam = theory::uf::FunctionConst::toLambda(n);
    Assert(!lam.isNull());
    return convert(lam);
  }
  else if (k == BITVECTOR_BB_TERM)
  {
    Node curr = mkInternalSymbol("bvempty", nm->mkBitVectorType(0));
    for (size_t i = 0, nchildren = n.getNumChildren(); i < nchildren; i++)
    {
      size_t ii = (nchildren - 1) - i;
      std::vector<Node> args;
      args.push_back(n[ii]);
      args.push_back(curr);
      curr = mkInternalApp("bbT", args, nm->mkBitVectorType(i + 1));
    }
    return curr;
  }
  else if (k == APPLY_TESTER || k == APPLY_UPDATER || k == NEG
           || k == DIVISION_TOTAL || k == INTS_DIVISION_TOTAL
           || k == INTS_MODULUS_TOTAL || k == APPLY_CONSTRUCTOR
           || k == APPLY_SELECTOR)
  {
    // kinds where the operator may be different
    Node opc = getOperatorOfTerm(n);
    std::vector<Node> newArgs;
    if (n.getNumChildren() == 0)
    {
      return opc;
    }
    else if (opc.getNumChildren() > 0)
    {
      newArgs.insert(newArgs.end(), opc.begin(), opc.end());
      newArgs.insert(newArgs.end(), n.begin(), n.end());
      opc = opc.getOperator();
      std::stringstream ss;
      ss << opc;
      return mkInternalApp(ss.str(), newArgs, tn);
    }
    newArgs.insert(newArgs.end(), n.begin(), n.end());
    return mkApplyUf(opc, newArgs);
  }
  else if (k == INDEXED_ROOT_PREDICATE)
  {
    const IndexedRootPredicate& irp = n.getOperator().getConst<IndexedRootPredicate>();
    std::vector<Node> newArgs;
    newArgs.push_back(nm->mkConstInt(irp.d_index));
    newArgs.insert(newArgs.end(), n.begin(), n.end());
    return mkInternalApp("INDEXED_ROOT_PREDICATE", newArgs, tn);
  }
  else if (k==FLOATINGPOINT_COMPONENT_NAN ||
    k==FLOATINGPOINT_COMPONENT_INF ||
    k==FLOATINGPOINT_COMPONENT_ZERO ||
    k==FLOATINGPOINT_COMPONENT_SIGN ||
    k==FLOATINGPOINT_COMPONENT_EXPONENT ||
    k==FLOATINGPOINT_COMPONENT_SIGNIFICAND)
  {
    // dummy symbol, provide the return type
    Node tnn = typeAsNode(tn);
    return mkInternalApp(printer::smt2::Smt2Printer::smtKindString(k), {tnn}, tn);
  }
  else if (GenericOp::isIndexedOperatorKind(k))
  {
    // return app of?
    std::vector<Node> args =
        GenericOp::getIndicesForOperator(k, n.getOperator());
    if (k==RELATION_GROUP || k == TABLE_GROUP)
    {
      Node list = mkList(args);
      std::vector<Node> children;
      children.push_back(list);
      children.insert(children.end(), n.begin(), n.end());
      return mkInternalApp(printer::smt2::Smt2Printer::smtKindString(k), children, tn);
    }
    args.insert(args.end(), n.begin(), n.end());
    return mkInternalApp(
        printer::smt2::Smt2Printer::smtKindString(k), args, tn);
  }
  return n;
}

Node AlfNodeConverter::mkApplyUf(Node op, const std::vector<Node>& args) const
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> aargs;
  if (op.isVar())
  {
    aargs.push_back(op);
  }
  else
  {
    // Note that dag threshold is disabled for printing operators.
    std::stringstream ss;
    options::ioutils::applyOutputLanguage(ss, Language::LANG_SMTLIB_V2_6);
    options::ioutils::applyDagThresh(ss, 0);
    ss << op;
    Node opv = nm->mkRawSymbol(ss.str(), op.getType());
    aargs.push_back(opv);
  }
  aargs.insert(aargs.end(), args.begin(), args.end());
  return nm->mkNode(APPLY_UF, aargs);
}

bool AlfNodeConverter::shouldTraverse(Node n)
{
  Kind k = n.getKind();
  // don't convert bound variable or instantiation pattern list directly
  if (k == BOUND_VAR_LIST || k == INST_PATTERN_LIST)
  {
    return false;
  }
  // should not traverse internal applications
  if (k == APPLY_UF)
  {
    if (d_symbols.find(n.getOperator()) != d_symbols.end())
    {
      return false;
    }
  }
  return true;
}

Node AlfNodeConverter::maybeMkSkolemFun(Node k)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  SkolemFunId sfi = SkolemFunId::NONE;
  Node cacheVal;
  TypeNode tn = k.getType();
  if (sm->isSkolemFunction(k, sfi, cacheVal))
  {
    Node app;
    if (sfi == SkolemFunId::PURIFY)
    {
      Assert(cacheVal.getType() == k.getType());
      // special case: just use self
      app = convert(cacheVal);
    }
    else
    {
      // convert every skolem function to its name applied to arguments
      std::stringstream ss;
      ss << "@k." << sfi;
      std::vector<Node> args;
      if (sfi == SkolemFunId::QUANTIFIERS_SKOLEMIZE)
      {
        // must provide the variable, not the index (for typing)
        Assert(cacheVal.getNumChildren() == 2);
        Assert(cacheVal[0].getKind() == EXISTS);
        Node q = convert(cacheVal[0]);
        Node index = cacheVal[1];
        Assert(index.getKind() == CONST_INTEGER);
        const Integer& i = index.getConst<Rational>().getNumerator();
        Assert(i.fitsUnsignedInt());
        size_t ii = i.getUnsignedInt();
        args.push_back(q);
        args.push_back(convert(q[0][ii]));
      }
      else
      {
        if (cacheVal.getKind() == SEXPR)
        {
          for (const Node& cv : cacheVal)
          {
            args.push_back(convert(cv));
          }
        }
        else if (!cacheVal.isNull())
        {
          args.push_back(convert(cacheVal));
        }
      }
      // must convert all arguments
      app = mkInternalApp(ss.str(), args, k.getType());
    }
    // wrap in "skolem" operator
    return mkInternalApp("skolem", {app}, k.getType());
  }
  return Node::null();
}

Node AlfNodeConverter::typeAsNode(TypeNode tn)
{
  // should always exist in the cache, as we always run types through
  // postConvertType before calling this method.
  std::map<TypeNode, Node>::const_iterator it = d_typeAsNode.find(tn);
  if (it != d_typeAsNode.end())
  {
    return it->second;
  }
  // dummy symbol whose name is the type printed
  // this suffices since ALF faithfully represents all types.
  // note we cannot letify types (same as in SMT-LIB)
  std::stringstream ss;
  ss << tn;
  Node ret = mkInternalSymbol(ss.str(), d_sortType, true);
  d_typeAsNode[tn] = ret;
  return ret;
}
size_t AlfNodeConverter::getNumChildrenForClosure(Kind k) const
{
  return k==SET_COMPREHENSION ? 3 : 2;
}

Node AlfNodeConverter::mkNil(TypeNode tn)
{
  return mkInternalSymbol("alf.nil", tn);
}

Node AlfNodeConverter::getNullTerminator(Kind k, TypeNode tn)
{
  switch (k)
  {
    case kind::APPLY_UF:
    case kind::DISTINCT:
    case kind::FLOATINGPOINT_LT:
    case kind::FLOATINGPOINT_LEQ:
    case kind::FLOATINGPOINT_GT:
    case kind::FLOATINGPOINT_GEQ:
      // the above operators may take arbitrary number of arguments but are not marked as n-ary in ALF
      return Node::null();
    case kind::APPLY_CONSTRUCTOR:
      // tuple constructor is n-ary with unit tuple as null terminator
      if (tn.isTuple())
      {
        TypeNode tnu = NodeManager::currentNM()->mkTupleType({});
        return NodeManager::currentNM()->mkGroundValue(tnu);
      }
      return Node::null();
      break;
    case kind::OR: return NodeManager::currentNM()->mkConst(false);
    case kind::AND: return NodeManager::currentNM()->mkConst(true);
    case kind::ADD: return NodeManager::currentNM()->mkConstInt(Rational(0));
    case kind::MULT:
    case kind::NONLINEAR_MULT:
      return NodeManager::currentNM()->mkConstInt(Rational(1));
    case kind::BITVECTOR_CONCAT:
      return mkInternalSymbol("bvempty",
                              NodeManager::currentNM()->mkBitVectorType(0));
    default: break;
  }
  return mkNil(tn);
}

Node AlfNodeConverter::mkList(const std::vector<Node>& args)
{
  TypeNode tn = NodeManager::currentNM()->booleanType();
  if (args.empty())
  {
    return mkNil(tn);
  }
  else if (args.size() == 1)
  {
    std::vector<Node> aargs(args.begin(), args.end());
    aargs.push_back(mkNil(tn));
    return mkInternalApp("@list", aargs, tn);
  }
  return mkInternalApp("@list", args, tn);
}

Node AlfNodeConverter::mkInternalSymbol(const std::string& name,
                                        TypeNode tn,
                                        bool useRawSym)
{
  // use raw symbol so that it is never quoted
  NodeManager* nm = NodeManager::currentNM();
  Node sym = useRawSym ? nm->mkRawSymbol(name, tn) : nm->mkBoundVar(name, tn);
  d_symbols.insert(sym);
  return sym;
}

Node AlfNodeConverter::mkInternalApp(const std::string& name,
                                     const std::vector<Node>& args,
                                     TypeNode ret,
                                     bool useRawSym)
{
  if (!args.empty())
  {
    std::vector<TypeNode> argTypes;
    for (const Node& a : args)
    {
      Assert(!a.isNull());
      argTypes.push_back(a.getType());
    }
    NodeManager* nm = NodeManager::currentNM();
    TypeNode atype = nm->mkFunctionType(argTypes, ret);
    Node op = mkInternalSymbol(name, atype, useRawSym);
    std::vector<Node> aargs;
    aargs.push_back(op);
    aargs.insert(aargs.end(), args.begin(), args.end());
    return nm->mkNode(APPLY_UF, aargs);
  }
  return mkInternalSymbol(name, ret, useRawSym);
}

Node AlfNodeConverter::getOperatorOfTerm(Node n)
{
  Assert(n.hasOperator());
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  std::stringstream opName;
  Trace("alf-term-process-debug2")
      << "getOperatorOfTerm " << n << " " << k << " "
      << (n.getMetaKind() == metakind::PARAMETERIZED) << " "
      << GenericOp::isIndexedOperatorKind(k) << std::endl;
  std::vector<Node> indices;
  if (n.getMetaKind() == metakind::PARAMETERIZED)
  {
    Node op = n.getOperator();
    bool isIndexed = GenericOp::isIndexedOperatorKind(k);
    if (isIndexed)
    {
      indices = GenericOp::getIndicesForOperator(k, n.getOperator());
    }
    else if (op.getType().isFunction())
    {
      return op;
    }
    // note other kinds of functions (e.g. selectors and testers)
    Node ret;
    if (isIndexed)
    {
      if (k == APPLY_TESTER)
      {
        size_t cindex = DType::indexOf(op);
        const DType& dt = DType::datatypeOf(op);
        if (dt.isTuple())
        {
          opName << "is-tuple";
        }
        else
        {
          opName << "is-" << dt[cindex].getConstructor();
        }
        indices.clear();
      }
      else if (k == APPLY_UPDATER)
      {
        indices.clear();
        size_t index = DType::indexOf(op);
        const DType& dt = DType::datatypeOf(op);
        size_t cindex = DType::cindexOf(op);
        if (dt.isTuple())
        {
          opName << "tuple.update";
          indices.push_back(nm->mkConstInt(cindex));
        }
        else
        {
          opName << "update-" << dt[cindex][index].getSelector();
        }
      }
      else
      {
        opName << printer::smt2::Smt2Printer::smtKindString(k);
      }
    }
    else if (k == APPLY_CONSTRUCTOR)
    {
      unsigned index = DType::indexOf(op);
      const DType& dt = DType::datatypeOf(op);
      // get its variable name
      if (dt.isTuple())
      {
        if (n.getNumChildren() == 0)
        {
          opName << "tuple.unit";
        }
        else
        {
          opName << "tuple";
        }
      }
      else
      {
        opName << dt[index].getConstructor();
      }
    }
    else if (k == APPLY_SELECTOR)
    {
      // maybe a shared selector
      ret = maybeMkSkolemFun(op);
      if (!ret.isNull())
      {
        return ret;
      }
      unsigned index = DType::indexOf(op);
      const DType& dt = DType::datatypeOf(op);
      if (dt.isTuple())
      {
        indices.push_back(nm->mkConstInt(index));
        opName << "tuple.select";
      }
      else
      {
        unsigned cindex = DType::cindexOf(op);
        opName << dt[cindex][index].getSelector();
      }
    }
    else
    {
      opName << op;
    }
  }
  // we only use binary operators
  else
  {
    if (k == NEG)
    {
      opName << "u";
    }
    opName << printer::smt2::Smt2Printer::smtKindString(k);
    if (k == DIVISION_TOTAL || k == INTS_DIVISION_TOTAL
        || k == INTS_MODULUS_TOTAL)
    {
      opName << "_total";
    }
  }
  std::vector<Node> args(n.begin(), n.end());
  Node app = mkInternalApp(opName.str(), args, n.getType());
  Node ret;
  if (!indices.empty())
  {
    ret = mkInternalApp(opName.str(), indices, app.getOperator().getType());
  }
  else
  {
    ret = args.empty() ? app : app.getOperator();
  }
  Trace("alf-term-process-debug2") << "...return " << ret << std::endl;
  return ret;
}

size_t AlfNodeConverter::getOrAssignIndexForConst(Node v)
{
  Assert(v.isVar());
  std::map<Node, size_t>::iterator it = d_constIndex.find(v);
  if (it != d_constIndex.end())
  {
    return it->second;
  }
  size_t id = d_constIndex.size();
  d_constIndex[v] = id;
  return id;
}

}  // namespace proof
}  // namespace cvc5::internal
