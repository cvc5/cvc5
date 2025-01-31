/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

#include "expr/aci_norm.h"
#include "expr/array_store_all.h"
#include "expr/cardinality_constraint.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/sequence.h"
#include "expr/sort_to_term.h"
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
#include "util/indexed_root_predicate.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace proof {

BaseAlfNodeConverter::BaseAlfNodeConverter(NodeManager* nm) : NodeConverter(nm)
{
}

AlfNodeConverter::AlfNodeConverter(NodeManager* nm) : BaseAlfNodeConverter(nm)
{
  d_sortType = nm->mkSort("sortType");
}

AlfNodeConverter::~AlfNodeConverter() {}

Node AlfNodeConverter::preConvert(Node n)
{
  // match is not supported in ALF syntax, we eliminate it at pre-order
  // traversal, which avoids type-checking errors during conversion, since e.g.
  // match case nodes are required but cannot be preserved
  if (n.getKind() == Kind::MATCH)
  {
    return theory::datatypes::DatatypesRewriter::expandMatch(n);
  }
  return n;
}

Node AlfNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  // we eliminate MATCH at preConvert above
  Assert(k != Kind::MATCH);
  Trace("alf-term-process-debug")
      << "postConvert " << n << " " << k << std::endl;
  if (k == Kind::ASCRIPTION_TYPE || k == Kind::RAW_SYMBOL)
  {
    // dummy node, return it
    return n;
  }
  // case for skolems, unhandled variables, and other unhandled terms
  // These should print as @const, or otherwise be printed as a skolem,
  // which may need further processing below. In the case of unhandled
  // terms (e.g. DT_SYGUS_EVAL), we prefer printing them as @const instead
  // of using their smt2 printer, which would lead to undeclared identifiers in
  // the proof.
  if (k == Kind::SKOLEM || k == Kind::DUMMY_SKOLEM || k == Kind::INST_CONSTANT
      || k == Kind::DT_SYGUS_EVAL)
  {
    TypeNode tn = n.getType();
    // constructors/selectors are represented by skolems, which are defined
    // symbols
    if (tn.isDatatypeConstructor() || tn.isDatatypeSelector()
        || tn.isDatatypeTester() || tn.isDatatypeUpdater())
    {
      // note these are not converted to their user named (cvc.) symbols here,
      // to avoid type errors when constructing terms for postConvert
      return n;
    }
    if (k == Kind::SKOLEM)
    {
      // might be a skolem function
      Node ns = maybeMkSkolemFun(n);
      if (!ns.isNull())
      {
        return ns;
      }
    }
    // Otherwise, it is an uncategorized skolem, must use a fresh variable.
    // This case will only apply for terms originating from places with no
    // proof support. Note it is not added as a declared variable, instead it
    // is used as (var N T) throughout.
    Node index = d_nm->mkConstInt(Rational(getOrAssignIndexForConst(n)));
    Node tc = typeAsNode(tn);
    return mkInternalApp("@const", {index, tc}, tn);
  }
  else if (k == Kind::BOUND_VARIABLE)
  {
    std::string sname;
    if (n.hasName())
    {
      // get its name if it has one
      sname = n.getName();
    }
    else
    {
      // otherwise invoke the printer to get its name
      std::stringstream ss;
      ss << n;
      sname = ss.str();
    }
    // A variable x of type T can unambiguously referred to as (@var "x" T),
    // which is a macro for (eo::var "x" T) in the cpc signature.
    // We convert to this representation here, which will often be letified.
    TypeNode tn = n.getType();
    std::vector<Node> args;
    Node nn = d_nm->mkConst(String(sname));
    args.push_back(nn);
    Node tnn = typeAsNode(tn);
    args.push_back(tnn);
    return mkInternalApp("@var", args, tn);
  }
  else if (k == Kind::VARIABLE)
  {
    // note that we do not handle overloading here
    return n;
  }
  else if (k == Kind::APPLY_UF)
  {
    // must ensure we print higher-order function applications with "_"
    if (!n.getOperator().isVar())
    {
    TypeNode tn = n.getType();
      std::vector<Node> args;
      args.push_back(n.getOperator());
      args.insert(args.end(), n.begin(), n.end());
      return mkInternalApp("_", args, tn);
    }
  }
  else if (k == Kind::HO_APPLY)
  {
    TypeNode tn = n.getType();
    return mkInternalApp("_", {n[0], n[1]}, tn);
  }
  else if (n.isClosure())
  {
    TypeNode tn = n.getType();
    Node vl = n[0];
    // Notice that intentionally we drop annotations here.
    // Additionally, it is important that we convert the closure to a
    // non-closure operator here, since we will be traversing over it
    // during letification.
    std::vector<Node> args;
    args.insert(args.end(),
                n.begin(),
                n.begin() + getNumChildrenToProcessForClosure(k));
    return mkInternalApp(
        printer::smt2::Smt2Printer::smtKindString(k), args, tn);
  }
  else if (k == Kind::STORE_ALL)
  {
    TypeNode tn = n.getType();
    Node t = typeAsNode(tn);
    ArrayStoreAll storeAll = n.getConst<ArrayStoreAll>();
    Node val = convert(storeAll.getValue());
    return mkInternalApp("store_all", {t, val}, tn);
  }
  else if (k == Kind::SET_EMPTY || k == Kind::SET_UNIVERSE
           || k == Kind::BAG_EMPTY || k == Kind::SEP_NIL)
  {
    TypeNode tn = n.getType();
    Node t = typeAsNode(tn);
    return mkInternalApp(printer::smt2::Smt2Printer::smtKindString(k), {t}, tn);
  }
  else if (k == Kind::SET_INSERT)
  {
    TypeNode tn = n.getType();
    std::vector<Node> iargs(n.begin(), n.begin() + n.getNumChildren() - 1);
    Node list = mkList(iargs);
    return mkInternalApp("set.insert", {list, n[n.getNumChildren() - 1]}, tn);
  }
  else if (k == Kind::CONST_SEQUENCE)
  {
    if (n.getConst<Sequence>().empty())
    {
      TypeNode tn = n.getType();
      Node t = typeAsNode(tn);
      return mkInternalApp("seq.empty", {t}, tn);
    }
    // otherwise must convert to term representation and convert
    Node cc = theory::strings::utils::mkConcatForConstSequence(n);
    return convert(cc);
  }
  else if (k == Kind::CONST_FINITE_FIELD)
  {
    TypeNode tn = n.getType();
    const FiniteFieldValue& ffv = n.getConst<FiniteFieldValue>();
    Node v = convert(d_nm->mkConstInt(ffv.getValue()));
    Node fs = convert(d_nm->mkConstInt(ffv.getFieldSize()));
    return mkInternalApp("ff.value", {fs, v}, tn);
  }
  else if (k == Kind::FUNCTION_ARRAY_CONST)
  {
    // must convert to lambda and then run the conversion
    Node lam = theory::uf::FunctionConst::toLambda(n);
    Assert(!lam.isNull());
    return convert(lam);
  }
  else if (k == Kind::APPLY_CONSTRUCTOR)
  {
    Node opc = getOperatorOfTerm(n);
    if (n.getNumChildren() == 0)
    {
      return opc;
    }
    std::vector<Node> newArgs;
    newArgs.push_back(opc);
    newArgs.insert(newArgs.end(), n.begin(), n.end());
    Node ret = d_nm->mkNode(Kind::APPLY_UF, newArgs);
    return convert(ret);
  }
  else if (k == Kind::APPLY_TESTER || k == Kind::APPLY_UPDATER || k == Kind::NEG
           || k == Kind::DIVISION_TOTAL || k == Kind::INTS_DIVISION_TOTAL
           || k == Kind::INTS_MODULUS_TOTAL || k == Kind::APPLY_SELECTOR
           || k == Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV)
  {
    // kinds where the operator may be different
    Node opc = getOperatorOfTerm(n);
    if (n.getNumChildren() == 0)
    {
      return opc;
    }
    std::vector<Node> newArgs;
    if (opc.getNumChildren() > 0)
    {
      TypeNode tn = n.getType();
      newArgs.insert(newArgs.end(), opc.begin(), opc.end());
      newArgs.insert(newArgs.end(), n.begin(), n.end());
      opc = opc.getOperator();
      std::stringstream ss;
      ss << opc;
      return mkInternalApp(ss.str(), newArgs, tn);
    }
    newArgs.push_back(opc);
    newArgs.insert(newArgs.end(), n.begin(), n.end());
    return d_nm->mkNode(Kind::APPLY_UF, newArgs);
  }
  else if (k == Kind::INDEXED_ROOT_PREDICATE)
  {
    TypeNode tn = n.getType();
    const IndexedRootPredicate& irp =
        n.getOperator().getConst<IndexedRootPredicate>();
    std::vector<Node> newArgs;
    newArgs.push_back(d_nm->mkConstInt(irp.d_index));
    newArgs.insert(newArgs.end(), n.begin(), n.end());
    return mkInternalApp("@indexed_root_predicate", newArgs, tn);
  }
  else if (k == Kind::FLOATINGPOINT_COMPONENT_NAN
           || k == Kind::FLOATINGPOINT_COMPONENT_INF
           || k == Kind::FLOATINGPOINT_COMPONENT_ZERO
           || k == Kind::FLOATINGPOINT_COMPONENT_SIGN
           || k == Kind::FLOATINGPOINT_COMPONENT_EXPONENT
           || k == Kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND)
  {
    TypeNode tn = n.getType();
    // dummy symbol, provide the return type
    Node tnn = typeAsNode(tn);
    std::stringstream ss;
    ss << printer::smt2::Smt2Printer::smtKindString(k);
    return mkInternalApp(ss.str(), {tnn}, tn);
  }
  else if (k == Kind::SEXPR || k == Kind::BOUND_VAR_LIST)
  {
    TypeNode tn = n.getType();
    // use generic list
    std::vector<Node> args;
    args.insert(args.end(), n.begin(), n.end());
    return mkInternalApp("@list", args, tn);
  }
  else if (k == Kind::APPLY_INDEXED_SYMBOLIC)
  {
    Kind okind = n.getOperator().getConst<GenericOp>().getKind();
    if (okind == Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV)
    {
      TypeNode tn = n.getType();
      // This does not take a rounding mode, we change the smt2 syntax
      // to distinguish this case, similar to the case in getOperatorOfTerm
      // where it is processed as an indexed operator.
      std::vector<Node> children(n.begin(), n.end());
      return mkInternalApp("to_fp_bv", children, tn);
    }
  }
  else if (k == Kind::BITVECTOR_EAGER_ATOM)
  {
    // For now, we explicity remove the application.
    // https://github.com/cvc5/cvc5-wishues/issues/156: if the smt2 printer
    // is refactored to silently ignore this kind, this case can be deleted.
    return n[0];
  }
  else if (GenericOp::isIndexedOperatorKind(k))
  {
    TypeNode tn = n.getType();
    // return app of?
    std::vector<Node> args =
        GenericOp::getIndicesForOperator(k, n.getOperator());
    if (k == Kind::RELATION_GROUP || k == Kind::TABLE_GROUP)
    {
      Node list = mkList(args);
      std::vector<Node> children;
      children.push_back(list);
      children.insert(children.end(), n.begin(), n.end());
      return mkInternalApp(
          printer::smt2::Smt2Printer::smtKindString(k), children, tn);
    }
    args.insert(args.end(), n.begin(), n.end());
    return mkInternalApp(
        printer::smt2::Smt2Printer::smtKindString(k), args, tn);
  }
  return n;
}

bool AlfNodeConverter::shouldTraverse(Node n)
{
  Kind k = n.getKind();
  // don't convert instantiation pattern list directly
  if (k == Kind::INST_PATTERN_LIST)
  {
    return false;
  }
  // should not traverse internal applications
  if (k == Kind::APPLY_UF)
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
  SkolemManager* sm = d_nm->getSkolemManager();
  SkolemId sfi = SkolemId::NONE;
  Node cacheVal;
  TypeNode tn = k.getType();
  if (sm->isSkolemFunction(k, sfi, cacheVal))
  {
    if (isHandledSkolemId(sfi))
    {
      if (!cacheVal.isNull())
      {
        std::vector<Node> vals;
        if (cacheVal.getKind() == Kind::SEXPR)
        {
          vals.insert(vals.end(), cacheVal.begin(), cacheVal.end());
        }
        else
        {
          vals.push_back(cacheVal);
        }
        bool hasChanged = false;
        for (Node& v : vals)
        {
          Node orig = v;
          v = convert(v);
          hasChanged = hasChanged || v != orig;
        }
        // if an index term changed, we have to construct a new skolem
        if (hasChanged)
        {
          // construct an internal app instead
          std::stringstream ss;
          ss << "@" << sfi;
          return mkInternalApp(ss.str(), vals, k.getType());
        }
      }
      // otherwise we return itself, this will be printed in its full
      // definition since applyPrintSkolemDefinitions is set to true
      return k;
    }
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

size_t AlfNodeConverter::getNumChildrenToProcessForClosure(Kind k) const
{
  return k == Kind::SET_COMPREHENSION ? 3 : 2;
}


Node AlfNodeConverter::mkList(const std::vector<Node>& args)
{
  Assert(!args.empty());
  TypeNode tn = d_nm->booleanType();
  // singleton lists are handled due to (@list x) ---> (@list x eo::nil)
  return mkInternalApp("@list", args, tn);
}

Node AlfNodeConverter::mkInternalSymbol(const std::string& name,
                                        TypeNode tn,
                                        bool useRawSym)
{
  // use raw symbol so that it is never quoted
  Node sym = useRawSym ? NodeManager::mkRawSymbol(name, tn)
                       : NodeManager::mkBoundVar(name, tn);
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
    TypeNode atype = d_nm->mkFunctionType(argTypes, ret);
    Node op = mkInternalSymbol(name, atype, useRawSym);
    std::vector<Node> aargs;
    aargs.push_back(op);
    aargs.insert(aargs.end(), args.begin(), args.end());
    return d_nm->mkNode(Kind::APPLY_UF, aargs);
  }
  return mkInternalSymbol(name, ret, useRawSym);
}

Node AlfNodeConverter::getOperatorOfTerm(Node n)
{
  Assert(n.hasOperator());
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
      if (k == Kind::APPLY_TESTER)
      {
        indices.clear();
        size_t cindex = DType::indexOf(op);
        const DType& dt = DType::datatypeOf(op);
        opName << "is";
        if (dt.isTuple())
        {
          std::string tname = dt[0].getNumArgs() == 0 ? "tuple.unit" : "tuple";
          Node tsym = mkInternalSymbol(tname, dt[0].getConstructor().getType());
          indices.push_back(tsym);
        }
        else
        {
          indices.push_back(dt[cindex].getConstructor());
        }
      }
      else if (k == Kind::APPLY_UPDATER)
      {
        indices.clear();
        size_t index = DType::indexOf(op);
        const DType& dt = DType::datatypeOf(op);
        size_t cindex = DType::cindexOf(op);
        opName << "update";
        if (dt.isTuple())
        {
          std::vector<Node> args;
          args.push_back(d_nm->mkConstInt(cindex));
          Node ssym = mkInternalApp(
              "tuple.select", args, dt[cindex][index].getSelector().getType());
          indices.push_back(ssym);
        }
        else
        {
          indices.push_back(dt[cindex][index].getSelector());
        }
      }
      else if (k == Kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV)
      {
        // this does not take a rounding mode, we change the smt2 syntax
        // to distinguish this case.
        opName << "to_fp_bv";
      }
      else
      {
        opName << printer::smt2::Smt2Printer::smtKindString(k);
      }
    }
    else if (k == Kind::APPLY_CONSTRUCTOR)
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
      else if ((dt.isNullable() && index == 0)
               || (dt.isParametric()
                   && isAmbiguousDtConstructor(dt[index].getConstructor())))
      {
        // ambiguous if nullable.null or a user provided ambiguous datatype
        // constructor
        opName << "as";
        indices.push_back(dt[index].getConstructor());
        // tn is the return type
        TypeNode tn = n.getType();
        indices.push_back(typeAsNode(tn));
      }
      else
      {
        opName << dt[index].getConstructor();
      }
    }
    else if (k == Kind::APPLY_SELECTOR)
    {
      // maybe a shared selector
      if (op.getSkolemId() == SkolemId::SHARED_SELECTOR)
      {
        std::vector<Node> kindices = op.getSkolemIndices();
        opName << "@shared_selector";
        indices.push_back(
            typeAsNode(kindices[0].getConst<SortToTerm>().getType()));
        indices.push_back(
            typeAsNode(kindices[1].getConst<SortToTerm>().getType()));
        indices.push_back(kindices[2]);
      }
      else
      {
        unsigned index = DType::indexOf(op);
        const DType& dt = DType::datatypeOf(op);
        if (dt.isTuple())
        {
          indices.push_back(d_nm->mkConstInt(index));
          opName << "tuple.select";
        }
        else
        {
          unsigned cindex = DType::cindexOf(op);
          opName << dt[cindex][index].getSelector();
        }
      }
    }
    else
    {
      opName << op;
    }
  }
  else
  {
    opName << printer::smt2::Smt2Printer::smtKindString(k);
  }
  std::vector<Node> args(n.begin(), n.end());
  Node app = mkInternalApp(opName.str(), args, n.getType());
  Node ret;
  if (!indices.empty())
  {
    Node op = args.empty() ? app : app.getOperator();
    ret = mkInternalApp(opName.str(), indices, op.getType());
  }
  else if (n.isClosure())
  {
    // The operator of a closure by convention includes its variable list.
    // This is required for cong over binders. We do not convert the variable
    // list here, for the same reason as why it is not converted in convert(..).
    Node vl = n[0];
    // the type of this term is irrelevant, just use vl's type
    ret = mkInternalApp(
        printer::smt2::Smt2Printer::smtKindString(k), {vl}, vl.getType());
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
  std::map<Node, size_t>::iterator it = d_constIndex.find(v);
  if (it != d_constIndex.end())
  {
    return it->second;
  }
  size_t id = d_constIndex.size();
  d_constIndex[v] = id;
  return id;
}

bool AlfNodeConverter::isAmbiguousDtConstructor(const Node& op)
{
  std::map<Node, bool>::iterator it = d_ambDt.find(op);
  if (it != d_ambDt.end())
  {
    return it->second;
  }
  bool ret = false;
  TypeNode tn = op.getType();
  Trace("alf-amb-dt") << "Ambiguous datatype constructor? " << op << " " << tn
                      << std::endl;
  size_t nchild = tn.getNumChildren();
  Assert(nchild > 0);
  std::unordered_set<TypeNode> atypes;
  for (size_t i = 0; i < nchild - 1; i++)
  {
    expr::getComponentTypes(tn[i], atypes);
  }
  const DType& dt = DType::datatypeOf(op);
  std::vector<TypeNode> params = dt.getParameters();
  for (const TypeNode& p : params)
  {
    if (atypes.find(p) == atypes.end())
    {
      Trace("alf-amb-dt") << "...yes since " << p << " not contained"
                          << std::endl;
      ret = true;
      break;
    }
  }
  Trace("alf-amb-dt") << "...returns " << ret << std::endl;
  d_ambDt[op] = ret;
  return ret;
}

bool AlfNodeConverter::isHandledSkolemId(SkolemId id)
{
  // Note we don't handle skolems that take types as arguments yet.
  switch (id)
  {
    case SkolemId::PURIFY:
    case SkolemId::ARRAY_DEQ_DIFF:
    case SkolemId::BV_EMPTY:
    case SkolemId::DIV_BY_ZERO:
    case SkolemId::INT_DIV_BY_ZERO:
    case SkolemId::MOD_BY_ZERO:
    case SkolemId::TRANSCENDENTAL_PURIFY:
    case SkolemId::TRANSCENDENTAL_PURIFY_ARG:
    case SkolemId::ARITH_VTS_DELTA:
    case SkolemId::ARITH_VTS_DELTA_FREE:
    case SkolemId::QUANTIFIERS_SKOLEMIZE:
    case SkolemId::SETS_DEQ_DIFF:
    case SkolemId::STRINGS_NUM_OCCUR:
    case SkolemId::STRINGS_NUM_OCCUR_RE:
    case SkolemId::STRINGS_OCCUR_INDEX:
    case SkolemId::STRINGS_OCCUR_INDEX_RE:
    case SkolemId::STRINGS_OCCUR_LEN_RE:
    case SkolemId::STRINGS_DEQ_DIFF:
    case SkolemId::STRINGS_REPLACE_ALL_RESULT:
    case SkolemId::STRINGS_ITOS_RESULT:
    case SkolemId::STRINGS_STOI_RESULT:
    case SkolemId::STRINGS_STOI_NON_DIGIT:
    case SkolemId::RE_FIRST_MATCH_PRE:
    case SkolemId::RE_FIRST_MATCH:
    case SkolemId::RE_FIRST_MATCH_POST:
    case SkolemId::RE_UNFOLD_POS_COMPONENT:
    case SkolemId::BAGS_DEQ_DIFF:
    case SkolemId::BAGS_DISTINCT_ELEMENTS:
    case SkolemId::BAGS_MAP_PREIMAGE_INJECTIVE:
    case SkolemId::BAGS_DISTINCT_ELEMENTS_SIZE:
    case SkolemId::BAGS_MAP_SUM:
    case SkolemId::TABLES_GROUP_PART:
    case SkolemId::TABLES_GROUP_PART_ELEMENT: return true;
    default: break;
  }
  return false;
}

}  // namespace proof
}  // namespace cvc5::internal
