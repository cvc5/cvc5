/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  NodeManager* nm = NodeManager::currentNM();
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
  TypeNode tn = n.getType();
  if (k == Kind::SKOLEM || k == Kind::DUMMY_SKOLEM)
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
  else if (k == Kind::BOUND_VARIABLE)
  {
    // note: we always distinguish variables, to ensure they do not have
    // names that are overloaded with user names
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
    size_t index = d_varIndex[sname];
    d_varIndex[sname]++;
    std::stringstream ssn;
    ssn << "@v." << index << "." << sname;
    return NodeManager::currentNM()->mkBoundVar(ssn.str(), tn);
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
      std::vector<Node> args;
      args.push_back(n.getOperator());
      args.insert(args.end(), n.begin(), n.end());
      return mkInternalApp("_", args, tn);
    }
  }
  else if (k == Kind::HO_APPLY)
  {
    return mkInternalApp("_", {n[0], n[1]}, tn);
  }
  else if (n.isClosure())
  {
    Node vl = n[0];
    // notice that intentionally we drop annotations here.
    std::vector<Node> args;
    // We take the *original* bound variable list, since variable names are
    // preserved in the translation; using the updated variable `@v.N.x`
    // would lead to using a variable named "@v.N.x" instead of "x", where
    // `@v.N.x` is a macro for the variable "x".
    args.push_back(n[0]);
    args.insert(args.end(),
                n.begin() + 1,
                n.begin() + getNumChildrenToProcessForClosure(k));
    return mkInternalApp(
        printer::smt2::Smt2Printer::smtKindString(k), args, tn);
  }
  else if (k == Kind::STORE_ALL)
  {
    Node t = typeAsNode(tn);
    ArrayStoreAll storeAll = n.getConst<ArrayStoreAll>();
    Node val = convert(storeAll.getValue());
    return mkInternalApp("store_all", {t, val}, tn);
  }
  else if (k == Kind::SET_EMPTY || k == Kind::SET_UNIVERSE
           || k == Kind::BAG_EMPTY || k == Kind::SEP_NIL)
  {
    Node t = typeAsNode(tn);
    return mkInternalApp(printer::smt2::Smt2Printer::smtKindString(k), {t}, tn);
  }
  else if (k == Kind::SET_INSERT)
  {
    std::vector<Node> iargs(n.begin(), n.begin() + n.getNumChildren() - 1);
    Node list = mkList(iargs);
    return mkInternalApp("set.insert", {list, n[n.getNumChildren() - 1]}, tn);
  }
  else if (k == Kind::CONST_SEQUENCE)
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
  else if (k == Kind::CONST_FINITE_FIELD)
  {
    const FiniteFieldValue& ffv = n.getConst<FiniteFieldValue>();
    Node v = convert(nm->mkConstInt(ffv.getValue()));
    Node fs = convert(nm->mkConstInt(ffv.getFieldSize()));
    return mkInternalApp("ff.value", {fs, v}, tn);
  }
  else if (k == Kind::FUNCTION_ARRAY_CONST)
  {
    // must convert to lambda and then run the conversion
    Node lam = theory::uf::FunctionConst::toLambda(n);
    Assert(!lam.isNull());
    return convert(lam);
  }
  else if (k == Kind::APPLY_TESTER || k == Kind::APPLY_UPDATER || k == Kind::NEG
           || k == Kind::DIVISION_TOTAL || k == Kind::INTS_DIVISION_TOTAL
           || k == Kind::INTS_MODULUS_TOTAL || k == Kind::APPLY_CONSTRUCTOR
           || k == Kind::APPLY_SELECTOR
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
      newArgs.insert(newArgs.end(), opc.begin(), opc.end());
      newArgs.insert(newArgs.end(), n.begin(), n.end());
      opc = opc.getOperator();
      std::stringstream ss;
      ss << opc;
      return mkInternalApp(ss.str(), newArgs, tn);
    }
    newArgs.push_back(opc);
    newArgs.insert(newArgs.end(), n.begin(), n.end());
    return nm->mkNode(Kind::APPLY_UF, newArgs);
  }
  else if (k == Kind::INDEXED_ROOT_PREDICATE)
  {
    const IndexedRootPredicate& irp =
        n.getOperator().getConst<IndexedRootPredicate>();
    std::vector<Node> newArgs;
    newArgs.push_back(nm->mkConstInt(irp.d_index));
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
    // dummy symbol, provide the return type
    Node tnn = typeAsNode(tn);
    std::stringstream ss;
    ss << "@fp." << printer::smt2::Smt2Printer::smtKindString(k);
    return mkInternalApp(ss.str(), {tnn}, tn);
  }
  else if (k == Kind::SEXPR || k == Kind::BOUND_VAR_LIST)
  {
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
      // This does not take a rounding mode, we change the smt2 syntax
      // to distinguish this case, similar to the case in getOperatorOfTerm
      // where it is processed as an indexed operator.
      std::vector<Node> children(n.begin(), n.end());
      return mkInternalApp("to_fp_bv", children, tn);
    }
  }
  else if (GenericOp::isIndexedOperatorKind(k))
  {
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
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  SkolemId sfi = SkolemId::NONE;
  Node cacheVal;
  TypeNode tn = k.getType();
  if (sm->isSkolemFunction(k, sfi, cacheVal))
  {
    if (isHandledSkolemId(sfi))
    {
      // convert every skolem function to its name applied to arguments
      std::stringstream ss;
      ss << "@" << sfi;
      std::vector<Node> args;
      if (cacheVal.getKind() == Kind::SEXPR)
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
      // must convert all arguments
      Node app = mkInternalApp(ss.str(), args, k.getType());
      return app;
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
  TypeNode tn = NodeManager::currentNM()->booleanType();
  // singleton lists are handled due to (@list x) ---> (@list x alf.nil)
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
    return nm->mkNode(Kind::APPLY_UF, aargs);
  }
  return mkInternalSymbol(name, ret, useRawSym);
}

Node AlfNodeConverter::getOperatorOfTerm(Node n, bool reqCast)
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
      if (k == Kind::APPLY_TESTER)
      {
        size_t cindex = DType::indexOf(op);
        const DType& dt = DType::datatypeOf(op);
        if (dt.isTuple())
        {
          opName << "is-tuple";
        }
        else if (dt.isNullable())
        {
          if (cindex == 0)
          {
            opName << "nullable.is_null";
          }
          else
          {
            opName << "nullable.is_some";
          }
        }
        else
        {
          opName << "is-" << dt[cindex].getConstructor();
        }
        indices.clear();
      }
      else if (k == Kind::APPLY_UPDATER)
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
      else
      {
        opName << dt[index].getConstructor();
      }
    }
    else if (k == Kind::APPLY_SELECTOR)
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
  else
  {
    bool isParameterized = false;
    if (reqCast)
    {
      // If the operator is a parameterized constant and reqCast is true,
      // then we must apply the parameters of the operator, e.g. such that
      // bvor becomes (alf._ bvor 32) where 32 is the bitwidth of the first
      // argument.
      if (k == Kind::BITVECTOR_ADD || k == Kind::BITVECTOR_MULT
          || k == Kind::BITVECTOR_OR || k == Kind::BITVECTOR_AND
          || k == Kind::BITVECTOR_XOR)
      {
        TypeNode tna = n[0].getType();
        indices.push_back(nm->mkConstInt(tna.getBitVectorSize()));
        isParameterized = true;
      }
      else if (k == Kind::FINITE_FIELD_ADD || k == Kind::FINITE_FIELD_BITSUM
               || k == Kind::FINITE_FIELD_MULT)
      {
        TypeNode tna = n[0].getType();
        indices.push_back(nm->mkConstInt(tna.getFfSize()));
        isParameterized = true;
      }
      else if (k == Kind::STRING_CONCAT)
      {
        // String concatenation is parameterized by the character type, which
        // is the "Char" type in the ALF signature for String (which note does
        // not exist internally in cvc5). Otherwise it is the sequence element
        // type.
        TypeNode tna = n[0].getType();
        Node cht;
        if (tna.isString())
        {
          cht = mkInternalSymbol("Char", d_sortType);
        }
        else
        {
          cht = typeAsNode(tna.getSequenceElementType());
        }
        indices.push_back(cht);
        isParameterized = true;
      }
    }
    if (isParameterized)
    {
      opName << "alf._";
      std::stringstream oppName;
      oppName << printer::smt2::Smt2Printer::smtKindString(k);
      Node opp = mkInternalSymbol(oppName.str(), n.getType());
      indices.insert(indices.begin(), opp);
    }
    else
    {
      opName << printer::smt2::Smt2Printer::smtKindString(k);
    }
  }
  std::vector<Node> args(n.begin(), n.end());
  Node app = mkInternalApp(opName.str(), args, n.getType());
  Node ret;
  if (!indices.empty())
  {
    ret = mkInternalApp(opName.str(), indices, app.getOperator().getType());
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
  if (reqCast)
  {
    // - prints as e.g. (alf.as - (-> Int Int)).
    if (k == Kind::NEG || k == Kind::SUB)
    {
      std::vector<Node> asChildren;
      asChildren.push_back(ret);
      asChildren.push_back(typeAsNode(ret.getType()));
      ret = mkInternalApp("alf.as", asChildren, n.getType());
    }
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

bool AlfNodeConverter::isHandledSkolemId(SkolemId id)
{
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
    case SkolemId::QUANTIFIERS_SKOLEMIZE:
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
