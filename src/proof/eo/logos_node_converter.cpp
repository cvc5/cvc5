/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Logos node conversion
 */

#include "proof/eo/logos_node_converter.h"

#include <cstdlib>

#include "expr/aci_norm.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "util/bitvector.h"
#include "util/iand.h"
#include "util/indexed_root_predicate.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"

namespace cvc5::internal {
namespace proof {

LogosNodeConverter::LogosNodeConverter(NodeManager* nm) : EoNodeConverter(nm)
{
  d_constIdCount = 0;
  d_sortIdCount = 0;
}
LogosNodeConverter::~LogosNodeConverter() {}

bool LogosNodeConverter::shouldTraverse(Node n) { return true; }

Node LogosNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  TypeNode tn = n.getType();
  if (k == Kind::CONST_INTEGER)
  {
    std::stringstream ss;
    ss << "(Term.Numeral " << n << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k == Kind::CONST_RATIONAL)
  {
    std::stringstream ss;
    ss << "(Term.Rational " << n << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k == Kind::CONST_STRING)
  {
    std::stringstream ss;
    ss << "(Term.String " << n << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k == Kind::CONST_BITVECTOR)
  {
    BitVector b = n.getConst<BitVector>();
    ;
    std::stringstream ss;
    ss << "(Term.Binary " << b.getSize() << " " << b.getValue() << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k == Kind::CONST_BOOLEAN)
  {
    std::stringstream ss;
    ss << "(Term.Boolean " << (n.getConst<bool>() ? "true" : "false") << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k == Kind::APPLY_UF)
  {
    // convert to curried apply
    return convert(theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(n));
  }
  else if (k == Kind::HO_APPLY)
  {
    return mkInternalApp("Term.Apply", {n[0], n[1]}, n.getType());
  }
  else if (k == Kind::DISTINCT)
  {
    std::vector<Node> args(n.begin(), n.end());
    Node distinct = mkInternalSymbol(mkUserOpId("distinct"), tn);
    // it is :arg-list, so it must be a list of terms
    Node an = mkLogosTypedList(args, tn);
    return mkInternalApp("Term.Apply", {distinct, an}, tn);
  }
  else if (k == Kind::APPLY_CONSTRUCTOR || k == Kind::APPLY_TESTER
           || k == Kind::APPLY_SELECTOR || k == Kind::APPLY_UPDATER)
  {
    Node op = n.getOperator();
    unsigned index = DType::indexOf(op);
    const DType& dt = DType::datatypeOf(op);
    Node dtn = typeAsNode(dt.getTypeNode());
    Assert(dtn.getNumChildren() == 2);
    std::vector<Node> children;
    children.push_back(dtn[0]);
    children.push_back(dtn[1]);
    Node ret;
    if (k == Kind::APPLY_CONSTRUCTOR || k == Kind::APPLY_TESTER)
    {
      children.push_back(d_nm->mkConstInt(Rational(index)));
      ret = mkInternalApp("Term.DtCons", children, tn);
      if (k == Kind::APPLY_TESTER)
      {
        Node tester = mkInternalSymbol(mkUserOpId("is"), tn);
        ret = mkInternalApp("Term.Apply", {tester, ret}, tn);
      }
      for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
      {
        ret = mkInternalApp("Term.Apply", {ret, n[i]}, tn);
      }
    }
    else if (k == Kind::APPLY_SELECTOR || k == Kind::APPLY_UPDATER)
    {
      unsigned cindex = DType::cindexOf(op);
      children.push_back(d_nm->mkConstInt(Rational(index)));
      children.push_back(d_nm->mkConstInt(Rational(cindex)));
      ret = mkInternalApp("Term.DtSel", children, tn);
      if (k == Kind::APPLY_UPDATER)
      {
        Node update = mkInternalSymbol(mkUserOpId("update"), tn);
        ret = mkInternalApp("Term.Apply", {update, ret}, tn);
      }
      ret = mkInternalApp("Term.Apply", {ret, n[0]}, tn);
    }
    return ret;
  }
  else if (k == Kind::SEXPR || k == Kind::BOUND_VAR_LIST)
  {
    std::vector<Node> args(n.begin(), n.end());
    return mkLogosList(args, tn);
  }
  else if (n.getNumChildren() > 0)
  {
    std::stringstream ssOp;
    ssOp << printer::smt2::Smt2Printer::smtKindString(k);
    std::string id = mkUserOpId(cleanSmtId(ssOp.str()));
    Node nil = expr::getNullTerminator(d_nm, k, tn);
    if (!nil.isNull())
    {
      Node ret = convert(nil);
      Node f = mkInternalSymbol(id, tn);
      for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
      {
        size_t ii = (nchild - 1) - i;
        Node cc = mkInternalApp("Term.Apply", {f, convert(n[ii])}, tn);
        ret = mkInternalApp("Term.Apply", {cc, ret}, tn);
      }
      return ret;
    }
    // will convert to curried apply
    std::vector<Node> args(n.begin(), n.end());
    return convert(mkInternalApp(id, args, tn));
  }
  else if (n.isVar() && d_symbols.find(n) == d_symbols.end())
  {
    // don't change builtin datatype operators
    if (tn.isDatatypeConstructor() || tn.isDatatypeSelector()
        || tn.isDatatypeTester() || tn.isDatatypeUpdater())
    {
      return n;
    }
    d_constIdCount++;
    Trace("print-logos-debug")
        << "Introduce UConst " << d_constIdCount << " for " << n << std::endl;
    std::stringstream ss;
    ss << "Term.UConst " << d_constIdCount;
    Node tnn = typeAsNode(n.getType());
    return mkInternalApp(ss.str(), {tnn}, n.getType());
  }

  return n;
}

std::string LogosNodeConverter::replace_all(std::string str,
                        const std::string& from,
                        const std::string& to)
{
  if (from.empty()) return str;  // avoid infinite loop

  std::size_t pos = 0;
  while ((pos = str.find(from, pos)) != std::string::npos)
  {
    str.replace(pos, from.length(), to);
    pos += to.length();  // move past the replacement
  }
  return str;
}

std::string LogosNodeConverter::cleanSmtId(const std::string& id)
{
  // A generic method for turning an SMT-LIB identifier into a Lean identifier.
  std::string idc = id;
  idc = replace_all(idc, "++", "concat");
  idc = replace_all(idc, "+", "plus");
  idc = replace_all(idc, "-", "neg");
  idc = replace_all(idc, "*", "mult");
  idc = replace_all(idc, "=>", "imp");
  idc = replace_all(idc, "<=", "leq");
  idc = replace_all(idc, "<", "lt");
  idc = replace_all(idc, ">=", "geq");
  idc = replace_all(idc, ">", "gt");
  idc = replace_all(idc, "=", "eq");
  idc = replace_all(idc, "/", "qdiv");
  idc = replace_all(idc, "^", "exp");
  idc = replace_all(idc, ".", "_");
  idc = replace_all(idc, "@", "_at_");
  idc = replace_all(idc, "$", "__");
  return idc;
}

std::string LogosNodeConverter::mkUserOpId(const std::string& str)
{
  std::stringstream ss;
  ss << "(Term.UOp UserOp." << str << ")";
  return ss.str();
}

Node LogosNodeConverter::typeAsNode(TypeNode tn)
{
  // should always exist in the cache, as we always run types through
  // postConvertType before calling this method.
  std::map<TypeNode, Node>::const_iterator it = d_ltypeAsNode.find(tn);
  if (it != d_ltypeAsNode.end())
  {
    return it->second;
  }
  Node ret;
  if (tn.isUninterpretedSort())
  {
    d_sortIdCount++;
    std::stringstream ssi;
    ssi << d_sortIdCount;
    Node i = mkInternalSymbol(ssi.str(), d_nm->integerType());
    ret = mkInternalApp("Term.USort", {i}, d_sortType);
  }
  else if (tn.isDatatype())
  {
    std::unordered_set<TypeNode> scope;
    return typeAsNodeDatatype(tn.getDType(), scope);
  }
  else if (tn.getNumChildren() > 0)
  {
    size_t nchild = tn.getNumChildren();
    Node cons;
    if (tn.isFunction())
    {
      cons = mkInternalSymbol("Term.FunType", d_sortType);
    }
    else if (tn.isArray())
    {
      cons = mkInternalSymbol(mkUserOpId("Array"), d_sortType);
    }
    else if (tn.isSet())
    {
      cons = mkInternalSymbol(mkUserOpId("Set"), d_sortType);
    }
    else if (tn.isSequence())
    {
      cons = mkInternalSymbol(mkUserOpId("Seq"), d_sortType);
    }
    ret = typeAsNode(tn[nchild - 1]);
    for (size_t i = 1; i < nchild; i++)
    {
      size_t ii = (nchild - 1) - i;
      Node cc =
          mkInternalApp("Term.Apply", {cons, typeAsNode(tn[ii])}, d_sortType);
      ret = mkInternalApp("Term.Apply", {cc, ret}, tn);
    }
  }
  else
  {
    // dummy symbol whose name is the type printed
    std::stringstream ss;
    ss << tn;
    ret = mkInternalSymbol(mkUserOpId(ss.str()), d_sortType);
  }
  d_ltypeAsNode[tn] = ret;
  return ret;
}

Node LogosNodeConverter::typeAsNodeDatatype(const DType& dt,
                                            std::unordered_set<TypeNode>& scope)
{
  Node ret = mkInternalSymbol("Datatype.null", d_sortType);
  Node consUnit = mkInternalSymbol("DatatypeCons.unit", d_sortType);
  for (size_t j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
  {
    size_t jj = (ncons-1)-j;
    Node cons = consUnit;
    // traverse the argument types
    for (size_t k = 0, nargs = dt[jj].getNumArgs(); k < nargs; k++)
    {
      Node an;
      TypeNode argt = dt[jj].getArgType((nargs - 1) - k);
      if (argt.isDatatype())
      {
        if (scope.insert(argt).second)
        {
          an = typeAsNodeDatatype(argt.getDType(), scope);
          scope.erase(argt);
        }
        else
        {
          Node dtName = d_nm->mkConst(String(argt.getDType().getName()));
          an = mkInternalApp("Term.DatatypeTypeRef", {dtName}, d_sortType);
        }
      }
      else
      {
        an = typeAsNode(argt);
      }
      cons = mkInternalApp("DatatypeCons.cons", {an, cons}, d_sortType);
    }
    ret = mkInternalApp("Datatype.sum", {cons, ret}, d_sortType);
  }
  Node dtName = d_nm->mkConst(String(dt.getName()));
  ret = mkInternalApp("Term.DatatypeType", {dtName, ret}, d_sortType);
  return ret;
}

Node LogosNodeConverter::mkLogosList(const std::vector<Node>& args, const TypeNode& tn)
{
  Node ret = mkInternalSymbol("Term.__eo_List_nil", tn);
  Node cons = mkInternalSymbol("Term.__eo_List_cons", tn);
  // use generic list
  for (size_t i = 0, nchild = args.size(); i < nchild; i++)
  {
    size_t ii = (nchild - i) - 1;
    Node cc = mkInternalApp("Term.Apply", {cons, args[ii]}, tn);
    ret = mkInternalApp("Term.Apply", {cc, ret}, tn);
  }
  return ret;
}

Node LogosNodeConverter::mkLogosTypedList(const std::vector<Node>& args, const TypeNode& tn)
{
  Assert (!args.empty());
  Node nilu = mkInternalSymbol(mkUserOpId("_at__at_TypedList_nil"), tn);
  Node niltype = typeAsNode(args[0].getType());
  Node ret = mkInternalApp("Term.Apply", {nilu, niltype}, tn);
  Node cons = mkInternalSymbol(mkUserOpId("_at__at_TypedList_cons"), tn);
  // use generic list
  for (size_t i = 0, nchild = args.size(); i < nchild; i++)
  {
    size_t ii = (nchild - i) - 1;
    Node cc = mkInternalApp("Term.Apply", {cons, args[ii]}, tn);
    ret = mkInternalApp("Term.Apply", {cc, ret}, tn);
  }
  return ret;
}

}  // namespace proof
}  // namespace cvc5::internal
