/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of ALF node conversion
 */

#include "proof/alf/logos_lean_node_converter.h"
#include <cstdlib>

#include "expr/aci_norm.h"
#include "util/bitvector.h"
#include "util/iand.h"
#include "util/indexed_root_predicate.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "printer/smt2/smt2_printer.h"

namespace cvc5::internal {
namespace proof {

LogosLeanNodeConverter::LogosLeanNodeConverter(NodeManager* nm)
    : AlfNodeConverter(nm)
{
  d_constIdCount = 0;
  d_sortIdCount = 0;
}
LogosLeanNodeConverter::~LogosLeanNodeConverter() {}

bool LogosLeanNodeConverter::shouldTraverse(Node n)
{
  return true;
}

Node LogosLeanNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  TypeNode tn = n.getType();
  if (k==Kind::CONST_INTEGER)
  {
    std::stringstream ss;
    ss << "(Term.Numeral " << n << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k==Kind::CONST_RATIONAL)
  {
    std::stringstream ss;
    ss << "(Term.Rational " << n << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k==Kind::CONST_STRING)
  {
    std::stringstream ss;
    ss << "(Term.String " << n << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k==Kind::CONST_BITVECTOR)
  {
    BitVector b = n.getConst<BitVector>();;
    std::stringstream ss;
    ss << "(Term.Binary " << b.getSize() << " " << b.getValue() << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k==Kind::CONST_BOOLEAN)
  {
    std::stringstream ss;
    ss << "(Term.Boolean " << (n.getConst<bool>() ? "true" : "false") << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k==Kind::APPLY_UF)
  {
    // convert to curried apply
    return convert(theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(n));
  }
  else if (k==Kind::HO_APPLY)
  {
    return mkInternalApp("Term.Apply", {n[0], n[1]}, n.getType());
  }
  else if (k==Kind::BOUND_VAR_LIST)
  {
    // TODO
  }
  else if (k==Kind::FORALL || k==Kind::EXISTS || k==Kind::LAMBDA)
  {
    // TODO
  }
  else if (k==Kind::APPLY_CONSTRUCTOR)
  {
  }
  else if (k==Kind::APPLY_TESTER)
  {
  }
  else if (k==Kind::APPLY_SELECTOR)
  {
  }
  else if (k == Kind::SEXPR || k == Kind::BOUND_VAR_LIST)
  {
    Node ret = mkInternalSymbol("Term.__eo_List_nil", tn);
    Node cons = mkInternalSymbol("Term.__eo_List_cons", tn);
    // use generic list
    for (size_t i=0, nchild=n.getNumChildren(); i<nchild; i++)
    {
      size_t ii = (nchild-i)-1;
      Node cc = mkInternalApp("Term.Apply", {cons, n[ii]}, tn);
      ret = mkInternalApp("Term.Apply", {cc, ret}, tn);
    }
    return ret;
  }
  else if (n.getNumChildren()>0)
  {
    std::stringstream ssOp;
    ssOp << printer::smt2::Smt2Printer::smtKindString(k);
    std::string id = "Term." + cleanSmtId(ssOp.str());
    Node nil = expr::getNullTerminator(d_nm, k, tn);
    if (!nil.isNull())
    {
      Node ret = convert(nil);
      Node f = mkInternalSymbol(id, tn);
      for (size_t i=0, nchild=n.getNumChildren(); i<nchild; i++)
      {
        size_t ii = (nchild-1)-i;
        Node cc = mkInternalApp("Term.Apply", {f, convert(n[ii])}, tn);
        ret = mkInternalApp("Term.Apply", {cc, ret}, tn);
      }
      return ret;
    }
    // will convert to curried apply
    std::vector<Node> args(n.begin(), n.end());
    return convert(mkInternalApp(id, args, tn));
  }
  else if (n.isVar() && d_symbols.find(n)==d_symbols.end())
  {
    d_constIdCount++;
    Trace("print-logos-debug") << "Introduce UConst " << d_constIdCount << " for " << n << std::endl;
    std::stringstream ss;
    ss << "Term.UConst " << d_constIdCount;
    Node tnn = typeAsNode(n.getType());
    return mkInternalApp(ss.str(), {tnn}, n.getType());
  }
  
  return n;
}

std::string replace_all(std::string str,
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

std::string LogosLeanNodeConverter::cleanSmtId(const std::string& id)
{
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

Node LogosLeanNodeConverter::typeAsNode(TypeNode tn)
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
  else if (tn.getNumChildren()>0)
  {
    size_t nchild = tn.getNumChildren();
    Node cons;
    if (tn.isFunction())
    {
      cons = mkInternalSymbol("Term.FunType", d_sortType);
    }
    else if (tn.isArray())
    {
      cons = mkInternalSymbol("Term.Array", d_sortType);
    }
    else if (tn.isSet())
    {
      cons = mkInternalSymbol("Term.Set", d_sortType);
    }
    else if (tn.isSequence())
    {
      cons = mkInternalSymbol("Term.Seq", d_sortType);
    }
    ret = typeAsNode(tn[nchild-1]);
    for (size_t i=1; i<nchild; i++)
    {
      size_t ii = (nchild-1)-i;
      Node cc = mkInternalApp("Term.Apply", {cons, typeAsNode(tn[ii])}, d_sortType);
      ret = mkInternalApp("Term.Apply", {cc, ret}, tn);
    }
  }
  else
  {
    // dummy symbol whose name is the type printed
    // this suffices since ALF faithfully represents all types.
    // note we cannot letify types (same as in SMT-LIB)
    std::stringstream ss;
    ss << "Term." << tn;
    ret = mkInternalSymbol(ss.str(), d_sortType);
  }
  d_ltypeAsNode[tn] = ret;
  return ret;
}

}  // namespace proof
}  // namespace cvc5::internal
