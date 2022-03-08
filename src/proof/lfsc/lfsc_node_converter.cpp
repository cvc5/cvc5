/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of LFSC node conversion
 */

#include "proof/lfsc/lfsc_node_converter.h"

#include <iomanip>
#include <sstream>

#include "expr/array_store_all.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/nary_term_util.h"
#include "expr/node_manager_attributes.h"
#include "expr/sequence.h"
#include "expr/skolem_manager.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/strings/word.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "util/bitvector.h"
#include "util/iand.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace proof {

LfscNodeConverter::LfscNodeConverter()
{
  NodeManager* nm = NodeManager::currentNM();
  d_arrow = nm->mkSortConstructor("arrow", 2);

  d_sortType = nm->mkSort("sortType");
  // the embedding of arrow into Node, which is binary constructor over sorts
  TypeNode anfType = nm->mkFunctionType({d_sortType, d_sortType}, d_sortType);
  d_typeAsNode[d_arrow] = getSymbolInternal(FUNCTION_TYPE, anfType, "arrow");

  TypeNode intType = nm->integerType();
  TypeNode arrType = nm->mkFunctionType({d_sortType, d_sortType}, d_sortType);
  d_typeKindToNodeCons[ARRAY_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, arrType, "Array");
  TypeNode bvType = nm->mkFunctionType(intType, d_sortType);
  d_typeKindToNodeCons[BITVECTOR_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, bvType, "BitVec");
  TypeNode fpType = nm->mkFunctionType({intType, intType}, d_sortType);
  d_typeKindToNodeCons[FLOATINGPOINT_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, fpType, "FloatingPoint");
  TypeNode setType = nm->mkFunctionType(d_sortType, d_sortType);
  d_typeKindToNodeCons[SET_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, setType, "Set");
  d_typeKindToNodeCons[BAG_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, setType, "Bag");
  d_typeKindToNodeCons[SEQUENCE_TYPE] =
      getSymbolInternal(FUNCTION_TYPE, setType, "Seq");
}

Node LfscNodeConverter::preConvert(Node n)
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

Node LfscNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  if (k == ASCRIPTION_TYPE)
  {
    // dummy node, return it
    return n;
  }
  TypeNode tn = n.getType();
  Trace("lfsc-term-process-debug")
      << "postConvert " << n << " " << k << std::endl;
  if (k == BOUND_VARIABLE)
  {
    // ignore internally generated symbols
    if (d_symbols.find(n) != d_symbols.end())
    {
      return n;
    }
    // bound variable v is (bvar x T)
    TypeNode intType = nm->integerType();
    Node x = nm->mkConstInt(Rational(getOrAssignIndexForVar(n)));
    Node tc = typeAsNode(convertType(tn));
    TypeNode ftype = nm->mkFunctionType({intType, d_sortType}, tn);
    Node bvarOp = getSymbolInternal(k, ftype, "bvar");
    return nm->mkNode(APPLY_UF, bvarOp, x, tc);
  }
  else if (k == SKOLEM || k == BOOLEAN_TERM_VARIABLE)
  {
    // constructors/selectors are represented by skolems, which are defined
    // symbols
    if (tn.isConstructor() || tn.isSelector() || tn.isTester()
        || tn.isUpdater())
    {
      // note these are not converted to their user named (cvc.) symbols here,
      // to avoid type errors when constructing terms for postConvert
      return n;
    }
    // skolems v print as their witness forms
    // v is (skolem W) where W is the original or witness form of v
    Node wi = SkolemManager::getOriginalForm(n);
    if (wi == n)
    {
      // if it is not a purification skolem, maybe it is a witness skolem
      wi = SkolemManager::getWitnessForm(n);
    }
    if (!wi.isNull() && wi != n)
    {
      Trace("lfsc-term-process-debug") << "...witness form " << wi << std::endl;
      wi = convert(wi);
      Trace("lfsc-term-process-debug")
          << "...converted witness for " << wi << std::endl;
      TypeNode ftype = nm->mkFunctionType(tn, tn);
      Node skolemOp = getSymbolInternal(k, ftype, "skolem");
      return nm->mkNode(APPLY_UF, skolemOp, wi);
    }
    // might be a skolem function
    Node ns = maybeMkSkolemFun(n);
    if (!ns.isNull())
    {
      return ns;
    }
    // Otherwise, it is an uncategorized skolem, must use a fresh variable.
    // This case will only apply for terms originating from places with no
    // proof support.
    TypeNode intType = nm->integerType();
    TypeNode varType = nm->mkFunctionType({intType, d_sortType}, tn);
    Node var = mkInternalSymbol("var", varType);
    Node index = nm->mkConstInt(Rational(getOrAssignIndexForVar(n)));
    Node tc = typeAsNode(convertType(tn));
    return nm->mkNode(APPLY_UF, var, index, tc);
  }
  else if (n.isVar())
  {
    return mkInternalSymbol(getNameForUserNameOf(n), tn);
  }
  else if (k == APPLY_UF)
  {
    return convert(theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(n));
  }
  else if (k == APPLY_CONSTRUCTOR || k == APPLY_SELECTOR || k == APPLY_TESTER
           || k == APPLY_SELECTOR_TOTAL || k == APPLY_UPDATER)
  {
    // must convert other kinds of apply to functions, since we convert to
    // HO_APPLY
    Node opc = getOperatorOfTerm(n, true);
    if (n.getNumChildren() == 0)
    {
      return opc;
    }
    std::vector<Node> children;
    children.push_back(opc);
    children.insert(children.end(), n.begin(), n.end());
    return postConvert(nm->mkNode(APPLY_UF, children));
  }
  else if (k == HO_APPLY)
  {
    std::vector<TypeNode> argTypes;
    argTypes.push_back(n[0].getType());
    argTypes.push_back(n[1].getType());
    TypeNode tnh = nm->mkFunctionType(argTypes, tn);
    Node hconstf = getSymbolInternal(k, tnh, "apply");
    return nm->mkNode(APPLY_UF, hconstf, n[0], n[1]);
  }
  else if (k == CONST_RATIONAL || k == CONST_INTEGER || k == CAST_TO_REAL)
  {
    if (k == CAST_TO_REAL)
    {
      // already converted
      do
      {
        n = n[0];
        Assert(n.getKind() == APPLY_UF || n.getKind() == CONST_RATIONAL
               || n.getKind() == CONST_INTEGER);
      } while (n.getKind() != CONST_RATIONAL && n.getKind() != CONST_INTEGER);
    }
    TypeNode tnv = nm->mkFunctionType(tn, tn);
    Node rconstf;
    Node arg;
    Rational r = n.getConst<Rational>();
    if (tn.isInteger())
    {
      rconstf = getSymbolInternal(k, tnv, "int");
      if (r.sgn() == -1)
      {
        // use LFSC syntax for mpz negation
        Node mpzn = getSymbolInternal(k, nm->mkFunctionType(tn, tn), "~");
        arg = nm->mkNode(APPLY_UF, mpzn, nm->mkConstInt(r.abs()));
      }
      else
      {
        arg = n;
      }
    }
    else
    {
      rconstf = getSymbolInternal(k, tnv, "real");
      // ensure rationals are printed properly here using mpq syntax
      // Note that inconvieniently, LFSC uses (non-sexpr) syntax n/m for
      // constant rationals, hence we must use a string
      std::stringstream ss;
      ss << "__LFSC_TMP" << r.getNumerator().abs() << "/" << r.getDenominator();
      arg = mkInternalSymbol(ss.str(), tn);
      // negative (~ n/m)
      if (r.sgn() == -1)
      {
        Node mpzn = getSymbolInternal(k, nm->mkFunctionType(tn, tn), "~");
        arg = nm->mkNode(APPLY_UF, mpzn, arg);
      }
    }
    return nm->mkNode(APPLY_UF, rconstf, arg);
  }
  else if (k == CONST_BITVECTOR)
  {
    TypeNode btn = nm->booleanType();
    TypeNode tnv = nm->mkFunctionType(btn, tn);
    TypeNode btnv = nm->mkFunctionType({btn, btn}, btn);
    BitVector bv = n.getConst<BitVector>();
    size_t w = bv.getSize();
    Node ret = getSymbolInternal(k, btn, "bvn");
    Node b0 = getSymbolInternal(k, btn, "b0");
    Node b1 = getSymbolInternal(k, btn, "b1");
    Node bvc = getSymbolInternal(k, btnv, "bvc");
    for (size_t i = 0; i < w; i++)
    {
      Node arg = bv.isBitSet((w - 1) - i) ? b1 : b0;
      ret = nm->mkNode(APPLY_UF, bvc, arg, ret);
    }
    Node bconstf = getSymbolInternal(k, tnv, "bv");
    return nm->mkNode(APPLY_UF, bconstf, ret);
  }
  else if (k == CONST_STRING)
  {
    //"" is emptystr
    //"A" is (char 65)
    //"ABC" is (str.++ (char 65) (str.++ (char 66) (str.++ (char 67) emptystr)))
    std::vector<Node> charVec;
    getCharVectorInternal(n, charVec);
    Assert(!charVec.empty());
    if (charVec.size() == 1)
    {
      // handles empty string and singleton character
      return charVec[0];
    }
    std::reverse(charVec.begin(), charVec.end());
    Node ret = postConvert(getNullTerminator(STRING_CONCAT, tn));
    for (size_t i = 0, size = charVec.size(); i < size; i++)
    {
      ret = nm->mkNode(STRING_CONCAT, charVec[i], ret);
    }
    return ret;
  }
  else if (k == CONST_SEQUENCE)
  {
    const std::vector<Node>& charVec = n.getConst<Sequence>().getVec();
    TypeNode etype = nm->mkFunctionType(d_sortType, tn);
    Node ret = getSymbolInternal(k, etype, "seq.empty");
    ret = nm->mkNode(APPLY_UF, ret, typeAsNode(convertType(tn)));
    std::vector<Node> vecu;
    for (size_t i = 0, size = charVec.size(); i < size; i++)
    {
      Node u = nm->mkNode(SEQ_UNIT, postConvert(charVec[size - (i + 1)]));
      if (size == 1)
      {
        // singleton case
        return u;
      }
      ret = nm->mkNode(STRING_CONCAT, u, ret);
    }
    return ret;
  }
  else if (k == STORE_ALL)
  {
    Node t = typeAsNode(convertType(tn));
    TypeNode caRetType = nm->mkFunctionType(tn.getArrayConstituentType(), tn);
    TypeNode catype = nm->mkFunctionType(d_sortType, caRetType);
    Node bconstf = getSymbolInternal(k, catype, "array_const");
    Node f = nm->mkNode(APPLY_UF, bconstf, t);
    ArrayStoreAll storeAll = n.getConst<ArrayStoreAll>();
    return nm->mkNode(APPLY_UF, f, convert(storeAll.getValue()));
  }
  else if (k == GEQ || k == GT || k == LEQ || k == LT || k == SUB
           || k == DIVISION || k == DIVISION_TOTAL || k == INTS_DIVISION
           || k == INTS_DIVISION_TOTAL || k == INTS_MODULUS
           || k == INTS_MODULUS_TOTAL || k == NEG || k == POW
           || isIndexedOperatorKind(k))
  {
    // must give special names to SMT-LIB operators with arithmetic subtyping
    // note that SUB is not n-ary
    // get the macro-apply version of the operator
    Node opc = getOperatorOfTerm(n, true);
    std::vector<Node> children;
    children.push_back(opc);
    children.insert(children.end(), n.begin(), n.end());
    return nm->mkNode(APPLY_UF, children);
  }
  else if (k == SET_EMPTY || k == SET_UNIVERSE || k == BAG_EMPTY)
  {
    Node t = typeAsNode(convertType(tn));
    TypeNode etype = nm->mkFunctionType(d_sortType, tn);
    Node ef = getSymbolInternal(
        k,
        etype,
        k == SET_EMPTY ? "set.empty"
                       : (k == SET_UNIVERSE ? "set.universe" : "bag.empty"));
    return nm->mkNode(APPLY_UF, ef, t);
  }
  else if (n.isClosure())
  {
    // (forall ((x1 T1) ... (xn Tk)) P) is
    // ((forall x1 T1) ((forall x2 T2) ... ((forall xk Tk) P))). We use
    // SEXPR to do this, which avoids the need for indexed operators.
    Node ret = n[1];
    Node cop = getOperatorOfClosure(n, true);
    Node pcop = getOperatorOfClosure(n, true, true);
    for (size_t i = 0, nchild = n[0].getNumChildren(); i < nchild; i++)
    {
      size_t ii = (nchild - 1) - i;
      Node v = n[0][ii];
      // use the partial operator for variables beyond the first
      Node vop = getOperatorOfBoundVar(ii == 0 ? cop : pcop, v);
      ret = nm->mkNode(APPLY_UF, vop, ret);
    }
    // notice that intentionally we drop annotations here
    return ret;
  }
  else if (k == REGEXP_LOOP)
  {
    // ((_ re.loop n1 n2) t) is ((re.loop n1 n2) t)
    TypeNode intType = nm->integerType();
    TypeNode relType =
        nm->mkFunctionType({intType, intType}, nm->mkFunctionType(tn, tn));
    Node rop = getSymbolInternal(
        k, relType, printer::smt2::Smt2Printer::smtKindString(k));
    RegExpLoop op = n.getOperator().getConst<RegExpLoop>();
    Node n1 = nm->mkConstInt(Rational(op.d_loopMinOcc));
    Node n2 = nm->mkConstInt(Rational(op.d_loopMaxOcc));
    return nm->mkNode(APPLY_UF, nm->mkNode(APPLY_UF, rop, n1, n2), n[0]);
  }
  else if (k == MATCH)
  {
    // currently unsupported
    return n;
  }
  else if (k == BITVECTOR_BB_TERM)
  {
    TypeNode btn = nm->booleanType();
    // (bbT t1 ... tn) is (bbT t1 (bbT t2 ... (bbT tn emptybv)))
    // where notice that each bbT has a different type
    Node curr = getNullTerminator(BITVECTOR_CONCAT, tn);
    for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; ++i)
    {
      TypeNode bvt = nm->mkBitVectorType(i + 1);
      TypeNode ftype = nm->mkFunctionType({btn, curr.getType()}, bvt);
      Node bbt = getSymbolInternal(k, ftype, "bbT");
      curr = nm->mkNode(APPLY_UF, bbt, n[nchild - (i + 1)], curr);
    }
    return curr;
  }
  else if (k == SEP_NIL)
  {
    Node tnn = typeAsNode(convertType(tn));
    TypeNode ftype = nm->mkFunctionType(d_sortType, tn);
    Node s = getSymbolInternal(k, ftype, "sep.nil");
    return nm->mkNode(APPLY_UF, s, tnn);
  }
  else if (NodeManager::isNAryKind(k) && n.getNumChildren() >= 2)
  {
    size_t nchild = n.getNumChildren();
    Assert(n.getMetaKind() != metakind::PARAMETERIZED);
    // convert all n-ary applications to binary
    std::vector<Node> children(n.begin(), n.end());
    // distinct is special case
    if (k == DISTINCT)
    {
      // DISTINCT(x1,...,xn) --->
      // AND(DISTINCT(x1,x2), AND(,..., AND(,..,DISTINCT(x_{n-1},x_n))))
      Node ret = nm->mkNode(k, children[0], children[1]);
      for (unsigned i = 0; i < nchild; i++)
        for (unsigned j = i + 1; j < nchild; j++)
        {
          if (i != 0 && j != 1)
          {
            ret = nm->mkNode(AND, ret, nm->mkNode(k, children[i], children[j]));
          }
        }
      Trace("lfsc-term-process-debug") << "n: " << n << std::endl
                                       << "ret: " << ret << std::endl;
      return ret;
    }
    std::reverse(children.begin(), children.end());
    // Add the null-terminator. This is done to disambiguate the number
    // of children for term with n-ary operators. In particular note that
    // (or A B C (or D E)) has representation:
    //   (or A (or B (or C (or (or D E) false))))
    // This makes the AST above distinguishable from (or A B C D E),
    // which otherwise would both have representation:
    //   (or A (or B (or C (or D E))))
    Node nullTerm = getNullTerminator(k, tn);
    // Most operators simply get binarized
    Node ret;
    size_t istart = 0;
    if (nullTerm.isNull())
    {
      ret = children[0];
      istart = 1;
    }
    else
    {
      // must convert recursively, since nullTerm may have subterms.
      ret = convert(nullTerm);
    }
    // the kind to chain
    Kind ck = k;
    // check whether we are also changing the operator name, in which case
    // we build a binary uninterpreted function opc
    Node opc;
    if (k == ADD || k == MULT || k == NONLINEAR_MULT)
    {
      std::stringstream opName;
      // currently allow subtyping
      opName << "a.";
      opName << printer::smt2::Smt2Printer::smtKindString(k);
      TypeNode ftype = nm->mkFunctionType({tn, tn}, tn);
      opc = getSymbolInternal(k, ftype, opName.str());
      ck = APPLY_UF;
    }
    // now, iterate over children and make binary conversion
    for (size_t i = istart, npchild = children.size(); i < npchild; i++)
    {
      if (!opc.isNull())
      {
        ret = nm->mkNode(ck, opc, children[i], ret);
      }
      else
      {
        ret = nm->mkNode(ck, children[i], ret);
      }
    }
    Trace("lfsc-term-process-debug")
        << "...return n-ary conv " << ret << std::endl;
    return ret;
  }
  return n;
}

TypeNode LfscNodeConverter::postConvertType(TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode cur = tn;
  Node tnn;
  Kind k = tn.getKind();
  Trace("lfsc-term-process-debug")
      << "postConvertType " << tn << " " << tn.getNumChildren() << " " << k
      << std::endl;
  if (k == FUNCTION_TYPE)
  {
    // (-> T1 ... Tn T) is (arrow T1 .... (arrow Tn T))
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    // also make the node embedding of the type
    Node arrown = d_typeAsNode[d_arrow];
    Assert(!arrown.isNull());
    cur = tn.getRangeType();
    tnn = typeAsNode(cur);
    for (std::vector<TypeNode>::reverse_iterator it = argTypes.rbegin();
         it != argTypes.rend();
         ++it)
    {
      std::vector<TypeNode> aargs;
      aargs.push_back(*it);
      aargs.push_back(cur);
      cur = nm->mkSort(d_arrow, aargs);
      tnn = nm->mkNode(APPLY_UF, arrown, typeAsNode(*it), tnn);
    }
  }
  else if (k == BITVECTOR_TYPE)
  {
    tnn = d_typeKindToNodeCons[k];
    Node w = nm->mkConstInt(Rational(tn.getBitVectorSize()));
    tnn = nm->mkNode(APPLY_UF, tnn, w);
  }
  else if (k == FLOATINGPOINT_TYPE)
  {
    tnn = d_typeKindToNodeCons[k];
    Node e = nm->mkConstInt(Rational(tn.getFloatingPointExponentSize()));
    Node s = nm->mkConstInt(Rational(tn.getFloatingPointSignificandSize()));
    tnn = nm->mkNode(APPLY_UF, tnn, e, s);
  }
  else if (tn.getNumChildren() == 0)
  {
    // special case: tuples must be distinguished by their arity
    if (tn.isTuple())
    {
      const DType& dt = tn.getDType();
      unsigned int nargs = dt[0].getNumArgs();
      if (nargs > 0)
      {
        std::vector<TypeNode> types;
        std::vector<TypeNode> convTypes;
        std::vector<Node> targs;
        for (unsigned int i = 0; i < nargs; i++)
        {
          // it is not converted yet, convert here
          TypeNode tnc = convertType(dt[0][i].getRangeType());
          types.push_back(d_sortType);
          convTypes.push_back(tnc);
          targs.push_back(typeAsNode(tnc));
        }
        TypeNode ftype = nm->mkFunctionType(types, d_sortType);
        // must distinguish by arity
        std::stringstream ss;
        ss << "Tuple_" << nargs;
        targs.insert(targs.begin(), getSymbolInternal(k, ftype, ss.str()));
        tnn = nm->mkNode(APPLY_UF, targs);
        // we are changing its name, we must make a sort constructor
        cur = nm->mkSortConstructor(ss.str(), nargs);
        cur = nm->mkSort(cur, convTypes);
      }
    }
    if (tnn.isNull())
    {
      std::stringstream ss;
      options::ioutils::applyOutputLang(ss, Language::LANG_SMTLIB_V2_6);
      tn.toStream(ss);
      if (tn.isSort() || (tn.isDatatype() && !tn.isTuple()))
      {
        std::stringstream sss;
        sss << LfscNodeConverter::getNameForUserName(ss.str());
        tnn = getSymbolInternal(k, d_sortType, sss.str());
        cur = nm->mkSort(sss.str());
      }
      else
      {
        tnn = getSymbolInternal(k, d_sortType, ss.str());
      }
    }
  }
  else
  {
    // to build the type-as-node, must convert the component types
    std::vector<Node> targs;
    std::vector<TypeNode> types;
    for (const TypeNode& tnc : tn)
    {
      targs.push_back(typeAsNode(tnc));
      types.push_back(d_sortType);
    }
    Node op;
    if (k == PARAMETRIC_DATATYPE)
    {
      // erase first child, which repeats the datatype
      targs.erase(targs.begin(), targs.begin() + 1);
      types.erase(types.begin(), types.begin() + 1);
      TypeNode ftype = nm->mkFunctionType(types, d_sortType);
      // the operator has been converted; it is no longer a datatype, thus
      // we must print to get its name.
      std::stringstream ss;
      ss << tn[0];
      op = getSymbolInternal(k, ftype, ss.str());
    }
    else if (k == SORT_TYPE)
    {
      TypeNode ftype = nm->mkFunctionType(types, d_sortType);
      std::string name;
      tn.getAttribute(expr::VarNameAttr(), name);
      op = getSymbolInternal(k, ftype, name);
    }
    else
    {
      std::map<Kind, Node>::iterator it = d_typeKindToNodeCons.find(k);
      if (it != d_typeKindToNodeCons.end())
      {
        op = it->second;
      }
    }
    if (!op.isNull())
    {
      targs.insert(targs.begin(), op);
      tnn = nm->mkNode(APPLY_UF, targs);
    }
    else
    {
      AlwaysAssert(false);
    }
  }
  Assert(!tnn.isNull());
  Trace("lfsc-term-process-debug") << "...type as node: " << tnn << std::endl;
  d_typeAsNode[cur] = tnn;
  return cur;
}

std::string LfscNodeConverter::getNameForUserName(const std::string& name)
{
  // For user name X, we do cvc.Y, where Y contains an escaped version of X.
  // Specifically, since LFSC does not allow these characters in identifier
  // bodies: "() \t\n\f;", each is replaced with an escape sequence "\xXX"
  // where XX is the zero-padded hex representation of the code point. "\\" is
  // also escaped.
  //
  // See also: https://github.com/cvc5/LFSC/blob/master/src/lexer.flex#L24
  //
  // The "cvc." prefix ensures we do not clash with LFSC definitions.
  //
  // The escaping ensures that all names are valid LFSC identifiers.
  std::string sanitized("cvc.");
  size_t found = sanitized.size();
  sanitized += name;
  // The following sanitizes symbols that are not allowed in LFSC identifiers
  // here, e.g.
  //   |a b|
  // is converted to:
  //   cvc.a\x20b
  // where "20" is the hex unicode value of " ".
  do
  {
    found = sanitized.find_first_of("() \t\n\f\\;", found);
    if (found != std::string::npos)
    {
      // Emit hex sequence
      std::stringstream seq;
      seq << "\\x" << std::setbase(16) << std::setfill('0') << std::setw(2)
          << static_cast<size_t>(sanitized[found]);
      sanitized.replace(found, 1, seq.str());
      // increment found over the escape
      found += 3;
    }
  } while (found != std::string::npos);
  return sanitized;
}

std::string LfscNodeConverter::getNameForUserNameOf(Node v)
{
  std::string name;
  v.getAttribute(expr::VarNameAttr(), name);
  return getNameForUserName(name);
}

bool LfscNodeConverter::shouldTraverse(Node n)
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

Node LfscNodeConverter::maybeMkSkolemFun(Node k, bool macroApply)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  SkolemFunId sfi = SkolemFunId::NONE;
  Node cacheVal;
  TypeNode tn = k.getType();
  if (sm->isSkolemFunction(k, sfi, cacheVal))
  {
    if (sfi == SkolemFunId::SHARED_SELECTOR)
    {
      // a skolem corresponding to shared selector should print in
      // LFSC as (sel T n) where T is the type and n is the index of the
      // shared selector.
      TypeNode fselt = nm->mkFunctionType(tn.getSelectorDomainType(),
                                          tn.getSelectorRangeType());
      TypeNode intType = nm->integerType();
      TypeNode selt = nm->mkFunctionType({d_sortType, intType}, fselt);
      Node sel = getSymbolInternal(k.getKind(), selt, "sel");
      Node kn = typeAsNode(convertType(tn.getSelectorRangeType()));
      Assert(!cacheVal.isNull() && cacheVal.getKind() == CONST_RATIONAL);
      return nm->mkNode(APPLY_UF, sel, kn, cacheVal);
    }
    else if (sfi == SkolemFunId::RE_UNFOLD_POS_COMPONENT)
    {
      // a skolem corresponding to a regular expression unfolding component
      // should print as (skolem_re_unfold_pos t R n) where the skolem is the
      // n^th component for the unfolding of (str.in_re t R).
      TypeNode strType = nm->stringType();
      TypeNode reType = nm->regExpType();
      TypeNode intType = nm->integerType();
      TypeNode reut = nm->mkFunctionType({strType, reType, intType}, strType);
      Node sk = getSymbolInternal(k.getKind(), reut, "skolem_re_unfold_pos");
      Assert(!cacheVal.isNull() && cacheVal.getKind() == SEXPR
             && cacheVal.getNumChildren() == 3);
      // third value is mpz, which is not converted
      return nm->mkNode(
          APPLY_UF,
          {sk, convert(cacheVal[0]), convert(cacheVal[1]), cacheVal[2]});
    }
  }
  return Node::null();
}

Node LfscNodeConverter::typeAsNode(TypeNode tni) const
{
  // should always exist in the cache, as we always run types through
  // postConvertType before calling this method.
  std::map<TypeNode, Node>::const_iterator it = d_typeAsNode.find(tni);
  AlwaysAssert(it != d_typeAsNode.end()) << "Missing typeAsNode " << tni;
  return it->second;
}

Node LfscNodeConverter::mkInternalSymbol(const std::string& name, TypeNode tn)
{
  Node sym = NodeManager::currentNM()->mkBoundVar(name, tn);
  d_symbols.insert(sym);
  return sym;
}

Node LfscNodeConverter::getSymbolInternalFor(Node n, const std::string& name)
{
  return getSymbolInternal(n.getKind(), n.getType(), name);
}

Node LfscNodeConverter::getSymbolInternal(Kind k,
                                          TypeNode tn,
                                          const std::string& name)
{
  std::tuple<Kind, TypeNode, std::string> key(k, tn, name);
  std::map<std::tuple<Kind, TypeNode, std::string>, Node>::iterator it =
      d_symbolsMap.find(key);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  Node sym = mkInternalSymbol(name, tn);
  d_symbolToBuiltinKind[sym] = k;
  d_symbolsMap[key] = sym;
  return sym;
}

void LfscNodeConverter::getCharVectorInternal(Node c, std::vector<Node>& chars)
{
  Assert(c.getKind() == CONST_STRING);
  NodeManager* nm = NodeManager::currentNM();
  const std::vector<unsigned>& vec = c.getConst<String>().getVec();
  if (vec.size() == 0)
  {
    Node ec = getSymbolInternalFor(c, "emptystr");
    chars.push_back(ec);
    return;
  }
  TypeNode tnc = nm->mkFunctionType(nm->integerType(), c.getType());
  Node aconstf = getSymbolInternal(CONST_STRING, tnc, "char");
  for (unsigned i = 0, size = vec.size(); i < size; i++)
  {
    Node cc = nm->mkNode(APPLY_UF, aconstf, nm->mkConstInt(Rational(vec[i])));
    chars.push_back(cc);
  }
}

bool LfscNodeConverter::isIndexedOperatorKind(Kind k)
{
  return k == REGEXP_LOOP || k == BITVECTOR_EXTRACT || k == BITVECTOR_REPEAT
         || k == BITVECTOR_ZERO_EXTEND || k == BITVECTOR_SIGN_EXTEND
         || k == BITVECTOR_ROTATE_LEFT || k == BITVECTOR_ROTATE_RIGHT
         || k == INT_TO_BITVECTOR || k == IAND || k == APPLY_UPDATER
         || k == APPLY_TESTER;
}

std::vector<Node> LfscNodeConverter::getOperatorIndices(Kind k, Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> indices;
  switch (k)
  {
    case REGEXP_LOOP:
    {
      RegExpLoop op = n.getConst<RegExpLoop>();
      indices.push_back(nm->mkConstInt(Rational(op.d_loopMinOcc)));
      indices.push_back(nm->mkConstInt(Rational(op.d_loopMaxOcc)));
      break;
    }
    case BITVECTOR_EXTRACT:
    {
      BitVectorExtract p = n.getConst<BitVectorExtract>();
      indices.push_back(nm->mkConstInt(Rational(p.d_high)));
      indices.push_back(nm->mkConstInt(Rational(p.d_low)));
      break;
    }
    case BITVECTOR_REPEAT:
      indices.push_back(nm->mkConstInt(
          Rational(n.getConst<BitVectorRepeat>().d_repeatAmount)));
      break;
    case BITVECTOR_ZERO_EXTEND:
      indices.push_back(nm->mkConstInt(
          Rational(n.getConst<BitVectorZeroExtend>().d_zeroExtendAmount)));
      break;
    case BITVECTOR_SIGN_EXTEND:
      indices.push_back(nm->mkConstInt(
          Rational(n.getConst<BitVectorSignExtend>().d_signExtendAmount)));
      break;
    case BITVECTOR_ROTATE_LEFT:
      indices.push_back(nm->mkConstInt(
          Rational(n.getConst<BitVectorRotateLeft>().d_rotateLeftAmount)));
      break;
    case BITVECTOR_ROTATE_RIGHT:
      indices.push_back(nm->mkConstInt(
          Rational(n.getConst<BitVectorRotateRight>().d_rotateRightAmount)));
      break;
    case INT_TO_BITVECTOR:
      indices.push_back(
          nm->mkConstInt(Rational(n.getConst<IntToBitVector>().d_size)));
      break;
    case IAND:
      indices.push_back(nm->mkConstInt(Rational(n.getConst<IntAnd>().d_size)));
      break;
    case APPLY_TESTER:
    {
      unsigned index = DType::indexOf(n);
      const DType& dt = DType::datatypeOf(n);
      indices.push_back(dt[index].getConstructor());
    }
    break;
    case APPLY_UPDATER:
    {
      unsigned index = DType::indexOf(n);
      const DType& dt = DType::datatypeOf(n);
      unsigned cindex = DType::cindexOf(n);
      indices.push_back(dt[cindex][index].getSelector());
    }
    break;
    default: Assert(false); break;
  }
  return indices;
}

Node LfscNodeConverter::getNullTerminator(Kind k, TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  Node nullTerm;
  switch (k)
  {
    case REGEXP_CONCAT:
      // the language containing only the empty string, which has special
      // syntax in LFSC
      nullTerm = getSymbolInternal(k, tn, "re.empty");
      break;
    case BITVECTOR_CONCAT:
    {
      // the null terminator of bitvector concat is a dummy variable of
      // bit-vector type with zero width, regardless of the type of the overall
      // concat.
      TypeNode bvz = nm->mkBitVectorType(0);
      nullTerm = getSymbolInternal(k, bvz, "emptybv");
    }
    break;
    default:
      // no special handling, or not null terminated
      break;
  }
  if (!nullTerm.isNull())
  {
    return nullTerm;
  }
  // otherwise, fall back to standard utility
  return expr::getNullTerminator(k, tn);
}

Kind LfscNodeConverter::getBuiltinKindForInternalSymbol(Node op) const
{
  std::map<Node, Kind>::const_iterator it = d_symbolToBuiltinKind.find(op);
  if (it != d_symbolToBuiltinKind.end())
  {
    return it->second;
  }
  return UNDEFINED_KIND;
}

Node LfscNodeConverter::getOperatorOfTerm(Node n, bool macroApply)
{
  Assert(n.hasOperator());
  Assert(!n.isClosure());
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  std::stringstream opName;
  Trace("lfsc-term-process-debug2")
      << "getOperatorOfTerm " << n << " " << k << " "
      << (n.getMetaKind() == metakind::PARAMETERIZED) << " "
      << isIndexedOperatorKind(k) << std::endl;
  if (n.getMetaKind() == metakind::PARAMETERIZED)
  {
    Node op = n.getOperator();
    std::vector<Node> indices;
    if (isIndexedOperatorKind(k))
    {
      indices = getOperatorIndices(k, n.getOperator());
      // we must convert the name of indices on updaters and testers
      if (k == APPLY_UPDATER || k == APPLY_TESTER)
      {
        Assert(indices.size() == 1);
        // must convert to user name
        TypeNode intType = nm->integerType();
        indices[0] =
            getSymbolInternal(k, intType, getNameForUserNameOf(indices[0]));
      }
    }
    else if (op.getType().isFunction())
    {
      return op;
    }
    // note other kinds of functions (e.g. selectors and testers)
    std::vector<TypeNode> argTypes;
    for (const Node& nc : n)
    {
      argTypes.push_back(nc.getType());
    }
    TypeNode ftype = n.getType();
    if (!argTypes.empty())
    {
      ftype = nm->mkFunctionType(argTypes, ftype);
    }
    Node ret;
    if (isIndexedOperatorKind(k))
    {
      std::vector<TypeNode> itypes;
      for (const Node& i : indices)
      {
        itypes.push_back(i.getType());
      }
      if (!itypes.empty())
      {
        ftype = nm->mkFunctionType(itypes, ftype);
      }
      if (!macroApply)
      {
        if (k != APPLY_UPDATER && k != APPLY_TESTER)
        {
          opName << "f_";
        }
      }
      opName << printer::smt2::Smt2Printer::smtKindString(k);
    }
    else if (k == APPLY_CONSTRUCTOR)
    {
      unsigned index = DType::indexOf(op);
      const DType& dt = DType::datatypeOf(op);
      // get its variable name
      opName << getNameForUserNameOf(dt[index].getConstructor());
    }
    else if (k == APPLY_SELECTOR)
    {
      if (k == APPLY_SELECTOR_TOTAL)
      {
        ret = maybeMkSkolemFun(op, macroApply);
      }
      if (ret.isNull())
      {
        unsigned index = DType::indexOf(op);
        const DType& dt = DType::datatypeOf(op);
        unsigned cindex = DType::cindexOf(op);
        std::stringstream sss;
        sss << dt[cindex][index].getSelector();
        opName << getNameForUserName(sss.str());
      }
    }
    else if (k == SET_SINGLETON || k == BAG_MAKE)
    {
      if (!macroApply)
      {
        opName << "f_";
      }
      opName << printer::smt2::Smt2Printer::smtKindString(k);
    }
    else
    {
      opName << op;
    }
    if (ret.isNull())
    {
      ret = getSymbolInternal(k, ftype, opName.str());
    }
    // if indexed, apply to index
    if (!indices.empty())
    {
      std::vector<Node> ichildren;
      ichildren.push_back(ret);
      ichildren.insert(ichildren.end(), indices.begin(), indices.end());
      ret = nm->mkNode(APPLY_UF, ichildren);
    }
    Trace("lfsc-term-process-debug2") << "...return " << ret << std::endl;
    return ret;
  }
  std::vector<TypeNode> argTypes;
  for (const Node& nc : n)
  {
    argTypes.push_back(nc.getType());
  }
  // we only use binary operators
  if (NodeManager::isNAryKind(k))
  {
    argTypes.resize(2);
  }
  TypeNode tn = n.getType();
  TypeNode ftype = nm->mkFunctionType(argTypes, tn);
  // most functions are called f_X where X is the SMT-LIB name, if we are
  // getting the macroApply variant, then we don't prefix with `f_`.
  if (!macroApply)
  {
    opName << "f_";
  }
  // all arithmetic kinds must explicitly deal with real vs int subtyping
  if (k == ADD || k == MULT || k == NONLINEAR_MULT || k == GEQ || k == GT
      || k == LEQ || k == LT || k == SUB || k == DIVISION || k == DIVISION_TOTAL
      || k == INTS_DIVISION || k == INTS_DIVISION_TOTAL || k == INTS_MODULUS
      || k == INTS_MODULUS_TOTAL || k == NEG || k == POW)
  {
    // currently allow subtyping
    opName << "a.";
  }
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
  return getSymbolInternal(k, ftype, opName.str());
}

Node LfscNodeConverter::getOperatorOfClosure(Node q,
                                             bool macroApply,
                                             bool isPartial)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode retType = isPartial ? q[1].getType() : q.getType();
  TypeNode bodyType = nm->mkFunctionType(q[1].getType(), retType);
  // We permit non-flat function types here
  // intType is used here for variable indices
  TypeNode intType = nm->integerType();
  TypeNode ftype = nm->mkFunctionType({intType, d_sortType}, bodyType);
  Kind k = q.getKind();
  std::stringstream opName;
  if (!macroApply)
  {
    opName << "f_";
  }
  opName << printer::smt2::Smt2Printer::smtKindString(k);
  return getSymbolInternal(k, ftype, opName.str());
}

Node LfscNodeConverter::getOperatorOfBoundVar(Node cop, Node v)
{
  NodeManager* nm = NodeManager::currentNM();
  Node x = nm->mkConstInt(Rational(getOrAssignIndexForVar(v)));
  Node tc = typeAsNode(convertType(v.getType()));
  return nm->mkNode(APPLY_UF, cop, x, tc);
}

size_t LfscNodeConverter::getOrAssignIndexForVar(Node v)
{
  Assert(v.isVar());
  std::map<Node, size_t>::iterator it = d_varIndex.find(v);
  if (it != d_varIndex.end())
  {
    return it->second;
  }
  size_t id = d_varIndex.size();
  d_varIndex[v] = id;
  return id;
}

}  // namespace proof
}  // namespace cvc5
