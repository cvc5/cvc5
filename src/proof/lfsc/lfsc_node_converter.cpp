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

#include <sstream>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_manager_attributes.h"
#include "expr/skolem_manager.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/uf/theory_uf_rewriter.h"

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
    Node x = nm->mkConst(Rational(getOrAssignIndexForVar(n)));
    Node tc = typeAsNode(convertType(tn));
    TypeNode ftype = nm->mkFunctionType({intType, d_sortType}, tn);
    Node bvarOp = getSymbolInternal(k, ftype, "bvar");
    return nm->mkNode(APPLY_UF, bvarOp, x, tc);
  }
  else if (k == SKOLEM || k == BOOLEAN_TERM_VARIABLE)
  {
    // constructors/selectors are represented by skolems, which are defined
    // symbols
    if (tn.isConstructor() || tn.isSelector() || tn.isTester())
    {
      // TODO: should be given user names
      return n;
    }
    // skolems v print as their witness forms
    // v is (skolem W) where W is the original or witness form of v
    Node on = SkolemManager::getOriginalForm(n);
    Node wi = on == n ? SkolemManager::getWitnessForm(n) : on;
    Assert(!wi.isNull()) << "Missing skolem definition for " << n;
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
    else
    {
      // use a fresh variable
      TypeNode intType = nm->integerType();
      TypeNode varType = nm->mkFunctionType({intType, d_sortType}, tn);
      Node var = mkInternalSymbol("var", varType);
      Node index = nm->mkConst(Rational(getOrAssignIndexForVar(n)));
      Node tc = typeAsNode(convertType(tn));
      return nm->mkNode(APPLY_UF, var, index, tc);
    }
  }
  else if (n.isVar())
  {
    std::stringstream ss;
    ss << n;
    Node nn = mkInternalSymbol(getNameForUserName(ss.str()), tn);
    return nn;
  }
  else if (k == APPLY_UF)
  {
    // Assert(d_symbols.find(n.getOperator()) != d_symbols.end());
    return convert(theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(n));
  }
  else if (k == APPLY_CONSTRUCTOR || k == APPLY_SELECTOR || k == APPLY_TESTER)
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
  else if (k == CONST_RATIONAL || k == CAST_TO_REAL)
  {
    if (k == CAST_TO_REAL)
    {
      // already converted
      do
      {
        Assert(n[0].getKind() == APPLY_UF);
        n = n[0];
      } while (n.getKind() != CONST_RATIONAL);
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
        arg = nm->mkNode(APPLY_UF, mpzn, nm->mkConst(r.abs()));
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
    TypeNode btnv = nm->mkFunctionType(btn, btn);
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
    Node ret = postConvert(getNullTerminator(STRING_CONCAT));
    for (size_t i = 0, size = charVec.size(); i < size; i++)
    {
      ret = nm->mkNode(STRING_CONCAT, charVec[i], ret);
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
  else if (k == ITE)
  {
    // (ite C A B) is ((ite T) C A B) where T is the return type.
    Node iteOp = getOperatorOfTerm(n, true);
    return nm->mkNode(APPLY_UF, iteOp, n[0], n[1], n[2]);
  }
  else if (k == GEQ || k == GT || k == LEQ || k == LT || k == MINUS
           || k == DIVISION || k == DIVISION_TOTAL || k == INTS_DIVISION
           || k == INTS_DIVISION_TOTAL || k == INTS_MODULUS
           || k == INTS_MODULUS_TOTAL || k == UMINUS
           || isIndexedOperatorKind(k))
  {
    // must give special names to SMT-LIB operators with arithmetic subtyping
    // note that MINUS is not n-ary
    // get the macro-apply version of the operator
    Node opc = getOperatorOfTerm(n, true);
    std::vector<Node> children;
    children.push_back(opc);
    children.insert(children.end(), n.begin(), n.end());
    return nm->mkNode(APPLY_UF, children);
  }
  else if (k == EMPTYSET || k == UNIVERSE_SET)
  {
    Node t = typeAsNode(convertType(tn));
    TypeNode etype = nm->mkFunctionType(d_sortType, tn);
    Node ef =
        getSymbolInternal(k, etype, k == EMPTYSET ? "emptyset" : "univset");
    return nm->mkNode(APPLY_UF, ef, t);
  }
  else if (n.isClosure())
  {
    // (forall ((x1 T1) ... (xn Tk)) P) is
    // ((forall x1 T1) ((forall x2 T2) ... ((forall xk Tk) P))). We use
    // SEXPR to do this, which avoids the need for indexed operators.
    Node ret = n[1];
    Node cop = getOperatorOfClosure(n);
    for (size_t i = 0, nchild = n[0].getNumChildren(); i < nchild; i++)
    {
      size_t ii = (nchild - 1) - i;
      Node v = n[0][ii];
      Node vop = getOperatorOfBoundVar(cop, v);
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
    Node n1 = nm->mkConst(Rational(op.d_loopMinOcc));
    Node n2 = nm->mkConst(Rational(op.d_loopMaxOcc));
    return nm->mkNode(APPLY_UF, nm->mkNode(APPLY_UF, rop, n1, n2), n[0]);
  }
  else if (k == MATCH)
  {
    // FIXME
    return n;
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
    Node nullTerm = getNullTerminator(k);
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
    if (k == PLUS || k == MULT || k == NONLINEAR_MULT)
    {
      std::stringstream opName;
      // currently allow subtyping
      opName << "a.";
      /*
      if (n.getType().isInteger())
      {
        opName << "int.";
      }
      else
      {
        opName << "real.";
      }
      */
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
    Node w = nm->mkConst(Rational(tn.getBitVectorSize()));
    tnn = nm->mkNode(APPLY_UF, tnn, w);
  }
  else if (k == FLOATINGPOINT_TYPE)
  {
    tnn = d_typeKindToNodeCons[k];
    Node e = nm->mkConst(Rational(tn.getFloatingPointExponentSize()));
    Node s = nm->mkConst(Rational(tn.getFloatingPointSignificandSize()));
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
      tn.toStream(ss, language::output::LANG_SMTLIB_V2_6);
      if (false && (tn.isSort() || tn.isDatatype()))
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
      TypeNode ftype = nm->mkFunctionType(types, d_sortType);
      op = getSymbolInternal(k, ftype, tn.getDType().getName());
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
  std::stringstream ss;
  ss << "cvc." << name;
  return ss.str();
}

bool LfscNodeConverter::shouldTraverse(Node n)
{
  Kind k = n.getKind();
  // don't convert bound variable list directly
  if (k == BOUND_VAR_LIST)
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
    Node cc = nm->mkNode(APPLY_UF, aconstf, nm->mkConst(Rational(vec[i])));
    chars.push_back(cc);
  }
}

bool LfscNodeConverter::isIndexedOperatorKind(Kind k)
{
  // TODO: this can be moved to a more central place
  return k == BITVECTOR_EXTRACT || k == BITVECTOR_REPEAT
         || k == BITVECTOR_ZERO_EXTEND || k == BITVECTOR_SIGN_EXTEND
         || k == BITVECTOR_ROTATE_LEFT || k == BITVECTOR_ROTATE_RIGHT
         || k == INT_TO_BITVECTOR;
}

std::vector<Node> LfscNodeConverter::getOperatorIndices(Node n)
{
  // TODO: this can be moved to a more central place
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> indices;
  Kind k = n.getKind();
  switch (k)
  {
    case kind::BITVECTOR_EXTRACT_OP:
    {
      BitVectorExtract p = n.getConst<BitVectorExtract>();
      indices.push_back(nm->mkConst(Rational(p.d_high)));
      indices.push_back(nm->mkConst(Rational(p.d_low)));
      break;
    }
    case kind::BITVECTOR_REPEAT_OP:
      indices.push_back(
          nm->mkConst(Rational(n.getConst<BitVectorRepeat>().d_repeatAmount)));
      break;
    case kind::BITVECTOR_ZERO_EXTEND_OP:
      indices.push_back(nm->mkConst(
          Rational(n.getConst<BitVectorZeroExtend>().d_zeroExtendAmount)));
      break;
    case kind::BITVECTOR_SIGN_EXTEND_OP:
      indices.push_back(nm->mkConst(
          Rational(n.getConst<BitVectorSignExtend>().d_signExtendAmount)));
      break;
    case kind::BITVECTOR_ROTATE_LEFT_OP:
      indices.push_back(nm->mkConst(
          Rational(n.getConst<BitVectorRotateLeft>().d_rotateLeftAmount)));
      break;
    case kind::BITVECTOR_ROTATE_RIGHT_OP:
      indices.push_back(nm->mkConst(
          Rational(n.getConst<BitVectorRotateRight>().d_rotateRightAmount)));
      break;
    case kind::INT_TO_BITVECTOR_OP:
      indices.push_back(
          nm->mkConst(Rational(n.getConst<IntToBitVector>().d_size)));
      break;
    default: Assert(false); break;
  }
  return indices;
}

Node LfscNodeConverter::getNullTerminator(Kind k)
{
  NodeManager* nm = NodeManager::currentNM();
  Node nullTerm;
  switch (k)
  {
    case OR: nullTerm = nm->mkConst(false); break;
    case AND: nullTerm = nm->mkConst(true); break;
    case PLUS: nullTerm = nm->mkConst(Rational(0)); break;
    case MULT:
    case NONLINEAR_MULT: nullTerm = nm->mkConst(Rational(1)); break;
    case STRING_CONCAT: nullTerm = nm->mkConst(String("")); break;
    case REGEXP_CONCAT:
      // the language containing only the empty string
      nullTerm = nm->mkNode(STRING_TO_REGEXP, nm->mkConst(String("")));
      break;
    default:
      // not handled as null-terminated
      break;
  }
  return nullTerm;
}

Node LfscNodeConverter::getOperatorOfTerm(Node n, bool macroApply)
{
  Assert(n.hasOperator());
  Assert(!n.isClosure());
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  std::stringstream opName;
  if (n.getMetaKind() == metakind::PARAMETERIZED)
  {
    Node op = n.getOperator();
    std::vector<Node> indices;
    if (isIndexedOperatorKind(k))
    {
      indices = getOperatorIndices(n.getOperator());
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
        opName << "f_";
      }
      opName << printer::smt2::Smt2Printer::smtKindString(k);
    }
    else if (k == APPLY_TESTER)
    {
      // use is-C instead of (_ is C) syntax for testers
      unsigned cindex = DType::indexOf(op);
      const DType& dt = DType::datatypeOf(op);
      opName << "is-" << dt[cindex].getConstructor();
    }
    else
    {
      opName << op;
    }
    Node ret = getSymbolInternal(k, ftype, opName.str());
    // TODO: if parametric, instantiate the parameters?

    // if indexed, apply to index
    if (!indices.empty())
    {
      std::vector<Node> ichildren;
      ichildren.push_back(ret);
      ichildren.insert(ichildren.end(), indices.begin(), indices.end());
      ret = nm->mkNode(APPLY_UF, ichildren);
    }
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
  if (k == PLUS || k == MULT || k == NONLINEAR_MULT || k == GEQ || k == GT
      || k == LEQ || k == LT || k == MINUS || k == DIVISION
      || k == DIVISION_TOTAL || k == INTS_DIVISION || k == INTS_DIVISION_TOTAL
      || k == INTS_MODULUS || k == INTS_MODULUS_TOTAL || k == UMINUS)
  {
    // currently allow subtyping
    opName << "a.";
    /*
    if (n[0].getType().isInteger())
    {
      opName << "int.";
    }
    else
    {
      opName << "real.";
    }
    */
  }
  if (k == UMINUS)
  {
    opName << "u";
  }
  opName << printer::smt2::Smt2Printer::smtKindString(k);
  if (k == DIVISION_TOTAL || k == INTS_DIVISION_TOTAL
      || k == INTS_MODULUS_TOTAL)
  {
    opName << "_total";
  }
  if (k == ITE)
  {
    // ITE is indexed by its type
    TypeNode boolType = nm->booleanType();
    TypeNode itype = nm->mkFunctionType(d_sortType, ftype);
    Node iteSym = getSymbolInternal(k, itype, opName.str());
    Node typeNode = typeAsNode(convertType(tn));
    Assert(!typeNode.isNull());
    return nm->mkNode(APPLY_UF, iteSym, typeNode);
  }
  return getSymbolInternal(k, ftype, opName.str());
}

Node LfscNodeConverter::getOperatorOfClosure(Node q)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode bodyType = nm->mkFunctionType(q[1].getType(), q.getType());
  // We permit non-flat function types here
  // intType is used here for variable indices
  TypeNode intType = nm->integerType();
  TypeNode ftype = nm->mkFunctionType({intType, d_sortType}, bodyType);
  Kind k = q.getKind();
  return getSymbolInternal(
      k, ftype, printer::smt2::Smt2Printer::smtKindString(k));
}

Node LfscNodeConverter::getOperatorOfBoundVar(Node cop, Node v)
{
  NodeManager* nm = NodeManager::currentNM();
  Node x = nm->mkConst(Rational(getOrAssignIndexForVar(v)));
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
