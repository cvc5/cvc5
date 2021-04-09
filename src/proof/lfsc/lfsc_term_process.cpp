/*********************                                                        */
/*! \file lfsc_term_process.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of rewrite db term processor.
 **/

#include "proof/lfsc/lfsc_term_process.h"

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

LfscTermProcessor::LfscTermProcessor()
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

Node LfscTermProcessor::runConvert(Node n)
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
      << "runConvert " << n << " " << k << std::endl;
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
    TypeNode ftype = nm->mkFunctionType({intType, d_sortType}, tn, false);
    Node bvarOp = getSymbolInternal(k, ftype, "bvar");
    return nm->mkNode(APPLY_UF, bvarOp, x, tc);
  }
  else if (k == SKOLEM)
  {
    // constructors/selectors are represented by skolems, which are defined
    // symbols
    if (tn.isConstructor() || tn.isSelector() || tn.isTester())
    {
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
      TypeNode ftype = nm->mkFunctionType(tn, tn, false);
      Node skolemOp = getSymbolInternal(k, ftype, "skolem");
      return nm->mkNode(APPLY_UF, skolemOp, wi);
    }
  }
  else if (k == APPLY_UF)
  {
    // Assert(d_symbols.find(n.getOperator()) != d_symbols.end());
    return runConvert(theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(n));
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
    return runConvert(nm->mkNode(APPLY_UF, children));
  }
  else if (k == HO_APPLY)
  {
    std::vector<TypeNode> argTypes;
    argTypes.push_back(n[0].getType());
    argTypes.push_back(n[1].getType());
    TypeNode tnh = nm->mkFunctionType(argTypes, tn, false);
    Node hconstf = getSymbolInternal(k, tnh, "apply");
    return nm->mkNode(APPLY_UF, hconstf, n[0], n[1]);
  }
  else if (k == CONST_RATIONAL)
  {
    TypeNode tnv = nm->mkFunctionType(tn, tn);
    // FIXME: subtyping makes this incorrect, also handle CAST_TO_REAL here
    Node rconstf;
    Node arg;
    if (tn.isInteger())
    {
      rconstf = getSymbolInternal(k, tnv, "int");
      Rational r = n.getConst<Rational>();
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
      // FIXME: ensure rationals are printed properly here using mpq syntax
      arg = n;
    }
    return nm->mkNode(APPLY_UF, rconstf, arg);
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
    Node ret = runConvert(getNullTerminator(STRING_CONCAT));
    for (size_t i = 0, size = charVec.size(); i < size; i++)
    {
      ret = nm->mkNode(STRING_CONCAT, charVec[i], ret);
    }
    return ret;
  }
  else if (k == ITE)
  {
    // (ite C A B) is ((ite T) C A B) where T is the return type.
    Node iteOp = getOperatorOfTerm(n, true);
    return nm->mkNode(APPLY_UF, iteOp, n[0], n[1], n[2]);
  }
  else if (k == GEQ || k == GT || k == LEQ || k == LT || k == MINUS)
  {
    // must give special names to SMT-LIB operators with arithmetic subtyping
    // note that MINUS is not n-ary
    Assert(n.getNumChildren() == 2);
    // get the macro-apply version of the operator
    Node opc = getOperatorOfTerm(n, true);
    return nm->mkNode(APPLY_UF, opc, n[0], n[1]);
  }
  else if (n.isClosure())
  {
    TypeNode intType = nm->integerType();
    // (forall ((x1 T1) ... (xn Tk)) P) is
    // ((forall x1 T1) ((forall x2 T2) ... ((forall xk Tk) P))). We use
    // SEXPR to do this, which avoids the need for indexed operators.
    Node ret = n[1];
    TypeNode bodyType = nm->mkFunctionType(ret.getType(), tn, false);
    // We permit non-flat function types here
    TypeNode ftype = nm->mkFunctionType({intType, d_sortType}, bodyType, false);
    Node forallOp = getSymbolInternal(
        k, ftype, printer::smt2::Smt2Printer::smtKindString(k));
    for (size_t i = 0, nchild = n[0].getNumChildren(); i < nchild; i++)
    {
      size_t ii = (nchild - 1) - i;
      Node v = n[0][ii];
      Node x = nm->mkConst(Rational(getOrAssignIndexForVar(v)));
      Node tc = typeAsNode(convertType(v.getType()));
      ret = nm->mkNode(APPLY_UF, nm->mkNode(APPLY_UF, forallOp, x, tc), ret);
    }
    return ret;
  }
  else if (k == REGEXP_LOOP)
  {
    // ((_ re.loop n1 n2) t) is ((re.loop n1 n2) t)
    TypeNode intType = nm->integerType();
    TypeNode relType = nm->mkFunctionType(
        {intType, intType}, nm->mkFunctionType(tn, tn), false);
    Node rop = getSymbolInternal(
        k, relType, printer::smt2::Smt2Printer::smtKindString(k));
    RegExpLoop op = n.getOperator().getConst<RegExpLoop>();
    Node n1 = nm->mkConst(Rational(op.d_loopMinOcc));
    Node n2 = nm->mkConst(Rational(op.d_loopMaxOcc));
    return nm->mkNode(APPLY_UF, nm->mkNode(APPLY_UF, rop, n1, n2), n[0]);
  }
  else if (NodeManager::isNAryKind(k) && n.getNumChildren() >= 2)
  {
    size_t nchild = n.getNumChildren();
    Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
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
            ret = nm->mkNode(
                kind::AND, ret, nm->mkNode(k, children[i], children[j]));
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
      if (n.getType().isInteger())
      {
        opName << "int.";
      }
      else
      {
        opName << "real.";
      }
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

TypeNode LfscTermProcessor::runConvertType(TypeNode tn)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode cur = tn;
  Node tnn;
  Kind k = tn.getKind();
  Trace("lfsc-term-process-debug")
      << "runConvertType " << tn << " " << tn.getNumChildren() << " " << k
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
    // special case: tuples are builtin datatypes
    // notice this would not be a special case if tuples were parametric
    // datatypes
    if (tn.isTuple())
    {
      const DType& dt = tn.getDType();
      unsigned int nargs = dt[0].getNumArgs();
      if (nargs > 0)
      {
        std::vector<Node> targs;
        std::vector<TypeNode> types;
        for (unsigned int i = 0; i < nargs; i++)
        {
          // it is not converted yet, convert here
          TypeNode tnc = runConvertType(dt[0][i].getRangeType());
          types.push_back(d_sortType);
          targs.push_back(typeAsNode(tnc));
        }
        TypeNode ftype = nm->mkFunctionType(types, d_sortType);
        targs.insert(targs.begin(), getSymbolInternal(k, d_sortType, "Tuple"));
        tnn = nm->mkNode(APPLY_UF, targs);
      }
    }
    if (tnn.isNull())
    {
      std::stringstream ss;
      ss << tn;
      tnn = getSymbolInternal(k, d_sortType, ss.str());
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

bool LfscTermProcessor::shouldTraverse(Node n)
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

Node LfscTermProcessor::typeAsNode(TypeNode tni) const
{
  // should always exist in the cache, as we always run types through
  // runConvertType before calling this method.
  std::map<TypeNode, Node>::const_iterator it = d_typeAsNode.find(tni);
  AlwaysAssert(it != d_typeAsNode.end()) << "Missing typeAsNode " << tni;
  return it->second;
}

Node LfscTermProcessor::mkInternalSymbol(const std::string& name, TypeNode tn)
{
  Node sym = NodeManager::currentNM()->mkBoundVar(name, tn);
  d_symbols.insert(sym);
  return sym;
}

Node LfscTermProcessor::getSymbolInternalFor(Node n, const std::string& name)
{
  return getSymbolInternal(n.getKind(), n.getType(), name);
}

Node LfscTermProcessor::getSymbolInternal(Kind k,
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

void LfscTermProcessor::getCharVectorInternal(Node c, std::vector<Node>& chars)
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

Node LfscTermProcessor::getNullTerminator(Kind k)
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

Node LfscTermProcessor::getOperatorOfTerm(Node n, bool macroApply)
{
  Assert(n.hasOperator());
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  std::stringstream opName;
  if (n.getMetaKind() == metakind::PARAMETERIZED)
  {
    Node op = n.getOperator();
    if (op.getType().isFunction())
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
      ftype = nm->mkFunctionType(argTypes, ftype, false);
    }
    if (k == APPLY_TESTER)
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
  TypeNode ftype = nm->mkFunctionType(argTypes, tn, false);
  // most functions are called f_X where X is the SMT-LIB name, if we are
  // getting the macroApply variant, then we don't prefix with `f_`.
  if (!macroApply)
  {
    opName << "f_";
  }
  // all arithmetic kinds must explicitly deal with real vs int subtyping
  if (k == PLUS || k == MULT || k == NONLINEAR_MULT || k == GEQ || k == GT
      || k == LEQ || k == LT || k == MINUS)
  {
    if (n[0].getType().isInteger())
    {
      opName << "int.";
    }
    else
    {
      opName << "real.";
    }
  }
  opName << printer::smt2::Smt2Printer::smtKindString(k);
  if (k == ITE)
  {
    // ITE is indexed by its type
    TypeNode boolType = nm->booleanType();
    TypeNode itype = nm->mkFunctionType(d_sortType, ftype, false);
    Node iteSym = getSymbolInternal(k, itype, opName.str());
    Node typeNode = typeAsNode(convertType(tn));
    Assert(!typeNode.isNull());
    return nm->mkNode(APPLY_UF, iteSym, typeNode);
  }
  return getSymbolInternal(k, ftype, opName.str());
}

size_t LfscTermProcessor::getOrAssignIndexForVar(Node v)
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
