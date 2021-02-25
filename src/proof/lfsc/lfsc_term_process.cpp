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

#include "printer/smt2/smt2_printer.h"
#include "theory/uf/theory_uf_rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace proof {

LfscTermProcessor::LfscTermProcessor()
{
  d_arrow = NodeManager::currentNM()->mkSortConstructor("arrow", 2);
  d_sortType = NodeManager::currentNM()->mkSort("sortType");
}

Node LfscTermProcessor::runConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  TypeNode tn = n.getType();
  if (k == APPLY_UF)
  {
    return runConvert(theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(n));
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
  else if (k == CONST_RATIONAL)
  {
    TypeNode tnv = nm->mkFunctionType(tn, tn);
    // FIXME: subtyping makes this incorrect, also handle TO_REAL here
    Node rconstf;
    Node arg;
    if (tn.isInteger())
    {
      rconstf = getSymbolInternal(k, tnv, "int");
      arg = n;
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
    // "" is emptystr
    // "A" is (char 65)
    // "ABC" is (str.++ (char 65) (str.++ (char 66) (char 67)))
    const std::vector<unsigned>& vec = n.getConst<String>().getVec();
    if (vec.size() == 0)
    {
      return getSymbolInternalFor(n, "emptystr");
    }
    if (vec.size() == 1)
    {
      TypeNode tnc = nm->mkFunctionType(nm->integerType(), tn);
      Node aconstf = getSymbolInternal(k, tnc, "char");
      return nm->mkNode(APPLY_UF, aconstf, nm->mkConst(Rational(vec[0])));
    }
    std::vector<unsigned> v(vec.begin(), vec.end());
    std::reverse(v.begin(), v.end());
    std::vector<unsigned> tmp;
    tmp.push_back(v[0]);
    Node ret = runConvert(nm->mkConst(String(tmp)));
    tmp.pop_back();
    for (unsigned i = 1, size = v.size(); i < size; i++)
    {
      tmp.push_back(v[i]);
      // also convert internal
      ret =
          nm->mkNode(STRING_CONCAT, runConvert(nm->mkConst(String(tmp))), ret);
      tmp.pop_back();
    }
    return ret;
  }
  else if (k == ITE)
  {
    // TODO: indexed type argument
    std::vector<TypeNode> argTypes;
    argTypes.push_back(nm->booleanType());
    argTypes.push_back(d_sortType);
    argTypes.push_back(tn);
    argTypes.push_back(tn);
    TypeNode tni = nm->mkFunctionType(argTypes, tn);
    Node itep = getSymbolInternal(k, tni, "ite");
    std::vector<Node> args;
    args.push_back(itep);
    args.push_back(n[0]);
    Node tv;  // TODO
    args.push_back(tv);
    args.push_back(n[1]);
    args.push_back(n[2]);
    return nm->mkNode(APPLY_UF, args);
  }
  else if (k== MINUS)
  {
    // note that MINUS is not n-ary
    Assert (n.getNumChildren()==2);
    // TODO: refactor
    std::stringstream opName;
    opName << "int." << printer::smt2::Smt2Printer::smtKindString(k);
    TypeNode type = n.getType();
    TypeNode ftype = nm->mkFunctionType({type, type}, type);
    Node opc = getSymbolInternal(k, ftype, opName.str());
    return nm->mkNode(APPLY_UF, opc, n[0], n[1]);
  }
  else if (n.isClosure())
  {
    // (forall ((x1 T1) ... (xn Tk)) P) is
    // ((forall n1 T1) ((forall n2 T2) ... ((forall nk Tk) P))). We use
    // SEXPR to do this, which avoids the need for indexed operators.
#if 0
    for (size_t i=0, nchild = n.getNumChildren(); i<nchild; i++)
    {
      Node n;
      Node tc = typeAsNode(
      Node sexprOp = nm->mkNode(SEXPR, forallOp, 
    }
#endif
  }
  else if (ExprManager::isNAryKind(k) && n.getNumChildren() >= 2)
  {
    size_t nchild = n.getNumChildren();
    Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
    // convert all n-ary applications to binary
    std::vector<Node> children(n.begin(), n.end());
    std::reverse(children.begin(), children.end());
    if (n.getKind() != DISTINCT)
    {
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
      size_t i = 0;
      if (nullTerm.isNull())
      {
        ret = children[0];
        i = 1;
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
      if (k==PLUS || k==MULT)
      {
        std::stringstream opName;
        opName << "int." << printer::smt2::Smt2Printer::smtKindString(k);
        TypeNode type = n.getType();
        TypeNode ftype = nm->mkFunctionType({type, type}, type);
        opc = getSymbolInternal(k, ftype, opName.str());
        ck = APPLY_UF;
      }
      // now, iterate over children and make binary conversion
      for (; i < nchild; i++)
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
    else
    {
      // DINSTICT(x1,...,xn) --->
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
  }
  return n;
}

TypeNode LfscTermProcessor::runConvertType(TypeNode tn)
{
  Kind k = tn.getKind();
  if (k == FUNCTION_TYPE)
  {
    NodeManager* nm = NodeManager::currentNM();
    // (-> T1 ... Tn T) is (arrow T1 .... (arrow Tn T))
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    TypeNode cur = tn.getRangeType();
    for (std::vector<TypeNode>::reverse_iterator it = argTypes.rbegin();
         it != argTypes.rend();
         ++it)
    {
      std::vector<TypeNode> aargs;
      aargs.push_back(*it);
      aargs.push_back(cur);
      cur = nm->mkSort(d_arrow, aargs);
    }
    return cur;
  }
  return tn;
}

Node LfscTermProcessor::typeAsNode(TypeNode tni)
{
  // TODO;
  return Node::null();
}

Node LfscTermProcessor::getSymbolInternalFor(Node n,
                                             const std::string& name,
                                             uint32_t v)
{
  return getSymbolInternal(n.getKind(), n.getType(), name, v);
}

Node LfscTermProcessor::getSymbolInternal(Kind k,
                                          TypeNode tn,
                                          const std::string& name,
                                          uint32_t v)
{
  std::tuple<Kind, TypeNode, uint32_t> key(k, tn, v);
  std::map<std::tuple<Kind, TypeNode, uint32_t>, Node>::iterator it =
      d_symbols.find(key);
  if (it != d_symbols.end())
  {
    return it->second;
  }
  Node sym = NodeManager::currentNM()->mkBoundVar(name, tn);
  d_symbols[key] = sym;
  return sym;
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
    case MULT: nullTerm = nm->mkConst(Rational(1)); break;
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

Node LfscTermProcessor::getOperatorForTerm(Node n)
{
  Assert(n.hasOperator());
  if (n.getMetaKind() == metakind::PARAMETERIZED)
  {
    return n.getOperator();
  }
  std::vector<TypeNode> argTypes;
  for (const Node& nc : n)
  {
    argTypes.push_back(nc.getType());
  }
  Kind k = n.getKind();
  // we only use binary operators
  if (ExprManager::isNAryKind(k))
  {
    argTypes.resize(2);
  }
  TypeNode retType = n.getType();
  TypeNode ftype = NodeManager::currentNM()->mkFunctionType(argTypes, retType);
  // most functions are called f_X where X is the SMT-LIB name
  std::stringstream opName;
  opName << "f_" << printer::smt2::Smt2Printer::smtKindString(k);
  return getSymbolInternal(k, ftype, opName.str());
}

}  // namespace proof
}  // namespace CVC4
