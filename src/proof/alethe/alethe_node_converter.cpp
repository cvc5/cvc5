/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion
 */

#include "proof/alethe/alethe_node_converter.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "proof/proof_rule_checker.h"
#include "util/bitvector.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace proof {


Node AletheNodeConverter::maybeConvert(Node n, bool isAssumption)
{
  d_error = "";
  Node res = convert(n);
  if (!d_error.empty())
  {
    return Node::null();
  }
  if (isAssumption)
  {
    d_convToOriginalAssumption[res] = n;
  }
  return res;
}

Node AletheNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::BITVECTOR_BITOF:
    {
      std::stringstream ss;
      ss << "(_ @bitOf " << n.getOperator().getConst<BitVectorBitOf>().d_bitIndex
         << ")";
      TypeNode fType = nm->mkFunctionType(n[0].getType(), n.getType());
      Node op = mkInternalSymbol(ss.str(), fType, true);
      Node converted = nm->mkNode(Kind::APPLY_UF, op, n[0]);
      return converted;
    }
    case Kind::BITVECTOR_BB_TERM:
    {
      std::vector<Node> children;
      std::vector<TypeNode> childrenTypes;
      for (const Node& c : n)
      {
        childrenTypes.push_back(c.getType());
        children.push_back(c);
      }
      TypeNode fType = nm->mkFunctionType(childrenTypes, n.getType());
      Node op = mkInternalSymbol("@bbT", fType, true);
      children.insert(children.begin(), op);
      Node converted = nm->mkNode(Kind::APPLY_UF, children);
      return converted;
    }
    case Kind::BITVECTOR_EAGER_ATOM:
    {
      return n[0];
    }
    case Kind::SKOLEM:
    {
      Trace("alethe-conv") << "AletheNodeConverter: handling skolem " << n
                           << "\n";
      SkolemManager* sm = nm->getSkolemManager();
      SkolemId sfi = SkolemId::NONE;
      Node cacheVal;
      sm->isSkolemFunction(n, sfi, cacheVal);
      // skolems v print as their original forms
      // v is (skolem W) where W is the original or original form of v
      Node wi = SkolemManager::getUnpurifiedForm(n);
      if (!wi.isNull() && wi != n)
      {
        Trace("alethe-conv")
            << "...to convert original form " << wi << std::endl;
        Node conv = convert(wi);
        // ignore purification skolems
        if (sfi != SkolemId::PURIFY)
        {
          d_skolems[n] = conv;
        }
        return conv;
      }
      // create the witness term (witness ((x_i T_i)) (exists ((x_i+1 T_i+1)
      // ... (x_n T_n)) body), where the bound variables and the body come from
      // the quantifier term which must be the first element of cacheVal (which
      // should be a list), and i the second.
      if (sfi == SkolemId::QUANTIFIERS_SKOLEMIZE)
      {
        Trace("alethe-conv")
            << ".. to build witness with index/quant: " << cacheVal[1] << " / "
            << cacheVal[0] << "\n";
        Assert(cacheVal.getKind() == Kind::SEXPR
               && cacheVal.getNumChildren() == 2);
        Node quant = cacheVal[0];
        Assert(quant.getKind() == Kind::EXISTS);
        Node var = cacheVal[1];
        uint32_t index = -1;
        for (size_t i = 0, size = quant[0].getNumChildren(); i < size; ++i)
        {
          if (var == quant[0][i])
          {
            index = i;
            break;
          }
        }
        // Since cvc5 *always* skolemize FORALLs, we generate the choice term
        // assuming it is gonna be introduced via a sko_forall rule, in which
        // case the body of the choice is negated, which means to have
        // universal quantification of the remaining variables in the choice
        // body, and the whole thing negated. Likewise, since during
        // Skolemization cvc5 will have negated the body of the original
        // quantifier, we need to revert that as well.
        Assert(index < quant[0].getNumChildren());
        Assert(quant[1].getKind() == Kind::NOT);
        Node body =
            index == quant[0].getNumChildren() - 1
                ? quant[1]
                : nm->mkNode(Kind::FORALL,
                             nm->mkNode(
                                 Kind::BOUND_VAR_LIST,
                                 std::vector<Node>{quant[0].begin() + index + 1,
                                                   quant[0].end()}),
                             quant[1][0])
                      .notNode();
        // we need to replace in the body all the free variables (i.e., from 0
        // to index) by their respective choice terms. To do this, we get
        // the skolems for each of these variables, retrieve their
        // conversions, and replace the variables by the conversions in body
        if (index > 0)
        {
          std::vector<Node> subs;
          for (size_t i = 0; i < index; ++i)
          {
            Node v = quant[0][i];
            std::vector<Node> cacheVals{quant, v};
            Node sk = sm->mkSkolemFunction(SkolemId::QUANTIFIERS_SKOLEMIZE,
                                           cacheVals);
            Assert(!sk.isNull());
            subs.push_back(d_defineSkolems ? sk : convert(sk));
          }
          body = body.substitute(quant[0].begin(),
                                 quant[0].begin() + index,
                                 subs.begin(),
                                 subs.end());
        }
        Node witness = nm->mkNode(
            Kind::WITNESS, nm->mkNode(Kind::BOUND_VAR_LIST, var), body);
        Trace("alethe-conv") << ".. witness: " << witness << "\n";
        witness = convert(witness);
        if (d_defineSkolems)
        {
          d_skolemsAux[n] = witness;
          if (index == quant[0].getNumChildren() - 1)
          {
            Trace("alethe-conv")
                << "....populate map from aux : " << d_skolemsAux << "\n";
            for (size_t i = index + 1; i > 0; --i)
            {
              Node v = quant[0][i - 1];
              std::vector<Node> cacheVals{quant, v};
              Node sk = sm->mkSkolemFunction(SkolemId::QUANTIFIERS_SKOLEMIZE,
                                             cacheVals);
              Assert(!sk.isNull());
              Assert(d_skolemsAux.find(sk) != d_skolemsAux.end())
                  << "Could not find sk " << sk;
              d_skolems[sk] = d_skolemsAux[sk];
            }
            d_skolemsAux.clear();
          }
          return n;
        }
        d_skolems[n] = witness;
        return witness;
      }
      std::stringstream ss;
      ss << "Proof contains Skolem (kind " << sfi << ", term " << n
         << ") is not supported by Alethe.";
      d_error = ss.str();
      return Node::null();
    }
    case Kind::FORALL:
    {
      // remove patterns, if any
      return n.getNumChildren() == 3 ? nm->mkNode(Kind::FORALL, n[0], n[1]) : n;
    }
    // we must make it to be printed with "choice", so we create an operator
    // with that name and the correct type and do a function application
    case Kind::WITNESS:
    {
      std::vector<TypeNode> childrenTypes;
      for (const Node& c : n)
      {
        childrenTypes.push_back(c.getType());
      }
      TypeNode fType = nm->mkFunctionType(childrenTypes, n.getType());
      Node choiceOp = mkInternalSymbol("choice", fType);
      Node converted = nm->mkNode(Kind::APPLY_UF, choiceOp, n[0], n[1]);
      Trace("alethe-conv") << ".. converted to choice: " << converted << "\n";
      return converted;
    }
    default:
    {
      return n;
    }
  }
  return n;
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name,
                                           TypeNode tn,
                                           bool useRawSym)
{
  std::pair<TypeNode, std::string> key(tn, name);
  std::map<std::pair<TypeNode, std::string>, Node>::iterator it =
      d_symbolsMap.find(key);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node sym = useRawSym ? nm->mkRawSymbol(name, tn) : nm->mkBoundVar(name, tn);
  d_symbolsMap[key] = sym;
  return sym;
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name)
{
  return mkInternalSymbol(name, NodeManager::currentNM()->sExprType());
}

const std::string& AletheNodeConverter::getError() { return d_error; }

Node AletheNodeConverter::getOriginalAssumption(Node n)
{
  auto it = d_convToOriginalAssumption.find(n);
  if (it != d_convToOriginalAssumption.end())
  {
    return it->second;
  }
  return Node::null();
}

const std::map<Node, Node>& AletheNodeConverter::getSkolemDefinitions()
{
  return d_skolems;
}

}  // namespace proof
}  // namespace cvc5::internal
