/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace proof {

Node AletheNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::SKOLEM:
    {
      Trace("alethe-conv") << "AletheNodeConverter: handling skolem " << n
                           << "\n";
      // skolems v print as their original forms
      // v is (skolem W) where W is the original or original form of v
      Node wi = SkolemManager::getUnpurifiedForm(n);
      if (!wi.isNull() && wi != n)
      {
        Trace("alethe-conv")
            << "...to convert original form " << wi << std::endl;
        return convert(wi);
      }
      // might be a skolem function. For now we only handle the function for
      // skolemization of strong quantifiers.
      SkolemManager* sm = nm->getSkolemManager();
      SkolemFunId sfi = SkolemFunId::NONE;
      Node cacheVal;
      // create the witness term (witness ((x_i T_i)) (exists ((x_i+1 T_i+1)
      // ... (x_n T_n)) body), where the bound variables and the body come from
      // the quantifier term which must be the first element of cacheVal (which
      // should be a list), and i the second.
      if (sm->isSkolemFunction(n, sfi, cacheVal)
          && sfi == SkolemFunId::QUANTIFIERS_SKOLEMIZE)
      {
        Trace("alethe-conv")
            << ".. to build witness with index/quant: " << cacheVal[1] << " / "
            << cacheVal[0] << "\n";
        Assert(cacheVal.getKind() == Kind::SEXPR
               && cacheVal.getNumChildren() == 2);
        Node quant = cacheVal[0];
        Assert(quant.getKind() == Kind::EXISTS);
        uint32_t index;
        if (ProofRuleChecker::getUInt32(cacheVal[1], index))
        {
          Assert(index < quant[0].getNumChildren());
          Node body =
              index == quant[0].getNumChildren() - 1
                  ? quant[1]
                  : nm->mkNode(
                      Kind::EXISTS,
                      nm->mkNode(Kind::BOUND_VAR_LIST,
                                 std::vector<Node>{quant[0].begin() + index + 1,
                                                   quant[0].end()}),
                      quant[1]);
          // we need to replace in the body all the free variables (i.e., from 0
          // to index) by their respective choice terms. To do this, we get
          // the skolems for each of these variables, retrieve their
          // conversions, and replace the variables by the conversions in body
          if (index > 0)
          {
            std::vector<Node> subs;
            for (size_t i = 0; i < index; ++i)
            {
              Node sk = sm->getSkolemForBVar(quant[0][i]);
              Assert(!sk.isNull());
              subs.push_back(convert(sk));
            }
            body = body.substitute(quant[0].begin(),
                                   quant[0].begin() + index,
                                   subs.begin(),
                                   subs.end());
          }
          Node witness =
              nm->mkNode(Kind::WITNESS,
                         nm->mkNode(Kind::BOUND_VAR_LIST, quant[0][index]),
                         body);
          Trace("alethe-conv") << ".. witness: " << witness << "\n";
          return convert(witness);
        }
      }
      Unreachable() << "Fresh Skolems are not allowed\n";
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

Node AletheNodeConverter::mkInternalSymbol(const std::string& name)
{
  return mkInternalSymbol(name, NodeManager::currentNM()->sExprType());
}

Node AletheNodeConverter::mkInternalSymbol(const std::string& name, TypeNode tn)
{
  std::pair<TypeNode, std::string> key(tn, name);
  std::map<std::pair<TypeNode, std::string>, Node>::iterator it =
      d_symbolsMap.find(key);
  if (it != d_symbolsMap.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node sym = nm->mkBoundVar(name, tn);
  d_symbolsMap[key] = sym;
  return sym;
}

}  // namespace proof
}  // namespace cvc5::internal
