/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Int-blasting utility
 */

#include "theory/bv/int_blaster.h"

#include <cmath>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "options/option_exception.h"
#include "options/uf_options.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "util/iand.h"
#include "util/rational.h"

namespace cvc5 {
using namespace cvc5::theory;

IntBlaster::IntBlaster(context::Context* c,
                       options::SolveBVAsIntMode mode,
                       uint64_t granularity,
                       bool introduceFreshIntVars)
    : d_binarizeCache(c),
      d_intblastCache(c),
      d_rangeAssertions(c),
      d_bitwiseAssertions(c),
      d_mode(mode),
      d_granularity(granularity),
      d_context(c),
      d_introduceFreshIntVars(introduceFreshIntVars)
{
  d_nm = NodeManager::currentNM();
  d_zero = d_nm->mkConst<Rational>(0);
  d_one = d_nm->mkConst<Rational>(1);
};

void IntBlaster::addRangeConstraint(Node node,
                                    uint64_t size,
                                    std::vector<Node>& lemmas)
{
}

void IntBlaster::addBitwiseConstraint(Node bitwiseConstraint,
                                      std::vector<Node>& lemmas)
{
}

Node IntBlaster::mkRangeConstraint(Node newVar, uint64_t k) { return Node(); }

Node IntBlaster::maxInt(uint64_t k) { return Node(); }

Node IntBlaster::pow2(uint64_t k) { return Node(); }

Node IntBlaster::modpow2(Node n, uint64_t exponent) { return Node(); }

Node IntBlaster::makeBinary(Node n)
{
  if (d_binarizeCache.find(n) != d_binarizeCache.end())
  {
    return d_binarizeCache[n];
  }
  uint64_t numChildren = n.getNumChildren();
  kind::Kind_t k = n.getKind();
  Node result = n;
  if ((numChildren > 2)
      && (k == kind::BITVECTOR_ADD || k == kind::BITVECTOR_MULT
          || k == kind::BITVECTOR_AND || k == kind::BITVECTOR_OR
          || k == kind::BITVECTOR_XOR || k == kind::BITVECTOR_CONCAT))
  {
    result = n[0];
    for (uint64_t i = 1; i < numChildren; i++)
    {
      result = d_nm->mkNode(n.getKind(), result, n[i]);
    }
  }
  d_binarizeCache[n] = result;
  Trace("int-blaster-debug") << "binarization result: " << result << std::endl;
  return result;
}

/**
 * Translate n to Integers via post-order traversal.
 */
Node IntBlaster::intBlast(Node n,
                          std::vector<Node>& lemmas,
                          std::map<Node, Node>& skolems)
{
  // make sure the node is re-written
  n = Rewriter::rewrite(n);

  // helper vector for traversal.
  std::vector<Node> toVisit;
  toVisit.push_back(makeBinary(n));

  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    uint64_t currentNumChildren = current.getNumChildren();
    if (d_intblastCache.find(current) == d_intblastCache.end())
    {
      // This is the first time we visit this node and it is not in the cache.
      // We mark this node as visited but not translated by assiging
      // a null node to it.
      d_intblastCache[current] = Node();
      // all the node's children are added to the stack to be visited
      // before visiting this node again.
      for (const Node& child : current)
      {
        toVisit.push_back(makeBinary(child));
      }
      // If this is a UF applicatinon, we also add the function to
      // toVisit.
      if (current.getKind() == kind::APPLY_UF)
      {
        toVisit.push_back(current.getOperator());
      }
    }
    else
    {
      // We already visited and translated this node
      if (!d_intblastCache[current].get().isNull())
      {
        // We are done computing the translation for current
        toVisit.pop_back();
      }
      else
      {
        // We are now visiting current on the way back up.
        // This is when we do the actual translation.
        Node translation;
        if (currentNumChildren == 0)
        {
          translation = translateNoChildren(current, lemmas, skolems);
        }
        else
        {
          /**
           * The current node has children.
           * Since we are on the way back up,
           * these children were already translated.
           * We save their translation for easy access.
           * If the node's kind is APPLY_UF,
           * we also need to include the translated uninterpreted function in
           * this list.
           */
          std::vector<Node> translated_children;
          if (current.getKind() == kind::APPLY_UF)
          {
            translated_children.push_back(
                d_intblastCache[current.getOperator()]);
          }
          for (uint64_t i = 0; i < currentNumChildren; i++)
          {
            translated_children.push_back(d_intblastCache[current[i]]);
          }
          translation =
              translateWithChildren(current, translated_children, lemmas);
        }

        Assert(!translation.isNull());
        // Map the current node to its translation in the cache.
        d_intblastCache[current] = translation;
        // Also map the translation to itself.
        d_intblastCache[translation] = translation;
        toVisit.pop_back();
      }
    }
  }
  return d_intblastCache[n].get();
}

Node IntBlaster::uts(Node n, uint64_t bw) { return Node(); }

Node IntBlaster::translateWithChildren(
    Node original,
    const std::vector<Node>& translated_children,
    std::vector<Node>& lemmas)
{
  Node binarized = makeBinary(original);
  // continue to process the binarized version
  return Node();
}

Node IntBlaster::translateNoChildren(Node original,
                                     std::vector<Node>& lemmas,
                                     std::map<Node, Node>& skolems)
{
  Trace("int-blaster-debug")
      << "translating leaf: " << original << "; of type: " << original.getType()
      << std::endl;

  // The result of the translation
  Node translation;

  // The translation is done differently for variables (bound or free)  and
  // constants (values)
  Assert(original.isVar() || original.isConst());
  if (original.isVar())
  {
    if (original.getType().isBitVector())
    {
      // For bit-vector variables, we create fresh integer variables.
      if (original.getKind() == kind::BOUND_VARIABLE)
      {
        // Range constraints for the bound integer variables are not added now.
        // they will be added once the quantifier itself is handled.
        std::stringstream ss;
        ss << original;
        translation = d_nm->mkBoundVar(ss.str() + "_int", d_nm->integerType());
      }
      else
      {
        // original is a bit-vector variable (symbolic constant).
        // Either we translate it to a fresh integer variable,
        // or we translate it to (bv2nat original).
        // In the former case, we must include range lemmas, while in the
        // latter we don't.
        // This is determined by the option bv-to-int-fresh-vars.
        // The variables intCast and bvCast are used for models:
        // even if we introduce a fresh variable,
        // it is associated with intCast (which is (bv2nat original)).
        // bvCast is either ( (_ nat2bv k) original) or just original.
        Node intCast = castToType(original, d_nm->integerType());
        Node bvCast;
        if (d_introduceFreshIntVars)
        {
          // we introduce a fresh variable, add range constraints, and save the
          // connection between original and the new variable via intCast
          translation = d_nm->getSkolemManager()->mkPurifySkolem(
              intCast,
              "__intblast__var",
              "Variable introduced in intblasting for " + original.toString());
          uint64_t bvsize = original.getType().getBitVectorSize();
          addRangeConstraint(translation, bvsize, lemmas);
          // put new definition of old variable in skolems
          bvCast = castToType(translation, original.getType());
        }
        else
        {
          // we just translate original to (bv2nat original)
          translation = intCast;
          // no need to do any casting back to bit-vector in this case.
          bvCast = original;
        }

        // add bvCast to skolems if it is not already there.
        if (skolems.find(original) == skolems.end())
        {
          skolems[original] = bvCast;
        }
        else
        {
          Assert(skolems[original] == bvCast);
        }
      }
    }
    else if (original.getType().isFunction())
    {
      // translate function symbol
      translation = translateFunctionSymbol(original, skolems);
    }
    else
    {
      // leave other variables intact
      translation = original;
    }
  }
  else
  {
    // original is a constant (value)
    if (original.getKind() == kind::CONST_BITVECTOR)
    {
      // Bit-vector constants are transformed into their integer value.
      BitVector constant(original.getConst<BitVector>());
      Integer c = constant.toInteger();
      translation = d_nm->mkConst<Rational>(c);
    }
    else
    {
      // Other constants stay the same.
      translation = original;
    }
  }
  return translation;
}

Node IntBlaster::translateFunctionSymbol(Node bvUF,
                                         std::map<Node, Node>& skolems)
{
  // construct the new function symbol.
  Node intUF;

  // old and new types of domain and result
  TypeNode tn = bvUF.getType();
  TypeNode bvRange = tn.getRangeType();
  std::vector<TypeNode> bvDomain = tn.getArgTypes();
  std::vector<TypeNode> intDomain;

  // if the original range is a bit-vector sort,
  // the new range should be an integer sort.
  // Otherwise, we keep the original range.
  // Similarly for the domain sorts.
  TypeNode intRange = bvRange.isBitVector() ? d_nm->integerType() : bvRange;
  for (const TypeNode& d : bvDomain)
  {
    intDomain.push_back(d.isBitVector() ? d_nm->integerType() : d);
  }

  // create the new function symbol as a skolem
  std::ostringstream os;
  os << "__intblast_fun_" << bvUF << "_int";
  SkolemManager* sm = d_nm->getSkolemManager();
  intUF = sm->mkDummySkolem(
      os.str(), d_nm->mkFunctionType(intDomain, intRange), "bv2int function");

  // add definition of old function symbol to skolems.

  // formal arguments of the lambda expression.
  std::vector<Node> args;

  // arguments to be passed in the application.
  std::vector<Node> achildren;
  achildren.push_back(intUF);

  // iterate the arguments, cast BV arguments to integers
  int i = 0;
  for (const TypeNode& d : bvDomain)
  {
    // Each bit-vector argument is casted to a natural number
    // Other arguments are left intact.
    Node fresh_bound_var = d_nm->mkBoundVar(d);
    args.push_back(fresh_bound_var);
    Node castedArg = args[i];
    if (d.isBitVector())
    {
      castedArg = castToType(castedArg, d_nm->integerType());
    }
    achildren.push_back(castedArg);
    i++;
  }

  // create the lambda expression, and add it to skolems
  Node app = d_nm->mkNode(kind::APPLY_UF, achildren);
  Node body = castToType(app, bvRange);
  Node bvlist = d_nm->mkNode(kind::BOUND_VAR_LIST, args);
  Node result = d_nm->mkNode(kind::LAMBDA, bvlist, body);
  if (skolems.find(bvUF) == skolems.end())
  {
    skolems[bvUF] = result;
  }
  return intUF;
}

bool IntBlaster::childrenTypesChanged(Node n) { return true; }

Node IntBlaster::castToType(Node n, TypeNode tn)
{
  // If there is no reason to cast, return the
  // original node.
  if (n.getType().isSubtypeOf(tn))
  {
    return n;
  }
  // We only case int to bv or vice verse.
  Assert((n.getType().isBitVector() && tn.isInteger())
         || (n.getType().isInteger() && tn.isBitVector()));
  Trace("int-blaster") << "castToType from " << n.getType() << " to " << tn
                       << std::endl;

  // casting integers to bit-vectors
  if (n.getType().isInteger())
  {
    Assert(tn.isBitVector());
    unsigned bvsize = tn.getBitVectorSize();
    Node intToBVOp = d_nm->mkConst<IntToBitVector>(IntToBitVector(bvsize));
    return d_nm->mkNode(intToBVOp, n);
  }

  // casting bit-vectors to ingers
  Assert(n.getType().isBitVector());
  Assert(tn.isInteger());
  return d_nm->mkNode(kind::BITVECTOR_TO_NAT, n);
}

Node IntBlaster::reconstructNode(Node originalNode,
                                 TypeNode resultType,
                                 const std::vector<Node>& translated_children)
{
  return Node();
}

Node IntBlaster::createShiftNode(std::vector<Node> children,
                                 uint64_t bvsize,
                                 bool isLeftShift)
{
  return Node();
}

Node IntBlaster::translateQuantifiedFormula(Node quantifiedNode)
{
  return Node();
}

}  // namespace cvc5
