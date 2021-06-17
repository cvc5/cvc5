/*********************                                                        */
/*! \file int_blaster.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar, Andrew Reynolds, Andres Noetzli
 ** This file is part of the cvc5 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The bit-blaster utility
 **
 ** Converts bit-vector operations into integer operations.
 **
 **/

#include "theory/bv/int_blaster.h"

#include <cmath>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "options/option_exception.h"
#include "options/uf_options.h"
#include "theory/rewriter.h"
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
  for (TNode current : NodeDfsIterable(n,
                                       VisitOrder::POSTORDER,
                                       // skip visited nodes
                                       [this](TNode tn) {
                                         return d_binarizeCache.find(tn)
                                                != d_binarizeCache.end();
                                       }))
  {
    uint64_t numChildren = current.getNumChildren();
    /*
     * We already visited the sub-dag rooted at the current node,
     * and binarized all its children.
     * Now we binarize the current node itself.
     */
    kind::Kind_t k = current.getKind();
    // We only binarize bvadd, bvmul, bvand, bvor, bvxor, bvconcat
    if ((numChildren > 2)
        && (k == kind::BITVECTOR_ADD || k == kind::BITVECTOR_MULT
            || k == kind::BITVECTOR_AND || k == kind::BITVECTOR_OR
            || k == kind::BITVECTOR_XOR || k == kind::BITVECTOR_CONCAT))
    {
      Assert(d_binarizeCache.find(current[0]) != d_binarizeCache.end());
      Node result = d_binarizeCache[current[0]];
      for (uint64_t i = 1; i < numChildren; i++)
      {
        Assert(d_binarizeCache.find(current[i]) != d_binarizeCache.end());
        Node child = d_binarizeCache[current[i]];
        result = d_nm->mkNode(current.getKind(), result, child);
      }
      d_binarizeCache[current] = result;
    }
    else if (numChildren > 0)
    {
      // current has children, but we do not binarize it
      NodeBuilder builder(k);
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        builder << current.getOperator();
      }
      for (Node child : current)
      {
        builder << d_binarizeCache[child].get();
      }
      d_binarizeCache[current] = builder.constructNode();
    }
    else
    {
      // current has no children
      d_binarizeCache[current] = current;
    }
  }
  return d_binarizeCache[n];
}

/**
 * Translate n to Integers via post-order traversal.
 */
Node IntBlaster::intBlast(Node n,
                          std::vector<Node>& lemmas,
                          std::map<Node, Node>& skolems)
{
  // make sure the node is re-written and binarized before processing it.
  n = Rewriter::rewrite(n);
  n = makeBinary(n);

  // helper vector for traversal.
  std::vector<Node> toVisit;
  toVisit.push_back(n);

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
      toVisit.insert(toVisit.end(), current.begin(), current.end());
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

Node IntBlaster::unsignedToSigned(Node n, uint64_t bw) { return Node(); }

Node IntBlaster::translateWithChildren(
    Node original,
    const std::vector<Node>& translated_children,
    std::vector<Node>& lemmas)
{
  return Node();
}

Node IntBlaster::translateNoChildren(Node original,
                                     std::vector<Node>& lemmas,
                                     std::map<Node, Node>& skolems)
{
  return Node();
}

Node IntBlaster::defineBVUFAsIntUF(Node bvUF, Node intUF) { return Node(); }

Node IntBlaster::translateFunctionSymbol(Node bvUF,
                                         std::map<Node, Node>& skolems)
{
  return Node();
}

bool IntBlaster::childrenTypesChanged(Node n) { return true; }

Node IntBlaster::castToType(Node n, TypeNode tn) { return Node(); }

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

Node IntBlaster::createBVNotNode(Node n, uint64_t bvsize) { return Node(); }

}  // namespace cvc5
