/*********************                                                        */
/*! \file int_to_bv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Yoni Zohar, Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The IntToBV preprocessing pass
 **
 ** Converts integer operations into bitvector operations. The width of the
 ** bitvectors is controlled through the `--solve-int-as-bv` command line
 ** option.
 **/

#include "preprocessing/passes/int_to_bv.h"

#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

using NodeMap = std::unordered_map<Node, Node, NodeHashFunction>;

namespace {

bool childrenTypesChanged(Node n, NodeMap& cache) {
  for (Node child : n) {
    TypeNode originalType = child.getType();
    TypeNode newType = cache[child].getType();
    if (! newType.isSubtypeOf(originalType)) {
      return true;
    }
  }
  return false;
}


Node intToBVMakeBinary(TNode n, NodeMap& cache)
{
  for (TNode current : NodeDfsIterable(n, VisitOrder::POSTORDER,
           [&cache](TNode nn) { return cache.count(nn) > 0; }))
  {
    Node result;
    NodeManager* nm = NodeManager::currentNM();
    if (current.getNumChildren() == 0)
    {
      result = current;
    }
    else if (current.getNumChildren() > 2
             && (current.getKind() == kind::PLUS
                 || current.getKind() == kind::MULT))
    {
      Assert(cache.find(current[0]) != cache.end());
      result = cache[current[0]];
      for (unsigned i = 1; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        Node child = current[i];
        Node childRes = cache[current[i]];
        result = nm->mkNode(current.getKind(), result, childRes);
      }
    }
    else
    {
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << current.getOperator();
      }

      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        builder << cache[current[i]];
      }
      result = builder;
    }
    cache[current] = result;
  }
  return cache[n];
}

Node intToBV(TNode n, NodeMap& cache)
{
  int size = options::solveIntAsBV();
  AlwaysAssert(size > 0);
  AlwaysAssert(!options::incrementalSolving());

  NodeMap binaryCache;
  Node n_binary = intToBVMakeBinary(n, binaryCache);

  for (TNode current : NodeDfsIterable(n_binary, VisitOrder::POSTORDER,
           [&cache](TNode nn) { return cache.count(nn) > 0; }))
  {
    NodeManager* nm = NodeManager::currentNM();
    if (current.getNumChildren() > 0)
    {
      // Not a leaf
      vector<Node> children;
      unsigned max = 0;
      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        TNode childRes = cache[current[i]];
        TypeNode type = childRes.getType();
        if (type.isBitVector())
        {
          unsigned bvsize = type.getBitVectorSize();
          if (bvsize > max)
          {
            max = bvsize;
          }
        }
        children.push_back(childRes);
      }

      kind::Kind_t newKind = current.getKind();
      if (max > 0)
      {
        switch (newKind)
        {
          case kind::PLUS:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_PLUS;
            max = max + 1;
            break;
          case kind::MULT:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_MULT;
            max = max * 2;
            break;
          case kind::MINUS:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_SUB;
            max = max + 1;
            break;
          case kind::UMINUS:
            Assert(children.size() == 1);
            newKind = kind::BITVECTOR_NEG;
            max = max + 1;
            break;
          case kind::LT: newKind = kind::BITVECTOR_SLT; break;
          case kind::LEQ: newKind = kind::BITVECTOR_SLE; break;
          case kind::GT: newKind = kind::BITVECTOR_SGT; break;
          case kind::GEQ: newKind = kind::BITVECTOR_SGE; break;
          case kind::EQUAL:
          case kind::ITE: break;
          default:
            if (childrenTypesChanged(current, cache)) {
              throw TypeCheckingException(
                current.toExpr(),
                string("Cannot translate to BV: ") + current.toString());
            }
            break;
        }
        for (unsigned i = 0; i < children.size(); ++i)
        {
          TypeNode type = children[i].getType();
          if (!type.isBitVector())
          {
            continue;
          }
          unsigned bvsize = type.getBitVectorSize();
          if (bvsize < max)
          {
            // sign extend
            Node signExtendOp = nm->mkConst<BitVectorSignExtend>(
                BitVectorSignExtend(max - bvsize));
            children[i] = nm->mkNode(signExtendOp, children[i]);
          }
        }
      }
      NodeBuilder<> builder(newKind);
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << current.getOperator();
      }
      for (unsigned i = 0; i < children.size(); ++i)
      {
        builder << children[i];
      }
      // Mark the substitution and continue
      Node result = builder;

      result = Rewriter::rewrite(result);
      cache[current] = result;
    }
    else
    {
      // It's a leaf: could be a variable or a numeral
      Node result = current;
      if (current.isVar())
      {
        if (current.getType() == nm->integerType())
        {
          result = nm->mkSkolem("__intToBV_var",
                                nm->mkBitVectorType(size),
                                "Variable introduced in intToBV pass");
        }
      }
      else if (current.isConst())
      {
        switch (current.getKind())
        {
          case kind::CONST_RATIONAL:
          {
            Rational constant = current.getConst<Rational>();
            if (constant.isIntegral()) {
              AlwaysAssert(constant >= 0);
              BitVector bv(size, constant.getNumerator());
              if (bv.toSignedInteger() != constant.getNumerator())
              {
                throw TypeCheckingException(
                    current.toExpr(),
                    string("Not enough bits for constant in intToBV: ")
                        + current.toString());
              }
              result = nm->mkConst(bv);
            }
            break;
          }
          default: break;
        }
      }
      else
      {
        throw TypeCheckingException(
            current.toExpr(),
            string("Cannot translate to BV: ") + current.toString());
      }
      cache[current] = result;
    }
  }
  return cache[n_binary];
}
}  // namespace

IntToBV::IntToBV(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "int-to-bv"){};

PreprocessingPassResult IntToBV::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeMap cache;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, intToBV((*assertionsToPreprocess)[i], cache));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
