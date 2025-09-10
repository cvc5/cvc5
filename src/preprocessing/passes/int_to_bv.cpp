/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Yoni Zohar, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The IntToBV preprocessing pass.
 *
 * Converts integer operations into bitvector operations. The width of the
 * bitvectors is controlled through the `--solve-int-as-bv` command line
 * option.
 */

#include "preprocessing/passes/int_to_bv.h"

#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/logic_exception.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "util/bitvector.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;


namespace {

bool childrenTypesChanged(Node n, NodeMap& cache) {
  for (Node child : n) {
    TypeNode originalType = child.getType();
    TypeNode newType = cache[child].getType();
    if (newType != originalType)
    {
      return true;
    }
  }
  return false;
}

Node intToBVMakeBinary(NodeManager* nm, TNode n, NodeMap& cache)
{
  for (TNode current : NodeDfsIterable(n, VisitOrder::POSTORDER,
           [&cache](TNode nn) { return cache.count(nn) > 0; }))
  {
    Node result;
    if (current.getNumChildren() == 0)
    {
      result = current;
    }
    else if (current.getNumChildren() > 2
             && (current.getKind() == Kind::ADD
                 || current.getKind() == Kind::MULT
                 || current.getKind() == Kind::NONLINEAR_MULT))
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
      NodeBuilder builder(nm, current.getKind());
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
}  // namespace

Node IntToBV::intToBV(TNode n, NodeMap& cache)
{
  Assert(options().smt.solveIntAsBV <= 4294967295);
  uint32_t size = options().smt.solveIntAsBV;
  AlwaysAssert(size > 0);
  AlwaysAssert(!options().base.incrementalSolving);

  NodeManager* nm = nodeManager();
  NodeMap binaryCache;
  Node n_binary = intToBVMakeBinary(nm, n, binaryCache);

  for (TNode current : NodeDfsIterable(n_binary, VisitOrder::POSTORDER,
           [&cache](TNode nn) { return cache.count(nn) > 0; }))
  {
    TypeNode tn = current.getType();
    if (tn.isReal() && !tn.isInteger())
    {
      throw TypeCheckingExceptionPrivate(
          current, string("Cannot translate to BV: ") + current.toString());
    }
    if (current.getNumChildren() > 0)
    {
      // Not a leaf
      vector<Node> children;
      uint64_t max = 0;
      for (const Node& nc : current)
      {
        Assert(cache.find(nc) != cache.end());
        TNode childRes = cache[nc];
        TypeNode type = childRes.getType();
        if (type.isBitVector())
        {
          uint32_t bvsize = type.getBitVectorSize();
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
          case Kind::ADD:
            Assert(children.size() == 2);
            newKind = Kind::BITVECTOR_ADD;
            max = max + 1;
            break;
          case Kind::MULT:
          case Kind::NONLINEAR_MULT:
            Assert(children.size() == 2);
            newKind = Kind::BITVECTOR_MULT;
            max = max * 2;
            break;
          case Kind::SUB:
            Assert(children.size() == 2);
            newKind = Kind::BITVECTOR_SUB;
            max = max + 1;
            break;
          case Kind::NEG:
            Assert(children.size() == 1);
            newKind = Kind::BITVECTOR_NEG;
            max = max + 1;
            break;
          case Kind::LT: newKind = Kind::BITVECTOR_SLT; break;
          case Kind::LEQ: newKind = Kind::BITVECTOR_SLE; break;
          case Kind::GT: newKind = Kind::BITVECTOR_SGT; break;
          case Kind::GEQ: newKind = Kind::BITVECTOR_SGE; break;
          case Kind::EQUAL:
          case Kind::ITE: break;
          default:
            if (childrenTypesChanged(current, cache)) {
              std::stringstream ss;
              ss << "Cannot translate " << current
                 << " to a bit-vector term. Remove option `--solve-int-as-bv`.";
              throw LogicException(ss.str());
            }
            break;
        }

        for (size_t i = 0, csize = children.size(); i < csize; ++i)
        {
          TypeNode type = children[i].getType();
          if (!type.isBitVector())
          {
            continue;
          }
          uint32_t bvsize = type.getBitVectorSize();
          if (bvsize < max)
          {
            // sign extend
            Node signExtendOp = nm->mkConst<BitVectorSignExtend>(
                BitVectorSignExtend(max - bvsize));
            children[i] = nm->mkNode(signExtendOp, children[i]);
          }
        }
      }

      // abort if the kind did not change and
      // the original type was integer.
      // The only exception is an ITE,
      // in which case we continue.
      if (tn.isInteger() && newKind != Kind::ITE
          && newKind == current.getKind())
      {
        std::stringstream ss;
        ss << "Cannot translate the operator " << current.getKind()
           << " to a bit-vector operator. Remove option `--solve-int-as-bv`.";
        throw LogicException(ss.str());
      }
      NodeBuilder builder(nm, newKind);
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << current.getOperator();
      }
      builder.append(children);
      // Mark the substitution and continue
      Node result = builder;

      result = rewrite(result);
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
          result =
              NodeManager::mkDummySkolem("__intToBV_var",
                                         nm->mkBitVectorType(size),
                                         "Variable introduced in intToBV pass");
          /**
           * Correctly convert signed/unsigned BV values to Integers as follows
           * x < 0 ? -nat(-x) : nat(x)
           * where x refers to the bit-vector term `result`.
           */
          BitVector bvzero(size, Integer(0));
          Node negResult = nm->mkNode(Kind::BITVECTOR_UBV_TO_INT,
                                      nm->mkNode(Kind::BITVECTOR_NEG, result));
          Node bv2int = nm->mkNode(
              Kind::ITE,
              nm->mkNode(Kind::BITVECTOR_SLT, result, nm->mkConst(bvzero)),
              nm->mkNode(Kind::NEG, negResult),
              nm->mkNode(Kind::BITVECTOR_UBV_TO_INT, result));
          d_preprocContext->addSubstitution(current, bv2int);
        }
      }
      else if (current.isConst())
      {
        if (current.getType().isInteger())
        {
          Rational constant = current.getConst<Rational>();
          Assert (constant.isIntegral());
          BitVector bv(size, constant.getNumerator());
          if (bv.toSignedInteger() != constant.getNumerator())
          {
            throw TypeCheckingExceptionPrivate(
                current,
                string("Not enough bits for constant in intToBV: ")
                    + current.toString());
          }
          result = nm->mkConst(bv);
        }
      }
      else
      {
        throw TypeCheckingExceptionPrivate(
            current, string("Cannot translate to BV: ") + current.toString());
      }
      cache[current] = result;
    }
  }
  Trace("int-to-bv-debug") << "original: " << n << std::endl;
  Trace("int-to-bv-debug") << "binary: " << n_binary << std::endl;
  Trace("int-to-bv-debug") << "result: " << cache[n_binary] << std::endl;
  return cache[n_binary];
}

IntToBV::IntToBV(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "int-to-bv"){};

PreprocessingPassResult IntToBV::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // this pass is refutation unsound, "unsat" will be "unknown"
  assertionsToPreprocess->markRefutationUnsound();
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
}  // namespace cvc5::internal
