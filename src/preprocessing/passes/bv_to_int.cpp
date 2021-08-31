/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BVToInt preprocessing pass.
 *
 * Converts bit-vector operations into integer operations.
 *
 */

#include "preprocessing/passes/bv_to_int.h"

#include <cmath>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/bv/theory_bv_rewrite_rules_operator_elimination.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "util/iand.h"
#include "util/rational.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::theory;
using namespace cvc5::theory::bv;

namespace {

Rational intpow2(uint64_t b)
{
  return Rational(Integer(2).pow(b), Integer(1));
}

} //end empty namespace

Node BVToInt::mkRangeConstraint(Node newVar, uint64_t k)
{
  Node lower = d_nm->mkNode(kind::LEQ, d_zero, newVar);
  Node upper = d_nm->mkNode(kind::LT, newVar, pow2(k));
  Node result = d_nm->mkNode(kind::AND, lower, upper);
  return Rewriter::rewrite(result);
}

Node BVToInt::maxInt(uint64_t k)
{
  Assert(k > 0);
  Rational max_value = intpow2(k) - 1;
  return d_nm->mkConst<Rational>(max_value);
}

Node BVToInt::pow2(uint64_t k)
{
  Assert(k >= 0);
  return d_nm->mkConst<Rational>(intpow2(k));
}

Node BVToInt::modpow2(Node n, uint64_t exponent)
{
  Node p2 = d_nm->mkConst<Rational>(intpow2(exponent));
  return d_nm->mkNode(kind::INTS_MODULUS_TOTAL, n, p2);
}

/**
 * Binarizing n via post-order traversal.
 */
Node BVToInt::makeBinary(Node n)
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
    if ((numChildren > 2)
        && (k == kind::BITVECTOR_ADD || k == kind::BITVECTOR_MULT
            || k == kind::BITVECTOR_AND || k == kind::BITVECTOR_OR
            || k == kind::BITVECTOR_XOR || k == kind::BITVECTOR_CONCAT))
    {
      // We only binarize bvadd, bvmul, bvand, bvor, bvxor, bvconcat
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
 * We traverse n and perform rewrites both on the way down and on the way up.
 * On the way down we rewrite the node but not it's children.
 * On the way up, we update the node's children to the rewritten ones.
 * For each sub-node, we perform rewrites to eliminate operators.
 * Then, the original children are added to toVisit stack so that we rewrite
 * them as well.
 */
Node BVToInt::eliminationPass(Node n)
{
  std::vector<Node> toVisit;
  toVisit.push_back(n);
  Node current;
  while (!toVisit.empty())
  {
    current = toVisit.back();
    // assert that the node is binarized
    // The following variable is only used in assertions
    CVC5_UNUSED kind::Kind_t k = current.getKind();
    uint64_t numChildren = current.getNumChildren();
    Assert((numChildren == 2)
           || !(k == kind::BITVECTOR_ADD || k == kind::BITVECTOR_MULT
                || k == kind::BITVECTOR_AND || k == kind::BITVECTOR_OR
                || k == kind::BITVECTOR_XOR || k == kind::BITVECTOR_CONCAT));
    toVisit.pop_back();
    bool inEliminationCache =
        (d_eliminationCache.find(current) != d_eliminationCache.end());
    bool inRebuildCache =
        (d_rebuildCache.find(current) != d_rebuildCache.end());
    if (!inEliminationCache)
    {
      // current is not the elimination of any previously-visited node
      // current hasn't been eliminated yet.
      // eliminate operators from it using rewrite rules
      Node currentEliminated =
          FixpointRewriteStrategy<RewriteRule<UdivZero>,
                                  RewriteRule<SdivEliminateFewerBitwiseOps>,
                                  RewriteRule<SremEliminateFewerBitwiseOps>,
                                  RewriteRule<SmodEliminateFewerBitwiseOps>,
                                  RewriteRule<XnorEliminate>,
                                  RewriteRule<NandEliminate>,
                                  RewriteRule<NorEliminate>,
                                  RewriteRule<NegEliminate>,
                                  RewriteRule<XorEliminate>,
                                  RewriteRule<OrEliminate>,
                                  RewriteRule<SubEliminate>,
                                  RewriteRule<RepeatEliminate>,
                                  RewriteRule<RotateRightEliminate>,
                                  RewriteRule<RotateLeftEliminate>,
                                  RewriteRule<CompEliminate>,
                                  RewriteRule<SleEliminate>,
                                  RewriteRule<SltEliminate>,
                                  RewriteRule<SgtEliminate>,
                                  RewriteRule<SgeEliminate>>::apply(current);

      // save in the cache
      d_eliminationCache[current] = currentEliminated;
      // also assign the eliminated now to itself to avoid revisiting.
      d_eliminationCache[currentEliminated] = currentEliminated;
      // put the eliminated node in the rebuild cache, but mark that it hasn't
      // yet been rebuilt by assigning null.
      d_rebuildCache[currentEliminated] = Node();
      // Push the eliminated node to the stack
      toVisit.push_back(currentEliminated);
      // Add the children to the stack for future processing.
      toVisit.insert(
          toVisit.end(), currentEliminated.begin(), currentEliminated.end());
    }
    if (inRebuildCache)
    {
      // current was already added to the rebuild cache.
      if (d_rebuildCache[current].get().isNull())
      {
        // current wasn't rebuilt yet.
        numChildren = current.getNumChildren();
        if (numChildren == 0)
        {
          // We only eliminate operators that are not nullary.
          d_rebuildCache[current] = current;
        }
        else
        {
          // The main operator is replaced, and the children
          // are replaced with their eliminated counterparts.
          NodeBuilder builder(current.getKind());
          if (current.getMetaKind() == kind::metakind::PARAMETERIZED)
          {
            builder << current.getOperator();
          }
          for (Node child : current)
          {
            Assert(d_eliminationCache.find(child) != d_eliminationCache.end());
            Node eliminatedChild = d_eliminationCache[child];
            Assert(d_rebuildCache.find(eliminatedChild) != d_eliminationCache.end());
            Assert(!d_rebuildCache[eliminatedChild].get().isNull());
            builder << d_rebuildCache[eliminatedChild].get();
          }
          d_rebuildCache[current] = builder.constructNode();
        }
      }
    }
  }
  Assert(d_eliminationCache.find(n) != d_eliminationCache.end());
  Node eliminated = d_eliminationCache[n];
  Assert(d_rebuildCache.find(eliminated) != d_rebuildCache.end());
  Assert(!d_rebuildCache[eliminated].get().isNull());
  return d_rebuildCache[eliminated];
}

/**
 * Translate n to Integers via post-order traversal.
 */
Node BVToInt::bvToInt(Node n)
{
  // make sure the node is re-written before processing it.
  n = Rewriter::rewrite(n);
  n = makeBinary(n);
  n = eliminationPass(n);
  // binarize again, in case the elimination pass introduced
  // non-binary terms (as can happen by RepeatEliminate, for example).
  n = makeBinary(n);
  vector<Node> toVisit;
  toVisit.push_back(n);

  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    uint64_t currentNumChildren = current.getNumChildren();
    if (d_bvToIntCache.find(current) == d_bvToIntCache.end())
    {
      // This is the first time we visit this node and it is not in the cache.
      // We mark this node as visited but not translated by assiging
      // a null node to it.
      d_bvToIntCache[current] = Node();
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
      if (!d_bvToIntCache[current].get().isNull())
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
          translation = translateNoChildren(current);
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
          vector<Node> translated_children;
          if (current.getKind() == kind::APPLY_UF)
          {
            translated_children.push_back(
                d_bvToIntCache[current.getOperator()]);
          }
          for (uint64_t i = 0; i < currentNumChildren; i++)
          {
            translated_children.push_back(d_bvToIntCache[current[i]]);
          }
          translation = translateWithChildren(current, translated_children);
        }
        // Map the current node to its translation in the cache.
        d_bvToIntCache[current] = translation;
        // Also map the translation to itself.
        d_bvToIntCache[translation] = translation;
        toVisit.pop_back();
      }
    }
  }
  return d_bvToIntCache[n].get();
}

Node BVToInt::translateWithChildren(Node original,
                                    const vector<Node>& translated_children)
{
  // The translation of the original node is determined by the kind of
  // the node.
  kind::Kind_t oldKind = original.getKind();
  // ultbv and sltbv were supposed to be eliminated before this point.
  Assert(oldKind != kind::BITVECTOR_ULTBV);
  Assert(oldKind != kind::BITVECTOR_SLTBV);
  // The following variable will only be used in assertions.
  CVC5_UNUSED uint64_t originalNumChildren = original.getNumChildren();
  Node returnNode;
  switch (oldKind)
  {
    case kind::BITVECTOR_ADD:
    {
      Assert(originalNumChildren == 2);
      uint64_t bvsize = original[0].getType().getBitVectorSize();
      Node plus = d_nm->mkNode(kind::PLUS, translated_children);
      Node p2 = pow2(bvsize);
      returnNode = d_nm->mkNode(kind::INTS_MODULUS_TOTAL, plus, p2);
      break;
    }
    case kind::BITVECTOR_MULT:
    {
      Assert(originalNumChildren == 2);
      uint64_t bvsize = original[0].getType().getBitVectorSize();
      Node mult = d_nm->mkNode(kind::MULT, translated_children);
      Node p2 = pow2(bvsize);
      returnNode = d_nm->mkNode(kind::INTS_MODULUS_TOTAL, mult, p2);
      break;
    }
    case kind::BITVECTOR_UDIV:
    {
      uint64_t bvsize = original[0].getType().getBitVectorSize();
      // we use an ITE for the case where the second operand is 0.
      Node pow2BvSize = pow2(bvsize);
      Node divNode =
          d_nm->mkNode(kind::INTS_DIVISION_TOTAL, translated_children);
      returnNode = d_nm->mkNode(
          kind::ITE,
          d_nm->mkNode(kind::EQUAL, translated_children[1], d_zero),
          d_nm->mkNode(kind::MINUS, pow2BvSize, d_one),
          divNode);
      break;
    }
    case kind::BITVECTOR_UREM:
    {
      // we use an ITE for the case where the second operand is 0.
      Node modNode =
          d_nm->mkNode(kind::INTS_MODULUS_TOTAL, translated_children);
      returnNode = d_nm->mkNode(
          kind::ITE,
          d_nm->mkNode(kind::EQUAL, translated_children[1], d_zero),
          translated_children[0],
          modNode);
      break;
    }
    case kind::BITVECTOR_NOT:
    {
      uint64_t bvsize = original[0].getType().getBitVectorSize();
      // we use a specified function to generate the node.
      returnNode = createBVNotNode(translated_children[0], bvsize);
      break;
    }
    case kind::BITVECTOR_TO_NAT:
    {
      // In this case, we already translated the child to integer.
      // So the result is the translated child.
      returnNode = translated_children[0];
      break;
    }
    case kind::INT_TO_BITVECTOR:
    {
      // ((_ int2bv n) t) ---> (mod t 2^n)
      size_t sz = original.getOperator().getConst<IntToBitVector>().d_size;
      returnNode = d_nm->mkNode(
          kind::INTS_MODULUS_TOTAL, translated_children[0], pow2(sz));
    }
    break;
    case kind::BITVECTOR_AND:
    {
      // We support three configurations:
      // 1. translating to IAND
      // 2. translating back to BV (using BITVECTOR_TO_NAT and INT_TO_BV
      // operators)
      // 3. translating into a sum
      uint64_t bvsize = original[0].getType().getBitVectorSize();
      if (options::solveBVAsInt() == options::SolveBVAsIntMode::IAND)
      {
        Node iAndOp = d_nm->mkConst(IntAnd(bvsize));
        returnNode = d_nm->mkNode(
            kind::IAND, iAndOp, translated_children[0], translated_children[1]);
      }
      else if (options::solveBVAsInt() == options::SolveBVAsIntMode::BV)
      {
        // translate the children back to BV
        Node intToBVOp = d_nm->mkConst<IntToBitVector>(IntToBitVector(bvsize));
        Node x = translated_children[0];
        Node y = translated_children[1];
        Node bvx = d_nm->mkNode(intToBVOp, x);
        Node bvy = d_nm->mkNode(intToBVOp, y);
        // perform bvand on the bit-vectors
        Node bvand = d_nm->mkNode(kind::BITVECTOR_AND, bvx, bvy);
        // translate the result to integers
        returnNode = d_nm->mkNode(kind::BITVECTOR_TO_NAT, bvand);
      }
      else
      {
        Assert(options::solveBVAsInt() == options::SolveBVAsIntMode::SUM);
        // Construct a sum of ites, based on granularity.
        Assert(translated_children.size() == 2);
        returnNode =
            d_iandUtils.createSumNode(translated_children[0],
                                      translated_children[1],
                                      bvsize,
                                      options::BVAndIntegerGranularity());
      }
      break;
    }
    case kind::BITVECTOR_SHL:
    {
      /**
       * a << b is a*2^b.
       * The exponentiation is simulated by an ite.
       * Only cases where b <= bit width are considered.
       * Otherwise, the result is 0.
       */
      uint64_t bvsize = original[0].getType().getBitVectorSize();
      returnNode = createShiftNode(translated_children, bvsize, true);
      break;
    }
    case kind::BITVECTOR_LSHR:
    {
      /**
       * a >> b is a div 2^b.
       * The exponentiation is simulated by an ite.
       * Only cases where b <= bit width are considered.
       * Otherwise, the result is 0.
       */
      uint64_t bvsize = original[0].getType().getBitVectorSize();
      returnNode = createShiftNode(translated_children, bvsize, false);
      break;
    }
    case kind::BITVECTOR_ASHR:
    {
      /*  From SMT-LIB2:
       *  (bvashr s t) abbreviates
       *     (ite (= ((_ extract |m-1| |m-1|) s) #b0)
       *          (bvlshr s t)
       *          (bvnot (bvlshr (bvnot s) t)))
       *
       *  Equivalently:
       *  (bvashr s t) abbreviates
       *      (ite (bvult s 100000...)
       *           (bvlshr s t)
       *           (bvnot (bvlshr (bvnot s) t)))
       *
       */
      uint64_t bvsize = original[0].getType().getBitVectorSize();
      // signed_min is 100000...
      Node signed_min = pow2(bvsize - 1);
      Node condition =
          d_nm->mkNode(kind::LT, translated_children[0], signed_min);
      Node thenNode = createShiftNode(translated_children, bvsize, false);
      vector<Node> children = {createBVNotNode(translated_children[0], bvsize),
                               translated_children[1]};
      Node elseNode =
          createBVNotNode(createShiftNode(children, bvsize, false), bvsize);
      returnNode = d_nm->mkNode(kind::ITE, condition, thenNode, elseNode);
      break;
    }
    case kind::BITVECTOR_ITE:
    {
      // Lifted to a boolean ite.
      Node cond = d_nm->mkNode(kind::EQUAL, translated_children[0], d_one);
      returnNode = d_nm->mkNode(
          kind::ITE, cond, translated_children[1], translated_children[2]);
      break;
    }
    case kind::BITVECTOR_ZERO_EXTEND:
    {
      returnNode = translated_children[0];
      break;
    }
    case kind::BITVECTOR_SIGN_EXTEND:
    {
      uint64_t bvsize = original[0].getType().getBitVectorSize();
      Node arg = translated_children[0];
      if (arg.isConst())
      {
        Rational c(arg.getConst<Rational>());
        Rational twoToKMinusOne(intpow2(bvsize - 1));
        uint64_t amount = bv::utils::getSignExtendAmount(original);
        /* if the msb is 0, this is like zero_extend.
         *  msb is 0 <-> the value is less than 2^{bvsize-1}
         */
        if (c < twoToKMinusOne || amount == 0)
        {
          returnNode = arg;
        }
        else
        {
          /* otherwise, we add the integer equivalent of
           * 11....1 `amount` times
           */
          Rational max_of_amount = intpow2(amount) - 1;
          Rational mul = max_of_amount * intpow2(bvsize);
          Rational sum = mul + c;
          returnNode = d_nm->mkConst(sum);
        }
      }
      else
      {
        uint64_t amount = bv::utils::getSignExtendAmount(original);
        if (amount == 0)
        {
          returnNode = translated_children[0];
        }
        else
        {
          Rational twoToKMinusOne(intpow2(bvsize - 1));
          Node minSigned = d_nm->mkConst(twoToKMinusOne);
          /* condition checks whether the msb is 1.
           * This holds when the integer value is smaller than
           * 100...0, which is 2^{bvsize-1}.
           */
          Node condition = d_nm->mkNode(kind::LT, arg, minSigned);
          Node thenResult = arg;
          Node left = maxInt(amount);
          Node mul = d_nm->mkNode(kind::MULT, left, pow2(bvsize));
          Node sum = d_nm->mkNode(kind::PLUS, mul, arg);
          Node elseResult = sum;
          Node ite = d_nm->mkNode(kind::ITE, condition, thenResult, elseResult);
          returnNode = ite;
        }
      }
      break;
    }
    case kind::BITVECTOR_CONCAT:
    {
      // (concat a b) translates to a*2^k+b, k being the bitwidth of b.
      uint64_t bvsizeRight = original[1].getType().getBitVectorSize();
      Node pow2BvSizeRight = pow2(bvsizeRight);
      Node a =
          d_nm->mkNode(kind::MULT, translated_children[0], pow2BvSizeRight);
      Node b = translated_children[1];
      returnNode = d_nm->mkNode(kind::PLUS, a, b);
      break;
    }
    case kind::BITVECTOR_EXTRACT:
    {
      // ((_ extract i j) a) is a / 2^j mod 2^{i-j+1}
      // original = a[i:j]
      uint64_t i = bv::utils::getExtractHigh(original);
      uint64_t j = bv::utils::getExtractLow(original);
      Assert(i >= j);
      Node div = d_nm->mkNode(
          kind::INTS_DIVISION_TOTAL, translated_children[0], pow2(j));
      returnNode = modpow2(div, i - j + 1);
      break;
    }
    case kind::EQUAL:
    {
      returnNode = d_nm->mkNode(kind::EQUAL, translated_children);
      break;
    }
    case kind::BITVECTOR_ULT:
    {
      returnNode = d_nm->mkNode(kind::LT, translated_children);
      break;
    }
    case kind::BITVECTOR_ULE:
    {
      returnNode = d_nm->mkNode(kind::LEQ, translated_children);
      break;
    }
    case kind::BITVECTOR_UGT:
    {
      returnNode = d_nm->mkNode(kind::GT, translated_children);
      break;
    }
    case kind::BITVECTOR_UGE:
    {
      returnNode = d_nm->mkNode(kind::GEQ, translated_children);
      break;
    }
    case kind::LT:
    {
      returnNode = d_nm->mkNode(kind::LT, translated_children);
      break;
    }
    case kind::LEQ:
    {
      returnNode = d_nm->mkNode(kind::LEQ, translated_children);
      break;
    }
    case kind::GT:
    {
      returnNode = d_nm->mkNode(kind::GT, translated_children);
      break;
    }
    case kind::GEQ:
    {
      returnNode = d_nm->mkNode(kind::GEQ, translated_children);
      break;
    }
    case kind::ITE:
    {
      returnNode = d_nm->mkNode(oldKind, translated_children);
      break;
    }
    case kind::APPLY_UF:
    {
      /**
       * higher order logic allows comparing between functions
       * The translation does not support this,
       * as the translated functions may be different outside
       * of the bounds that were relevant for the original
       * bit-vectors.
       */
      if (childrenTypesChanged(original) && options::ufHo())
      {
        throw TypeCheckingExceptionPrivate(
            original,
            string("Cannot translate to Int: ") + original.toString());
      }
      // Insert the translated application term to the cache
      returnNode = d_nm->mkNode(kind::APPLY_UF, translated_children);
      // Add range constraints if necessary.
      // If the original range was a BV sort, the original application of
      // the function Must be within the range determined by the
      // bitwidth.
      if (original.getType().isBitVector())
      {
        d_rangeAssertions.insert(mkRangeConstraint(
            returnNode, original.getType().getBitVectorSize()));
      }
      break;
    }
    case kind::BOUND_VAR_LIST:
    {
      returnNode = d_nm->mkNode(oldKind, translated_children);
      break;
    }
    case kind::FORALL:
    {
      returnNode = translateQuantifiedFormula(original);
      break;
    }
    default:
    {
      Assert(oldKind != kind::EXISTS);  // Exists is eliminated by the rewriter.
      // In the default case, we have reached an operator that we do not
      // translate directly to integers. The children whose types have
      // changed from bv to int should be adjusted back to bv and then
      // this term is reconstructed.
      TypeNode resultingType;
      if (original.getType().isBitVector())
      {
        resultingType = d_nm->integerType();
      }
      else
      {
        resultingType = original.getType();
      }
      Node reconstruction =
          reconstructNode(original, resultingType, translated_children);
      returnNode = reconstruction;
      break;
    }
  }
  Trace("bv-to-int-debug") << "original: " << original << endl;
  Trace("bv-to-int-debug") << "returnNode: " << returnNode << endl;
  return returnNode;
}

Node BVToInt::translateNoChildren(Node original)
{
  SkolemManager* sm = d_nm->getSkolemManager();
  Node translation;
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
        // New integer variables  that are not bound (symbolic constants)
        // are added together with range constraints induced by the 
        // bit-width of the original bit-vector variables.
        Node newVar = sm->mkDummySkolem("__bvToInt_var",
                                        d_nm->integerType(),
                                        "Variable introduced in bvToInt "
                                        "pass instead of original variable "
                                            + original.toString());
        uint64_t bvsize = original.getType().getBitVectorSize();
        translation = newVar;
        d_rangeAssertions.insert(mkRangeConstraint(newVar, bvsize));
        defineBVUFAsIntUF(original, newVar);
      }
    }
    else if (original.getType().isFunction())
    {
      translation = translateFunctionSymbol(original);
    }
    else
    {
      // variables other than bit-vector variables and function symbols
      // are left intact
      translation = original;
    }
  }
  else
  {
    // original is a const
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

Node BVToInt::translateFunctionSymbol(Node bvUF)
{
  // construct the new function symbol.
  Node intUF;
  TypeNode tn = bvUF.getType();
  TypeNode bvRange = tn.getRangeType();
  // The function symbol has not been converted yet
  vector<TypeNode> bvDomain = tn.getArgTypes();
  vector<TypeNode> intDomain;
  /**
   * if the original range is a bit-vector sort,
   * the new range should be an integer sort.
   * Otherwise, we keep the original range.
   * Similarly for the domains.
   */
  TypeNode intRange = bvRange.isBitVector() ? d_nm->integerType() : bvRange;
  for (TypeNode d : bvDomain)
  {
    intDomain.push_back(d.isBitVector() ? d_nm->integerType() : d);
  }
  SkolemManager* sm = d_nm->getSkolemManager();
  ostringstream os;
  os << "__bvToInt_fun_" << bvUF << "_int";
  intUF = sm->mkDummySkolem(
      os.str(), d_nm->mkFunctionType(intDomain, intRange), "bv2int function");
  // introduce a `define-fun` in the smt-engine to keep
  // the correspondence between the original
  // function symbol and the new one.
  defineBVUFAsIntUF(bvUF, intUF);
  return intUF;
}

void BVToInt::defineBVUFAsIntUF(Node bvUF, Node intUF)
{
  // The resulting term
  Node result;
  // The type of the resulting term
  TypeNode resultType;
  // symbolic arguments of original function
  vector<Node> args;
  if (!bvUF.getType().isFunction()) {
    // bvUF is a variable.
    // in this case, the result is just the original term
    // (it will be casted later if needed)
    result = intUF;
    resultType = bvUF.getType();
  } else {
    // bvUF is a function with arguments
    // The arguments need to be casted as well.
    TypeNode tn = bvUF.getType();
    resultType = tn.getRangeType();
    vector<TypeNode> bvDomain = tn.getArgTypes();
    // children of the new symbolic application
    vector<Node> achildren;
    achildren.push_back(intUF);
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
    result = d_nm->mkNode(kind::APPLY_UF, achildren);
  }
  // If the result is BV, it needs to be casted back.
  result = castToType(result, resultType);
  // add the substitution to the preprocessing context, which ensures the
  // model for bvUF is correct, as well as substituting it in the input
  // assertions when necessary.
  if (!args.empty())
  {
    result = d_nm->mkNode(
        kind::LAMBDA, d_nm->mkNode(kind::BOUND_VAR_LIST, args), result);
  }
  d_preprocContext->addSubstitution(bvUF, result);
}

bool BVToInt::childrenTypesChanged(Node n)
{
  bool result = false;
  for (const Node& child : n)
  {
    TypeNode originalType = child.getType();
    TypeNode newType = d_bvToIntCache[child].get().getType();
    if (!newType.isSubtypeOf(originalType))
    {
      result = true;
      break;
    }
  }
  return result;
}

Node BVToInt::castToType(Node n, TypeNode tn)
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
  if (n.getType().isInteger())
  {
    Assert(tn.isBitVector());
    unsigned bvsize = tn.getBitVectorSize();
    Node intToBVOp = d_nm->mkConst<IntToBitVector>(IntToBitVector(bvsize));
    return d_nm->mkNode(intToBVOp, n);
  }
  Assert(n.getType().isBitVector());
  Assert(tn.isInteger());
  return d_nm->mkNode(kind::BITVECTOR_TO_NAT, n);
}

Node BVToInt::reconstructNode(Node originalNode,
                              TypeNode resultType,
                              const vector<Node>& translated_children)
{
  // first, we adjust the children of the node as needed.
  // re-construct the term with the adjusted children.
  kind::Kind_t oldKind = originalNode.getKind();
  NodeBuilder builder(oldKind);
  if (originalNode.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << originalNode.getOperator();
  }
  for (size_t i = 0; i < originalNode.getNumChildren(); i++)
  {
    Node originalChild = originalNode[i];
    Node translatedChild = translated_children[i];
    Node adjustedChild = castToType(translatedChild, originalChild.getType());
    builder << adjustedChild;
  }
  Node reconstruction = builder.constructNode();
  // cast to tn in case the reconstruction is a bit-vector.
  reconstruction = castToType(reconstruction, resultType);
  return reconstruction;
}

BVToInt::BVToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-to-int"),
      d_binarizeCache(preprocContext->getUserContext()),
      d_eliminationCache(preprocContext->getUserContext()),
      d_rebuildCache(preprocContext->getUserContext()),
      d_bvToIntCache(preprocContext->getUserContext()),
      d_rangeAssertions(preprocContext->getUserContext())
{
  d_nm = NodeManager::currentNM();
  d_zero = d_nm->mkConst<Rational>(0);
  d_one = d_nm->mkConst<Rational>(1);
};

PreprocessingPassResult BVToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    Node bvNode = (*assertionsToPreprocess)[i];
    Node intNode = bvToInt(bvNode);
    Node rwNode = Rewriter::rewrite(intNode);
    Trace("bv-to-int-debug") << "bv node: " << bvNode << std::endl;
    Trace("bv-to-int-debug") << "int node: " << intNode << std::endl;
    Trace("bv-to-int-debug") << "rw node: " << rwNode << std::endl;
    assertionsToPreprocess->replace(i, rwNode);
  }
  addFinalizeRangeAssertions(assertionsToPreprocess);
  return PreprocessingPassResult::NO_CONFLICT;
}

void BVToInt::addFinalizeRangeAssertions(
    AssertionPipeline* assertionsToPreprocess)
{
  // collect the range assertions from d_rangeAssertions
  // (which is a context-dependent set)
  // into a vector.
  vector<Node> vec_range;
  vec_range.assign(d_rangeAssertions.key_begin(), d_rangeAssertions.key_end());
  // conjoin all range assertions and add the conjunction
  // as a new assertion
  Node rangeAssertions = Rewriter::rewrite(d_nm->mkAnd(vec_range));
  assertionsToPreprocess->push_back(rangeAssertions);
  Trace("bv-to-int-debug") << "range constraints: "
                           << rangeAssertions.toString() << std::endl;
}

Node BVToInt::createShiftNode(vector<Node> children,
                              uint64_t bvsize,
                              bool isLeftShift)
{
  /**
   * from SMT-LIB:
   * [[(bvshl s t)]] := nat2bv[m](bv2nat([[s]]) * 2^(bv2nat([[t]])))
   * [[(bvlshr s t)]] := nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
   * Since we don't have exponentiation, we use an ite.
   * Important note: below we use INTS_DIVISION_TOTAL, which is safe here
   * because we divide by 2^... which is never 0.
   */
  Node x = children[0];
  Node y = children[1];
  // shifting by const is eliminated by the theory rewriter
  Assert(!y.isConst());
  Node ite = d_zero;
  Node body;
  for (uint64_t i = 0; i < bvsize; i++)
  {
    if (isLeftShift)
    {
      body = d_nm->mkNode(kind::INTS_MODULUS_TOTAL,
                          d_nm->mkNode(kind::MULT, x, pow2(i)),
                          pow2(bvsize));
    }
    else
    {
      body = d_nm->mkNode(kind::INTS_DIVISION_TOTAL, x, pow2(i));
    }
    ite = d_nm->mkNode(kind::ITE,
                       d_nm->mkNode(kind::EQUAL, y, d_nm->mkConst<Rational>(i)),
                       body,
                       ite);
  }
  return ite;
}

Node BVToInt::translateQuantifiedFormula(Node quantifiedNode)
{
  kind::Kind_t k = quantifiedNode.getKind();
  Node boundVarList = quantifiedNode[0];
  Assert(boundVarList.getKind() == kind::BOUND_VAR_LIST);
  // Since bit-vector variables are being translated to
  // integer variables, we need to substitute the new ones
  // for the old ones.
  vector<Node> oldBoundVars;
  vector<Node> newBoundVars;
  vector<Node> rangeConstraints;
  for (Node bv : quantifiedNode[0])
  {
    oldBoundVars.push_back(bv);
    if (bv.getType().isBitVector())
    {
      // bit-vector variables are replaced by integer ones.
      // the new variables induce range constraints based on the
      // original bit-width.
      Node newBoundVar = d_bvToIntCache[bv];
      newBoundVars.push_back(newBoundVar);
      rangeConstraints.push_back(
          mkRangeConstraint(newBoundVar, bv.getType().getBitVectorSize()));
    }
    else
    {
      // variables that are not bit-vectors are not changed
      newBoundVars.push_back(bv);
    }
  }

  // the body of the quantifier
  Node matrix = d_bvToIntCache[quantifiedNode[1]];
  // make the substitution
  matrix = matrix.substitute(oldBoundVars.begin(),
                             oldBoundVars.end(),
                             newBoundVars.begin(),
                             newBoundVars.end());
  // A node to represent all the range constraints.
  Node ranges = d_nm->mkAnd(rangeConstraints);
  // Add the range constraints to the body of the quantifier.
  // For "exists", this is added conjunctively
  // For "forall", this is added to the left side of an implication.
  matrix = d_nm->mkNode(
      k == kind::FORALL ? kind::IMPLIES : kind::AND, ranges, matrix);
  // create the new quantified formula and return it.
  Node newBoundVarsList = d_nm->mkNode(kind::BOUND_VAR_LIST, newBoundVars);
  Node result = d_nm->mkNode(kind::FORALL, newBoundVarsList, matrix);
  return result;
}

Node BVToInt::createBVNotNode(Node n, uint64_t bvsize)
{
  return d_nm->mkNode(kind::MINUS, maxInt(bvsize), n);
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
