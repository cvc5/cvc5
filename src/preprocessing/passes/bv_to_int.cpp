/*********************                                                        */
/*! \file bv_to_int.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar, Ahmed Irfan
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BVToInt preprocessing pass
 **
 ** Converts bit-vector operations into integer operations.
 **
 **/

#include "preprocessing/passes/bv_to_int.h"

#include <cmath>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "options/uf_options.h"
#include "theory/bv/theory_bv_rewrite_rules_operator_elimination.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;
using namespace CVC4::theory::bv;

namespace {

Rational intpow2(uint64_t b)
{
  return Rational(Integer(2).pow(b), Integer(1));
}

/**
 * Helper functions for createBitwiseNode
 */
bool oneBitAnd(bool a, bool b) { return (a && b); }

bool oneBitOr(bool a, bool b) { return (a || b); }

bool oneBitXor(bool a, bool b) { return a != b; }

bool oneBitXnor(bool a, bool b) { return a == b; }

bool oneBitNand(bool a, bool b) { return !(a && b); }

bool oneBitNor(bool a, bool b) { return !(a || b); }

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
  vector<Node> toVisit;
  toVisit.push_back(n);
  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    uint64_t numChildren = current.getNumChildren();
    if (d_binarizeCache.find(current) == d_binarizeCache.end())
    {
      /**
       * We still haven't visited the sub-dag rooted at the current node.
       * In this case, we:
       * mark that we have visited this node by assigning a null node to it in
       * the cache, and add its children to toVisit.
       */
      d_binarizeCache[current] = Node();
      toVisit.insert(toVisit.end(), current.begin(), current.end());
    }
    else if (d_binarizeCache[current].isNull())
    {
      /*
       * We already visited the sub-dag rooted at the current node,
       * and binarized all its children.
       * Now we binarize the current node itself.
       */
      toVisit.pop_back();
      kind::Kind_t k = current.getKind();
      if ((numChildren > 2)
          && (k == kind::BITVECTOR_PLUS || k == kind::BITVECTOR_MULT
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
        NodeBuilder<> builder(k);
        if (current.getKind() == kind::BITVECTOR_EXTRACT
            || current.getKind() == kind::APPLY_UF)
        {
          builder << current.getOperator();
        }
        for (Node child : current)
        {
          builder << d_binarizeCache[child];
        }
        d_binarizeCache[current] = builder.constructNode();
      }
      else
      {
        // current has no children
        d_binarizeCache[current] = current;
      }
    }
    else
    {
      // We already binarized current and it is in the cache.
      toVisit.pop_back();
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
    toVisit.pop_back();
    bool inEliminationCache =
        (d_eliminationCache.find(current) != d_eliminationCache.end());
    bool inRebuildCache =
        (d_rebuildCache.find(current) != d_rebuildCache.end());
    if (!inEliminationCache)
    {
      // current hasn't been eliminated yet.
      // eliminate operators from it
      Node currentEliminated =
          FixpointRewriteStrategy<RewriteRule<UdivZero>,
                                  RewriteRule<SdivEliminate>,
                                  RewriteRule<SremEliminate>,
                                  RewriteRule<SmodEliminate>,
                                  RewriteRule<RepeatEliminate>,
                                  RewriteRule<ZeroExtendEliminate>,
                                  RewriteRule<SignExtendEliminate>,
                                  RewriteRule<RotateRightEliminate>,
                                  RewriteRule<RotateLeftEliminate>,
                                  RewriteRule<CompEliminate>,
                                  RewriteRule<SleEliminate>,
                                  RewriteRule<SltEliminate>,
                                  RewriteRule<SgtEliminate>,
                                  RewriteRule<SgeEliminate>,
                                  RewriteRule<ShlByConst>,
                                  RewriteRule<LshrByConst> >::apply(current);
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
      if (d_rebuildCache[current].isNull())
      {
        // current wasn't rebuilt yet.
        uint64_t numChildren = current.getNumChildren();
        if (numChildren == 0)
        {
          // We only eliminate operators that are not nullary.
          d_rebuildCache[current] = current;
        }
        else
        {
          // The main operator is replaced, and the children
          // are replaced with their eliminated counterparts.
          NodeBuilder<> builder(current.getKind());
          if (current.getKind() == kind::BITVECTOR_EXTRACT
              || current.getKind() == kind::APPLY_UF)
          {
            builder << current.getOperator();
          }
          for (Node child : current)
          {
            Assert(d_eliminationCache.find(child) != d_eliminationCache.end());
            Node eliminatedChild = d_eliminationCache[child];
            Assert(d_rebuildCache.find(eliminatedChild) != d_eliminationCache.end());
            Assert(!d_rebuildCache[eliminatedChild].isNull());
            builder << d_rebuildCache[eliminatedChild];
          }
          d_rebuildCache[current] = builder.constructNode();
        }
      }
    }
  }
  Assert(d_eliminationCache.find(n) != d_eliminationCache.end());
  Node eliminated = d_eliminationCache[n];
  Assert(d_rebuildCache.find(eliminated) != d_rebuildCache.end());
  Assert(!d_rebuildCache[eliminated].isNull());
  return d_rebuildCache[eliminated];
}

/**
 * Translate n to Integers via post-order traversal.
 */
Node BVToInt::bvToInt(Node n)
{
  n = eliminationPass(n);
  n = makeBinary(n);
  vector<Node> toVisit;
  toVisit.push_back(n);
  uint64_t granularity = options::solveBVAsInt();

  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    uint64_t currentNumChildren = current.getNumChildren();
    if (d_bvToIntCache.find(current) == d_bvToIntCache.end())
    {
      // This is the first time we visit this node and it is not in the cache.
      d_bvToIntCache[current] = Node();
      toVisit.insert(toVisit.end(), current.begin(), current.end());
    }
    else
    {
      // We already visited this node
      if (!d_bvToIntCache[current].isNull())
      {
        // We are done computing the translation for current
        toVisit.pop_back();
      }
      else
      {
        // We are now visiting current on the way back up.
        // This is when we do the actual translation.
        if (currentNumChildren == 0)
        {
          Assert(current.isVar() || current.isConst());
          if (current.isVar())
          {
            if (current.getType().isBitVector())
            {
              // For bit-vector variables, we create integer variables and add a
              // range constraint.
              Node newVar = d_nm->mkSkolem("__bvToInt_var",
                                           d_nm->integerType(),
                                           "Variable introduced in bvToInt "
                                           "pass instead of original variable "
                                               + current.toString());

              d_bvToIntCache[current] = newVar;
              d_rangeAssertions.insert(mkRangeConstraint(
                  newVar, current.getType().getBitVectorSize()));
            }
            else
            {
              // variables other than bit-vector variables are left intact
              d_bvToIntCache[current] = current;
            }
          }
          else
          {
            // current is a const
            if (current.getKind() == kind::CONST_BITVECTOR)
            {
              // Bit-vector constants are transformed into their integer value.
              BitVector constant(current.getConst<BitVector>());
              Integer c = constant.toInteger();
              d_bvToIntCache[current] = d_nm->mkConst<Rational>(c);
            }
            else
            {
              // Other constants stay the same.
              d_bvToIntCache[current] = current;
            }
          }
        }
        else
        {
          /**
           * The current node has children.
           * Since we are on the way back up,
           * these children were already translated.
           * We save their translation for future use.
           */
          vector<Node> translated_children;
          for (uint64_t i = 0; i < currentNumChildren; i++)
          {
            translated_children.push_back(d_bvToIntCache[current[i]]);
          }
          // The translation of the current node is determined by the kind of
          // the node.
          kind::Kind_t oldKind = current.getKind();
          //ultbv and sltbv were supposed to be eliminated before this point.
          Assert(oldKind != kind::BITVECTOR_ULTBV);
          Assert(oldKind != kind::BITVECTOR_SLTBV);
          switch (oldKind)
          {
            case kind::BITVECTOR_PLUS:
            {
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              /**
               * we avoid modular arithmetics by the addition of an
               * indicator variable sigma.
               * Tr(a+b) is Tr(a)+Tr(b)-(sigma*2^k),
               * with k being the bit width,
               * and sigma being either 0 or 1.
               */
              Node sigma = d_nm->mkSkolem(
                  "__bvToInt_sigma_var",
                  d_nm->integerType(),
                  "Variable introduced in bvToInt pass to avoid integer mod");
              Node plus = d_nm->mkNode(kind::PLUS, translated_children);
              Node multSig = d_nm->mkNode(kind::MULT, sigma, pow2(bvsize));
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::MINUS, plus, multSig);
              d_rangeAssertions.insert(d_nm->mkNode(kind::LEQ, d_zero, sigma));
              d_rangeAssertions.insert(d_nm->mkNode(kind::LEQ, sigma, d_one));
              d_rangeAssertions.insert(
                  mkRangeConstraint(d_bvToIntCache[current], bvsize));
              break;
            }
            case kind::BITVECTOR_MULT:
            {
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              /**
               * we use a similar trick to the one used for addition.
               * Tr(a*b) is Tr(a)*Tr(b)-(sigma*2^k),
               * with k being the bit width,
               * and sigma is between [0, 2^k - 1).
               */
              Node sigma = d_nm->mkSkolem(
                  "__bvToInt_sigma_var",
                  d_nm->integerType(),
                  "Variable introduced in bvToInt pass to avoid integer mod");
              Node mult = d_nm->mkNode(kind::MULT, translated_children);
              Node multSig = d_nm->mkNode(kind::MULT, sigma, pow2(bvsize));
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::MINUS, mult, multSig);
              d_rangeAssertions.insert(
                  mkRangeConstraint(d_bvToIntCache[current], bvsize));
              if (translated_children[0].isConst()
                  || translated_children[1].isConst())
              {
                /*
                 * based on equation (23), section 3.2.3 of:
                 * Bozzano et al.
                 * Encoding RTL Constructs for MathSAT: a Preliminary Report.
                 */
                // this is an optimization when one of the children is constant
                Node c = translated_children[0].isConst()
                             ? translated_children[0]
                             : translated_children[1];
                d_rangeAssertions.insert(
                    d_nm->mkNode(kind::LEQ, d_zero, sigma));
                // the value of sigma is bounded by (c - 1)
                // where c is the constant multiplicand
                d_rangeAssertions.insert(d_nm->mkNode(kind::LT, sigma, c));
              }
              else
              {
                d_rangeAssertions.insert(mkRangeConstraint(sigma, bvsize));
              }
              break;
            }
            case kind::BITVECTOR_UDIV_TOTAL:
            {
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              // we use an ITE for the case where the second operand is 0.
              Node pow2BvSize = pow2(bvsize);
              Node divNode =
                  d_nm->mkNode(kind::INTS_DIVISION_TOTAL, translated_children);
              Node ite = d_nm->mkNode(
                  kind::ITE,
                  d_nm->mkNode(kind::EQUAL, translated_children[1], d_zero),
                  d_nm->mkNode(kind::MINUS, pow2BvSize, d_one),
                  divNode);
              d_bvToIntCache[current] = ite;
              break;
            }
            case kind::BITVECTOR_UREM_TOTAL:
            {
              // we use an ITE for the case where the second operand is 0.
              Node modNode =
                  d_nm->mkNode(kind::INTS_MODULUS_TOTAL, translated_children);
              Node ite = d_nm->mkNode(
                  kind::ITE,
                  d_nm->mkNode(kind::EQUAL, translated_children[1], d_zero),
                  translated_children[0],
                  modNode);
              d_bvToIntCache[current] = ite;
              break;
            }
            case kind::BITVECTOR_NEG:
            {
              // (bvneg x) is 2^k-x, unless x is 0, 
              // in which case the result should be 0.
              // This can be expressed by (2^k-x) mod 2^k
              // However, since mod is an expensive arithmetic operation,
              // we represent `bvneg` using an ITE.
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              Node neg =
                  d_nm->mkNode(kind::MINUS, pow2BvSize, translated_children[0]);
              Node isZero =
                  d_nm->mkNode(kind::EQUAL, translated_children[0], d_zero);
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::ITE, isZero, d_zero, neg);
              break;
            }
            case kind::BITVECTOR_NOT:
            {
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              // we use a specified function to generate the node.
              d_bvToIntCache[current] =
                  createBVNotNode(translated_children[0], bvsize);
              break;
            }
            case kind::BITVECTOR_TO_NAT:
            {
              // In this case, we already translated the child to integer.
              // So the result is the translated child.
              d_bvToIntCache[current] = translated_children[0];
              break;
            }
            case kind::BITVECTOR_AND:
            {
              // Construct an ite, based on granularity.
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              Assert(translated_children.size() == 2);
              Node newNode = createBitwiseNode(translated_children[0],
                                               translated_children[1],
                                               bvsize,
                                               granularity,
                                               &oneBitAnd);
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_OR:
            {
              // Construct an ite, based on granularity.
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              Node newNode = createBitwiseNode(translated_children[0],
                                               translated_children[1],
                                               bvsize,
                                               granularity,
                                               &oneBitOr);
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_XOR:
            {
              // Construct an ite, based on granularity.
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              Node newNode = createBitwiseNode(translated_children[0],
                                               translated_children[1],
                                               bvsize,
                                               granularity,
                                               &oneBitXor);
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_XNOR:
            {
              // Construct an ite, based on granularity.
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              Node newNode = createBitwiseNode(translated_children[0],
                                               translated_children[1],
                                               bvsize,
                                               granularity,
                                               &oneBitXnor);
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_NAND:
            {
              // Construct an ite, based on granularity.
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              Node newNode = createBitwiseNode(translated_children[0],
                                               translated_children[1],
                                               bvsize,
                                               granularity,
                                               &oneBitNand);
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_NOR:
            {
              // Construct an ite, based on granularity.
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              Node newNode = createBitwiseNode(translated_children[0],
                                               translated_children[1],
                                               bvsize,
                                               granularity,
                                               &oneBitNor);
              d_bvToIntCache[current] = newNode;
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
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              Node newNode = createShiftNode(translated_children, bvsize, true);
              d_bvToIntCache[current] = newNode;
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
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              Node newNode = createShiftNode(translated_children, bvsize, false);
              d_bvToIntCache[current] = newNode;
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
              uint64_t bvsize = current[0].getType().getBitVectorSize();
              // signed_min is 100000...
              Node signed_min = pow2(bvsize - 1);
              Node condition =
                  d_nm->mkNode(kind::LT, translated_children[0], signed_min);
              Node thenNode = createShiftNode(translated_children, bvsize, false);
              vector<Node> children = {
                  createBVNotNode(translated_children[0], bvsize),
                  translated_children[1]};
              Node elseNode = createBVNotNode(
                  createShiftNode(children, bvsize, false), bvsize);
              Node ite = d_nm->mkNode(kind::ITE, condition, thenNode, elseNode);
              d_bvToIntCache[current] = ite;
              break;
            }
            case kind::BITVECTOR_ITE:
            {
              // Lifted to a boolean ite.
              Node cond = d_nm->mkNode(kind::EQUAL, translated_children[0], d_one);
              Node ite = d_nm->mkNode(
                  kind::ITE, cond, translated_children[1], translated_children[2]);
              d_bvToIntCache[current] = ite;
              break;
            }
            case kind::BITVECTOR_CONCAT:
            {
              // (concat a b) translates to a*2^k+b, k being the bitwidth of b.
              uint64_t bvsizeRight = current[1].getType().getBitVectorSize();
              Node pow2BvSizeRight = pow2(bvsizeRight);
              Node a = d_nm->mkNode(
                  kind::MULT, translated_children[0], pow2BvSizeRight);
              Node b = translated_children[1];
              Node sum = d_nm->mkNode(kind::PLUS, a, b);
              d_bvToIntCache[current] = sum;
              break;
            }
            case kind::BITVECTOR_EXTRACT:
            {
              // ((_ extract i j) a) is a / 2^j mod 2^{i-j+1}
              // current = a[i:j]
              Node a = current[0];
              uint64_t i = bv::utils::getExtractHigh(current);
              uint64_t j = bv::utils::getExtractLow(current);
              Assert(d_bvToIntCache.find(a) != d_bvToIntCache.end());
              Assert(i >= j);
              Node div = d_nm->mkNode(
                  kind::INTS_DIVISION_TOTAL, d_bvToIntCache[a], pow2(j));
              d_bvToIntCache[current] = modpow2(div, i - j + 1);
              break;
            }
            case kind::EQUAL:
            {
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::EQUAL, translated_children);
              break;
            }
            case kind::BITVECTOR_ULT:
            {
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::LT, translated_children);
              break;
            }
            case kind::BITVECTOR_ULE:
            {
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::LEQ, translated_children);
              break;
            }
            case kind::BITVECTOR_UGT:
            {
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::GT, translated_children);
              break;
            }
            case kind::BITVECTOR_UGE:
            {
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::GEQ, translated_children);
              break;
            }
            case kind::LT:
            {
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::LT, translated_children);
              break;
            }
            case kind::LEQ:
            {
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::LEQ, translated_children);
              break;
            }
            case kind::GT:
            {
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::GT, translated_children);
              break;
            }
            case kind::GEQ:
            {
              d_bvToIntCache[current] =
                  d_nm->mkNode(kind::GEQ, translated_children);
              break;
            }
            case kind::ITE:
            {
              d_bvToIntCache[current] = d_nm->mkNode(oldKind, translated_children);
              break;
            }
            case kind::APPLY_UF:
            {
              /*
               * We replace all BV-sorts of the domain with INT
               * If the range is a BV sort, we replace it with INT
               * We cache both the term itself (e.g., f(a)) and the function
               * symbol f.
               */

              //Construct the function itself
              Node bvUF = current.getOperator();
              Node intUF;
              TypeNode tn = current.getOperator().getType();
              TypeNode bvRange = tn.getRangeType();
              if (d_bvToIntCache.find(bvUF) != d_bvToIntCache.end())
              {
                intUF = d_bvToIntCache[bvUF];
              }
              else
              {
                vector<TypeNode> bvDomain = tn.getArgTypes();
                vector<TypeNode> intDomain;
                /**
                 * if the original range is a bit-vector sort,
                 * the new range should be an integer sort.
                 * Otherwise, we keep the original range.
                 */
                TypeNode intRange =
                    bvRange.isBitVector() ? d_nm->integerType() : bvRange;
                for (TypeNode d : bvDomain)
                {
                  intDomain.push_back(d.isBitVector() ? d_nm->integerType()
                                                      : d);
                }
                ostringstream os;
                os << "__bvToInt_fun_" << bvUF << "_int";
                intUF =
                    d_nm->mkSkolem(os.str(),
                                   d_nm->mkFunctionType(intDomain, intRange),
                                   "bv2int function");
                // Insert the function symbol itself to the cache
                d_bvToIntCache[bvUF] = intUF;
              }
              if (childrenTypesChanged(current) && options::ufHo()) {
              /**
               * higher order logic allows comparing between functions
               * The current translation does not support this,
               * as the translated functions may be different outside
               * of the bounds that were relevant for the original
               * bit-vectors.
               */
                  throw TypeCheckingException(
                      current.toExpr(),
                      string("Cannot translate to Int: ") + current.toString());
              }
              else {
                translated_children.insert(translated_children.begin(), intUF);
                // Insert the term to the cache
                d_bvToIntCache[current] =
                    d_nm->mkNode(kind::APPLY_UF, translated_children);
                /**
                 * Add range constraints if necessary.
                 * If the original range was a BV sort, the current application of
                 * the function Must be within the range determined by the
                 * bitwidth.
                 */
                if (bvRange.isBitVector())
                {
                  d_rangeAssertions.insert(
                      mkRangeConstraint(d_bvToIntCache[current],
                                        current.getType().getBitVectorSize()));
                }
              }
                break;
            }
            default:
            {
              if (childrenTypesChanged(current)) {
                /**
                 * This is "failing on demand":
                 * We throw an exception if we encounter a case
                 * that we do not know how to translate,
                 * only if we actually need to construct a new
                 * node for such a case.
                 */
                  throw TypeCheckingException(
                      current.toExpr(),
                      string("Cannot translate to Int: ") + current.toString());
              }
              else {
                d_bvToIntCache[current] =
                    d_nm->mkNode(oldKind, translated_children);
              }
              break;
            }
          }
        }
        toVisit.pop_back();
      }
    }
  }
  return d_bvToIntCache[n];
}

bool BVToInt::childrenTypesChanged(Node n) {
  bool result = false;
  for (Node child : n) {
    TypeNode originalType = child.getType();
    TypeNode newType = d_bvToIntCache[child].getType();
    if (! newType.isSubtypeOf(originalType)) {
      result = true;
      break;
    }
  }
  return result;
}

BVToInt::BVToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-to-int"),
      d_binarizeCache(),
      d_eliminationCache(),
      d_bvToIntCache(),
      d_rangeAssertions()
{
  d_nm = NodeManager::currentNM();
  d_zero = d_nm->mkConst<Rational>(0);
  d_one = d_nm->mkConst<Rational>(1);
};

PreprocessingPassResult BVToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  AlwaysAssert(!options::incrementalSolving());
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
  vector<Node> vec_range;
  vec_range.assign(d_rangeAssertions.begin(), d_rangeAssertions.end());
  if (vec_range.size() == 1)
  {
    assertionsToPreprocess->push_back(vec_range[0]);
    Trace("bv-to-int-debug")
        << "range constraints: " << vec_range[0].toString() << std::endl;
  }
  else if (vec_range.size() >= 2)
  {
    Node rangeAssertions =
        Rewriter::rewrite(d_nm->mkNode(kind::AND, vec_range));
    assertionsToPreprocess->push_back(rangeAssertions);
    Trace("bv-to-int-debug")
        << "range constraints: " << rangeAssertions.toString() << std::endl;
  }
}

Node BVToInt::createShiftNode(vector<Node> children,
                              uint64_t bvsize,
                              bool isLeftShift)
{
  Node x = children[0];
  Node y = children[1];
  Assert(!y.isConst());
  // ite represents 2^x for every integer x from 0 to bvsize-1.
  Node ite = pow2(0);
  for (uint64_t i = 1; i < bvsize; i++)
  {
    ite = d_nm->mkNode(kind::ITE,
                       d_nm->mkNode(kind::EQUAL, y, d_nm->mkConst<Rational>(i)),
                       pow2(i),
                       ite);
  }
  /**
   * from SMT-LIB:
   * [[(bvshl s t)]] := nat2bv[m](bv2nat([[s]]) * 2^(bv2nat([[t]])))
   * [[(bvlshr s t)]] := nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
   * Since we don't have exponentiation, we use the ite declared above.
   */
  kind::Kind_t then_kind = isLeftShift ? kind::MULT : kind::INTS_DIVISION_TOTAL;
  return d_nm->mkNode(kind::ITE,
                              d_nm->mkNode(kind::LT, y, d_nm->mkConst<Rational>(bvsize)),
                              d_nm->mkNode(kind::INTS_MODULUS_TOTAL,
                                                            d_nm->mkNode(then_kind, x, ite),
                                                            pow2(bvsize)),
                              d_zero);
}

Node BVToInt::createITEFromTable(
    Node x,
    Node y,
    uint64_t granularity,
    std::map<std::pair<uint64_t, uint64_t>, uint64_t> table)
{
  Assert(granularity <= 8);
  uint64_t max_value = ((uint64_t)pow(2, granularity));
  // The table represents a function from pairs of integers to integers, where
  // all integers are between 0 (inclusive) and max_value (exclusive).
  Assert(table.size() == max_value * max_value);
  Node ite = d_nm->mkConst<Rational>(table[std::make_pair(0, 0)]);
  for (uint64_t i = 0; i < max_value; i++)
  {
    for (uint64_t j = 0; j < max_value; j++)
    {
      if ((i == 0) && (j == 0))
      {
        continue;
      }
      ite = d_nm->mkNode(
          kind::ITE,
          d_nm->mkNode(
              kind::AND,
              d_nm->mkNode(kind::EQUAL, x, d_nm->mkConst<Rational>(i)),
              d_nm->mkNode(kind::EQUAL, y, d_nm->mkConst<Rational>(j))),
          d_nm->mkConst<Rational>(table[std::make_pair(i, j)]),
          ite);
    }
  }
  return ite;
}

Node BVToInt::createBitwiseNode(Node x,
                                Node y,
                                uint64_t bvsize,
                                uint64_t granularity,
                                bool (*f)(bool, bool))
{
  /**
   * Standardize granularity.
   * If it is greater than bvsize, it is set to bvsize.
   * Otherwise, it is set to the closest (going down)  divider of bvsize.
   */
  Assert(granularity > 0);
  if (granularity > bvsize)
  {
    granularity = bvsize;
  }
  else
  {
    while (bvsize % granularity != 0)
    {
      granularity = granularity - 1;
    }
  }
  // transform f into a table
  // f is defined over 1 bit, while the table is defined over `granularity` bits
  std::map<std::pair<uint64_t, uint64_t>, uint64_t> table;
  uint64_t max_value = ((uint64_t)pow(2, granularity));
  for (uint64_t i = 0; i < max_value; i++)
  {
    for (uint64_t j = 0; j < max_value; j++)
    {
      uint64_t sum = 0;
      for (uint64_t n = 0; n < granularity; n++)
      {
        // b is the result of f on the current bit
        bool b = f((((i >> n) & 1) == 1), (((j >> n) & 1) == 1));
        // add the corresponding power of 2 only if the result is 1
        if (b)
        {
          sum += 1 << n;
        }
      }
      table[std::make_pair(i, j)] = sum;
    }
  }
   Assert(table.size() == max_value * max_value);

  /*
   * Create the sum.
   * For granularity 1, the sum has bvsize elements.
   * In contrast, if bvsize = granularity, sum has one element.
   * Each element in the sum is an ite that corresponds to the generated table,
   * multiplied by the appropriate power of two.
   * More details are in bv_to_int.h .
   */
  uint64_t sumSize = bvsize / granularity;
  Node sumNode = d_zero;
  /**
   * extract definition in integers is:
   * (define-fun intextract ((k Int) (i Int) (j Int) (a Int)) Int
   * (mod (div a (two_to_the j)) (two_to_the (+ (- i j) 1))))
   */
  for (uint64_t i = 0; i < sumSize; i++)
  {
    Node xExtract = d_nm->mkNode(
        kind::INTS_MODULUS_TOTAL,
        d_nm->mkNode(kind::INTS_DIVISION_TOTAL, x, pow2(i * granularity)),
        pow2(granularity));
    Node yExtract = d_nm->mkNode(
        kind::INTS_MODULUS_TOTAL,
        d_nm->mkNode(kind::INTS_DIVISION_TOTAL, y, pow2(i * granularity)),
        pow2(granularity));
    Node ite = createITEFromTable(xExtract, yExtract, granularity, table);
    sumNode =
        d_nm->mkNode(kind::PLUS,
                     sumNode,
                     d_nm->mkNode(kind::MULT, pow2(i * granularity), ite));
  }
  return sumNode;
}

Node BVToInt::createBVNotNode(Node n, uint64_t bvsize)
{
  return d_nm->mkNode(kind::MINUS, maxInt(bvsize), n);
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
