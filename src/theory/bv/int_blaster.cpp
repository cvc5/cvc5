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
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/iand.h"
#include "util/rational.h"

namespace cvc5 {
using namespace cvc5::theory;
namespace {

// A helper function to compute 2^b as a Rational
Rational intpow2(uint64_t b) { return Rational(Integer(2).pow(b), Integer(1)); }

}  // namespace

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
  // The translation of the original node is determined by the kind of
  // the node.
  kind::Kind_t oldKind = original.getKind();
  // signed comparisons were supposed to be eliminated by this point.
  Assert(oldKind != kind::BITVECTOR_SDIV);
  Assert(oldKind != kind::BITVECTOR_SREM);
  Assert(oldKind != kind::BITVECTOR_SMOD);
  Assert(oldKind != kind::BITVECTOR_XNOR);
  Assert(oldKind != kind::BITVECTOR_NAND);
  Assert(oldKind != kind::BITVECTOR_SUB);
  Assert(oldKind != kind::BITVECTOR_REPEAT);
  Assert(oldKind != kind::BITVECTOR_ROTATE_RIGHT);
  Assert(oldKind != kind::BITVECTOR_ROTATE_LEFT);
  Assert(oldKind != kind::BITVECTOR_COMP);
  Assert(oldKind != kind::BITVECTOR_SGT);
  Assert(oldKind != kind::BITVECTOR_SLE);
  Assert(oldKind != kind::BITVECTOR_SGE);
  Assert(oldKind != kind::EXISTS);
  Assert(oldKind != kind::BITVECTOR_UDIV || !(original[1].isConst() && original[1].getConst<BitVector>().getValue().isZero()));
  // The following variable will only be used in assertions.
  CVC5_UNUSED uint64_t originalNumChildren = original.getNumChildren();
  Node returnNode;
  switch (oldKind)
  {
    case kind::BITVECTOR_ADD:
    {
      Assert(originalNumChildren == 2);
  uint64_t bvsize = original[0].getType().getBitVectorSize();
      returnNode = createBVAddNode(translated_children[0], translated_children[1], bvsize);
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
      // we use an ITE for the case where the second operand is 0.
  uint64_t bvsize = original[0].getType().getBitVectorSize();
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
      // we use a specified function to generate the node.
  uint64_t bvsize = original[0].getType().getBitVectorSize();
      returnNode = createBVNotNode(translated_children[0], bvsize);
      break;
    }
    case kind::BITVECTOR_NEG:
    {
  uint64_t bvsize = original[0].getType().getBitVectorSize();
      returnNode = createBVNegNode(translated_children[0], bvsize);
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
      // In this case we take the original integer,
      // modulo 2 to the power of the bit-width
      returnNode =
          modpow2(translated_children[0],
                  original.getOperator().getConst<IntToBitVector>().d_size);
      break;
    }
    case kind::BITVECTOR_OR:
    {
      Assert(translated_children.size() == 2);
  uint64_t bvsize = original[0].getType().getBitVectorSize();
      returnNode = createBVOrNode(translated_children[0], translated_children[1], bvsize, lemmas);
      break;
    }
    case kind::BITVECTOR_XOR:
    {
      Assert(translated_children.size() == 2);
  uint64_t bvsize = original[0].getType().getBitVectorSize();
      // Based on Hacker's Delight section 2-2 equation n:
      // x xor y = x|y - x&y
      Node bvor = createBVOrNode(translated_children[0], translated_children[1], bvsize, lemmas);
      Node bvand = createBVAndNode(translated_children[0], translated_children[1], bvsize, lemmas);
      returnNode = createBVSubNode(bvor, bvand, bvsize);
      break;
    }
    case kind::BITVECTOR_AND:
    {
      Assert(translated_children.size() == 2);
  uint64_t bvsize = original[0].getType().getBitVectorSize();
      returnNode = createBVAndNode(translated_children[0], translated_children[1], bvsize, lemmas);
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
      // signed_min is 100000...
  uint64_t bvsize = original[0].getType().getBitVectorSize();
      Node signed_min = pow2(bvsize - 1);
      Node condition =
          d_nm->mkNode(kind::LT, translated_children[0], signed_min);
      Node thenNode = createShiftNode(translated_children, bvsize, false);
      std::vector<Node> children = {
          createBVNotNode(translated_children[0], bvsize),
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
    case kind::BITVECTOR_SLT:
    {
  uint64_t bvsize = original[0].getType().getBitVectorSize();
      Trace("int-blaster-debug") << "first arg: " << original[0] << std::endl;
      Trace("int-blaster-debug") << "translated first arg: " << translated_children[0] << std::endl;
      Trace("int-blaster-debug") << "second arg: " << original[1] << std::endl;
      Trace("int-blaster-debug") << "translated second arg: " << translated_children[1] << std::endl;
      Trace("int-blaster-debug") << "first uts: " << uts(translated_children[0], bvsize) << std::endl;
      Trace("int-blaster-debug") << "second uts: " << uts(translated_children[1], bvsize) << std::endl;
      returnNode = d_nm->mkNode(kind::LT, uts(translated_children[0], bvsize), uts(translated_children[1], bvsize));
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
    case kind::BITVECTOR_ULTBV:
    {
      returnNode = d_nm->mkNode(kind::ITE,
                                d_nm->mkNode(kind::LT, translated_children),
                                d_one,
                                d_zero);
      break;
    }
    case kind::BITVECTOR_SLTBV:
    {
  uint64_t bvsize = original[0].getType().getBitVectorSize();
      returnNode = d_nm->mkNode(
          kind::ITE,
          d_nm->mkNode(kind::LT,
                       uts(translated_children[0], bvsize),
                       uts(translated_children[1], bvsize)),
          d_one,
          d_zero);
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
        throw OptionException("bv-to-int does not support higher order logic ");
      }
      // Insert the translated application term to the cache
      returnNode = d_nm->mkNode(kind::APPLY_UF, translated_children);
      // Add range constraints if necessary.
      // If the original range was a BV sort, the original application of
      // the function Must be within the range determined by the
      // bitwidth.
      if (original.getType().isBitVector())
      {
        addRangeConstraint(
            returnNode, original.getType().getBitVectorSize(), lemmas);
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
      // first, verify that we haven't missed
      // any bv operator
      Assert(theory::kindToTheoryId(oldKind) != THEORY_BV);

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
  Trace("int-blaster-debug") << "original: " << original << std::endl;
  Trace("int-blaster-debug") << "returnNode: " << returnNode << std::endl;
  return returnNode;
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

Node IntBlaster::createBVAndNode(Node x, Node y, uint64_t bvsize, std::vector<Node>& lemmas) {
      return Node();
}

Node IntBlaster::createBVOrNode(Node x, Node y, uint64_t bvsize, std::vector<Node>& lemmas) {
      // Based on Hacker's Delight section 2-2 equation h:
      // x+y = x|y + x&y
      // from which we deduce:
      // x|y = x+y - x&y
      Node plus = createBVAddNode(x, y, bvsize);
      Node bvand = createBVAndNode(x, y, bvsize, lemmas);
      return createBVSubNode(plus, bvand, bvsize);
}

Node IntBlaster::createBVSubNode(Node x, Node y, uint64_t bvsize) {
      Node minus = d_nm->mkNode(kind::MINUS, x, y);
      Node p2 = pow2(bvsize);
      return d_nm->mkNode(kind::INTS_MODULUS_TOTAL, minus, p2);
}

Node IntBlaster::createBVAddNode(Node x, Node y, uint64_t bvsize) {
      Node plus = d_nm->mkNode(kind::PLUS, x, y);
      Node p2 = pow2(bvsize);
      return d_nm->mkNode(kind::INTS_MODULUS_TOTAL, plus, p2);

}

Node IntBlaster::createBVNegNode(Node n, uint64_t bvsize) {
      // Based on Hacker's Delight section 2-2 equation a:
      // -x = ~x+1
      Node p2 = pow2(bvsize);
      return d_nm->mkNode(kind::MINUS, p2, n);
}

Node IntBlaster::createBVNotNode(Node n, uint64_t bvsize)
{
  return d_nm->mkNode(kind::MINUS, maxInt(bvsize), n);
}

}  // namespace cvc5
