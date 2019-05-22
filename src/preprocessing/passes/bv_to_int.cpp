/*********************                                                        */
/*! \file bv_to_int.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BVToInt preprocessing pass
 **
 ** Converts integer operations into bitvector operations. The width of the
 ** bitvectors is controlled through the `--solve-int-as-bv` command line
 ** option.
 **/

#include "preprocessing/passes/bv_to_int.h"

#include <string>
#include <unordered_map>
#include <vector>
#include <math.h>

#include "expr/node.h"
#include "theory/rewriter.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;
using namespace CVC4::theory::bv;


void printCache(NodeMap m) {
      for (auto const& pair: m) {
        std::cout << "{" << pair.first.toString() << ": "  << pair.second.toString() << "}\n";
    }
}

Node BVToInt::mkRangeConstraint(Node newVar, size_t k) {
  Node lower = d_nm->mkNode(kind::LEQ, d_nm->mkConst<Rational>(0), newVar);
  Node upper = d_nm->mkNode(kind::LT, newVar, pow2(k));
  Node result = d_nm->mkNode(kind::AND, lower, upper);
  return result;
}

Node BVToInt::pow2(Node n) {
	  Node two_const = d_nm->mkConst<Rational>(2);
    Node result = d_nm->mkNode(kind::POW, two_const, n);
    return result;
}

Node BVToInt::pow2(size_t k)
{
	  Node twoConst = d_nm->mkConst<Rational>(2);
	  Node k_const = d_nm->mkConst<Rational>(k);
	  Node result = d_nm->mkNode(kind::POW, twoConst, k_const);
	  return result;
}

Node BVToInt::makeBinary(Node n)
{
  vector<Node> toVisit;
  toVisit.push_back(n);
  while (!toVisit.empty())
  {
    // The current node we are processing
    Node current = toVisit.back();
    size_t numChildren = current.getNumChildren();
    if (d_binarizeCache.find(current) == d_binarizeCache.end()) {
      d_binarizeCache[current] = Node();
      for (size_t i=0; i<numChildren; i++) 
      {
	      toVisit.push_back(current[i]);
      }
    }
    else if (d_binarizeCache[current].isNull())
    {
      toVisit.pop_back();
      kind::Kind_t k = current.getKind();
      if ((numChildren > 2)  && (k == kind::BITVECTOR_PLUS ||
            k == kind::BITVECTOR_MULT ||
            k == kind::BITVECTOR_AND ||
            k == kind::BITVECTOR_OR ||
            k == kind::BITVECTOR_XOR)) {
        Assert(d_binarizeCache.find(current[0]) != d_binarizeCache.end());
        Node result = d_binarizeCache[current[0]];
        for (unsigned i = 1; i < numChildren; i++)
        {
          Assert(d_binarizeCache.find(current[i]) != d_binarizeCache.end());
          Node child = d_binarizeCache[current[i]];
          result = d_nm->mkNode(current.getKind(), result, child);
        }
        d_binarizeCache[current] = result;
      } else if (numChildren > 0) {
          vector<Node> binarized_children;
          if (current.getKind() == kind::BITVECTOR_EXTRACT) { 
            binarized_children.push_back(current.getOperator());
          }
          for (uint i = 0; i < numChildren; i++) {
            binarized_children.push_back(d_binarizeCache[current[i]]);
          }
          d_binarizeCache[current] = d_nm->mkNode(k, binarized_children);
      } else {
          d_binarizeCache[current] = current;
      }
    }
    else
    {
      toVisit.pop_back();
      continue;
    }
  }
  return d_binarizeCache[n];
}

//eliminate many bit-vector operators before the translation to integers.
Node BVToInt::eliminationPass(Node n) {
  std::vector<Node> toVisit;
  toVisit.push_back(n);
  Node current;
  Node currentEliminated;
  while (!toVisit.empty()) {
    current = toVisit.back();
    toVisit.pop_back();
    if (current.isNull()) {
      currentEliminated = toVisit.back();
      toVisit.pop_back();
      current = toVisit.back();
      toVisit.pop_back();
      size_t numChildren = currentEliminated.getNumChildren();
      if (numChildren == 0) {
        d_eliminationCache[current] = currentEliminated;
      } else {
        vector<Node> children;
        if (currentEliminated.getKind() == kind::BITVECTOR_EXTRACT || currentEliminated.getKind() == kind::APPLY_UF) {
          children.push_back(currentEliminated.getOperator());
        }
        for (size_t i=0; i<numChildren; i++) {
          Assert(d_eliminationCache.find(currentEliminated[i]) != d_eliminationCache.end());
          children.push_back(d_eliminationCache[currentEliminated[i]]);
        }
        d_eliminationCache[current] = d_nm->mkNode(currentEliminated.getKind(), children); 
      }
    } else {
        if (d_eliminationCache.find(current) != d_eliminationCache.end()) {
          continue;
        } else {
            currentEliminated = FixpointRewriteStrategy<
               RewriteRule<AshrEliminate>,
               RewriteRule<UdivZero>,
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
            	 RewriteRule<SgeEliminate>
	            >::apply(current);
            toVisit.push_back(current);
            toVisit.push_back(currentEliminated);
            toVisit.push_back(Node());
            size_t numChildren = currentEliminated.getNumChildren();
            for (size_t i = 0; i < numChildren; i++) {
              toVisit.push_back(currentEliminated[i]);
            }
        }
    }
  }
  return d_eliminationCache[n];
}

Node BVToInt::bvToInt(Node n)
{
  n = makeBinary(n);
  n = eliminationPass(n);
  vector<Node> toVisit;
  toVisit.push_back(n);
  Node one_const = d_nm->mkConst<Rational>(1);

  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    size_t currentNumChildren = current.getNumChildren();
    if (d_bvToIntCache.find(current) == d_bvToIntCache.end()) {
      d_bvToIntCache[current] = Node();
      for (size_t i=0; i < currentNumChildren; i++) {
	      toVisit.push_back(current[i]);
      }
    } else {
      if (!d_bvToIntCache[current].isNull()) {
	      toVisit.pop_back();
      } else {
        kind::Kind_t oldKind = current.getKind();
        if (currentNumChildren == 0) {
          if (current.isVar())
          {
            if (current.getType().isBitVector())
            {
              Node newVar = d_nm->mkSkolem("__bvToInt_var",
                                    d_nm->integerType(),
                                    "Variable introduced in bvToInt pass instead of original variable " + current.toString());

              d_bvToIntCache[current] = newVar;
              d_rangeAssertions.push_back(mkRangeConstraint(newVar, current.getType().getBitVectorSize()));
            }
            else
            {
              AlwaysAssert(current.getType() == d_nm->booleanType());
	      d_bvToIntCache[current] = current;
            }
          }
          else if (current.isConst())
          {
            switch (current.getKind())
            {
              case kind::CONST_RATIONAL:
              {
                d_bvToIntCache[current] = current;
                break;
              }
              case kind::CONST_BITVECTOR:
              {
                BitVector constant(current.getConst<BitVector>());
	        Integer c = constant.toInteger();
                d_bvToIntCache[current] = d_nm->mkConst<Rational>(c);
                break;
              }
              case kind::CONST_BOOLEAN: 
	      {
                d_bvToIntCache[current] = current;
	        break;
	      }
              default:
                throw TypeCheckingException(
                    current.toExpr(),
                    string("Cannot translate const: ")
                        + current.toString());
            }
          }
          else
          {
            throw TypeCheckingException(
                current.toExpr(),
                string("Cannot translate: ") + current.toString());
          }
	  
	} else {
	  vector<Node> intized_children;
	  for (size_t i=0; i<currentNumChildren; i++) {
	    intized_children.push_back(d_bvToIntCache[current[i]]);
	  }
	  switch (oldKind)
          {
            case kind::BITVECTOR_PLUS: 
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              Node plus = d_nm->mkNode(kind::PLUS, intized_children);
              vector<Node> children = {plus, pow2BvSize};
              Node mod = d_nm->mkNode(kind::INTS_MODULUS_TOTAL, children);
              d_bvToIntCache[current] = mod;
              break;
            }
            case kind::BITVECTOR_MULT: 
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              Node mul = d_nm->mkNode(kind::MULT, intized_children);
              vector<Node> children = {mul, pow2BvSize};
              d_bvToIntCache[current] = d_nm->mkNode(kind::INTS_MODULUS_TOTAL, children);
              break;
            }
            case kind::BITVECTOR_SUB:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              Node sub = d_nm->mkNode(kind::MINUS, intized_children);
              vector<Node> children = {sub, pow2BvSize};
              d_bvToIntCache[current] = d_nm->mkNode(kind::INTS_MODULUS_TOTAL, children);
              break;
            }
            case kind::BITVECTOR_UDIV:
            {
              cout << "panda this should have been eliminated" << std::endl;
              Assert(false);
              break;
            }
            case kind::BITVECTOR_UREM:
            {
              cout << "panda this should have been eliminated" << std::endl;
              Assert(false);
              break;
            }
            case kind::BITVECTOR_UDIV_TOTAL:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              Node divNode = d_nm->mkNode(kind::INTS_DIVISION_TOTAL, intized_children);
              Node ite = d_nm->mkNode(kind::ITE,d_nm->mkNode(kind::EQUAL, intized_children[1],d_nm->mkConst<Rational>(0)),d_nm->mkNode(kind::MINUS, pow2BvSize,d_nm->mkConst<Rational>(1)),d_nm->mkNode(kind::INTS_MODULUS_TOTAL, divNode, pow2BvSize));
              d_bvToIntCache[current] = ite;
              break;
            }
            case kind::BITVECTOR_UREM_TOTAL:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              Node modNode = d_nm->mkNode(kind::INTS_MODULUS_TOTAL, intized_children);
              Node ite = d_nm->mkNode(kind::ITE,d_nm->mkNode(kind::EQUAL, intized_children[1],d_nm->mkConst<Rational>(0)), intized_children[0],d_nm->mkNode(kind::INTS_MODULUS_TOTAL, modNode, pow2BvSize));
              d_bvToIntCache[current] = ite;
              break;
            }
            case kind::BITVECTOR_NEG: 
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              vector<Node> children = {pow2BvSize, intized_children[0]};
              d_bvToIntCache[current] = d_nm->mkNode(kind::MINUS, children);
              break;
            }  
            case kind::BITVECTOR_NOT: 
            {
       	      uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              vector<Node> children = {pow2BvSize, one_const};
              Node max = d_nm->mkNode(kind::MINUS, children);
              children = {pow2BvSize, intized_children[0]};
              d_bvToIntCache[current] = d_nm->mkNode(kind::MINUS, children);
              break;
            }
            case kind::BITVECTOR_TO_NAT:
            {
              d_bvToIntCache[current] = intized_children[0];
              break;
            }
            case kind::BITVECTOR_AND:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              uint32_t granularity = options::solveBVAsInt();
              Node newNode = createBitwiseNode(
                  intized_children, 
                  bvsize, 
                  granularity, 
                  [](uint32_t x, uint32_t y) {
                    Assert((x >= 0 && y >= 0 && x <= 1 && y <= 1));
                    if (x == 0 && y == 0) return (uint32_t)0;
                    if (x == 0 && y == 1) return (uint32_t)0;
                    if (x == 1 && y == 0) return (uint32_t)0;
                    if (x == 1 && y == 1) return (uint32_t)1;
                    Assert(false);
                    //TODO to the compiler it looks like an incomplete function. what to do?
                  }
                  );
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_OR:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              uint32_t granularity = options::solveBVAsInt();
              Node newNode = createBitwiseNode(
                  intized_children, 
                  bvsize, 
                  granularity, 
                  [](uint32_t x, uint32_t y) {
                    Assert((x >= 0 && y >= 0 && x <= 1 && y <= 1));
                    if (x == 0 && y == 0) return (uint32_t) 0;
                    if (x == 0 && y == 1) return (uint32_t) 1;
                    if (x == 1 && y == 0) return (uint32_t) 1;
                    if (x == 1 && y == 1) return (uint32_t) 1;
                    Assert(false);
                  }
                  );
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_XOR:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              uint32_t granularity = options::solveBVAsInt();
              Node newNode = createBitwiseNode(
                  intized_children, 
                  bvsize, 
                  granularity, 
                  [](uint32_t x, uint32_t y) {
                    Assert((x >= 0 && y >= 0 && x <= 1 && y <= 1));
                    if (x == 0 && y == 0) return (uint32_t) 1;
                    if (x == 0 && y == 1) return (uint32_t) 0;
                    if (x == 1 && y == 0) return (uint32_t) 0;
                    if (x == 1 && y == 1) return (uint32_t) 1;
                    Assert(false);
                  }
                  );
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_XNOR:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              uint32_t granularity = options::solveBVAsInt();
              Node newNode = createBitwiseNode(
                  intized_children, 
                  bvsize, 
                  granularity, 
                  [](uint32_t x, uint32_t y) {
                    Assert((x >= 0 && y >= 0 && x <= 1 && y <= 1));
                    if (x == 0 && y == 0) return (uint32_t) 1;
                    if (x == 0 && y == 1) return (uint32_t) 0;
                    if (x == 1 && y == 0) return (uint32_t) 0;
                    if (x == 1 && y == 1) return (uint32_t) 1;
                    Assert(false);
                  }
                  );
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_NAND:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              uint32_t granularity = options::solveBVAsInt();
              Node newNode = createBitwiseNode(
                  intized_children, 
                  bvsize, 
                  granularity, 
                  [](uint32_t x, uint32_t y) {
                    Assert((x >= 0 && y >= 0 && x <= 1 && y <= 1));
                    if (x == 0 && y == 0) return (uint32_t) 1;
                    if (x == 0 && y == 1) return (uint32_t) 1;
                    if (x == 1 && y == 0) return (uint32_t) 1;
                    if (x == 1 && y == 1) return (uint32_t) 0;
                    Assert(false);
                  }
                  );
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_NOR:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              uint32_t granularity = options::solveBVAsInt();
              Node newNode = createBitwiseNode(
                  intized_children, 
                  bvsize, 
                  granularity, 
                  [](uint32_t x, uint32_t y) {
                    Assert((x >= 0 && y >= 0 && x <= 1 && y <= 1));
                    if (x == 0 && y == 0) return (uint32_t) 1;
                    if (x == 0 && y == 1) return (uint32_t) 0;
                    if (x == 1 && y == 0) return (uint32_t) 0;
                    if (x == 1 && y == 1) return (uint32_t) 0;
                    Assert(false);
                  }
                  );
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_SHL:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node newNode = createShiftNode(intized_children, bvsize, true);
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_LSHR:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node newNode = createShiftNode(intized_children, bvsize, false);
              d_bvToIntCache[current] = newNode;
              break;
            }
            case kind::BITVECTOR_ASHR:
            {
              std::cout << "panda not supposed to be here" << std::endl;
              Assert(false);
              break;
            }
            case kind::BITVECTOR_ITE:
            {
              std::cout << "panda not supposed to be here" << std::endl;
              Assert(false);
              break;
            }
            case kind::BITVECTOR_CONCAT:
            {
              size_t bvsizeRight = current[1].getType().getBitVectorSize();
              Node pow2BvSizeRight = pow2(bvsizeRight);
              Node a = d_nm->mkNode(kind::MULT, intized_children[0], pow2BvSizeRight);
              Node b = intized_children[1];
              Node sum = d_nm->mkNode(kind::PLUS, a, b);
              d_bvToIntCache[current] = sum;
              break;
            }
            case kind::BITVECTOR_EXTRACT:
            {
              //current = a[i:j]
              Node a = current[0];
              size_t i = bv::utils::getExtractHigh(current);
              size_t j = bv::utils::getExtractLow(current);
              Assert(d_bvToIntCache.find(a) != d_bvToIntCache.end());
              Node div = d_nm->mkNode(kind::INTS_DIVISION_TOTAL, d_bvToIntCache[a], pow2(j));
              Node difference = d_nm->mkNode(kind::MINUS, d_nm->mkConst<Rational>(i), d_nm->mkConst<Rational>(j));
              Node plus = d_nm->mkNode(kind::PLUS, difference, d_nm->mkConst<Rational>(1));
              Node pow = pow2(plus);
              Node mod = d_nm->mkNode(kind::INTS_MODULUS_TOTAL, div, pow);
              d_bvToIntCache[current] = mod;
              break;
            }
            case kind::BITVECTOR_ULTBV:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_SLTBV:
            {
              Unimplemented();
              break;
            }
            case kind::EQUAL:
            {
              d_bvToIntCache[current] = d_nm->mkNode(kind::EQUAL, intized_children);
              break;
            }
            case kind::BITVECTOR_ULT:
            {
              d_bvToIntCache[current] = d_nm->mkNode(kind::LT, intized_children);
              break;
            }
            case kind::BITVECTOR_ULE:
            {
              d_bvToIntCache[current] = d_nm->mkNode(kind::LEQ, intized_children);
              break;
            }
            case kind::BITVECTOR_UGT:
            {
              d_bvToIntCache[current] = d_nm->mkNode(kind::GT, intized_children);
              break;
            }
            case kind::BITVECTOR_UGE:
            {
              d_bvToIntCache[current] = d_nm->mkNode(kind::GEQ, intized_children);
              break;
            }
            case kind::LT:
            {
              d_bvToIntCache[current] = current;
              break;
            }
            case kind::LEQ:
            {
              d_bvToIntCache[current] = current;
              break;
            }
            case kind::GT:
            {
              d_bvToIntCache[current] = current;
              break;
            }
            case kind::GEQ:
            {
              d_bvToIntCache[current] = current;
              break;
            }
            case kind::ITE:
	    {
                d_bvToIntCache[current] = d_nm->mkNode(oldKind, intized_children);
                break;
	    }
            case kind::APPLY_UF:
            {
              std::cout << "panda I do not expect to be here" << std::endl;
              Assert(false);
              break;
            }
            default:
	    {
              if (Theory::theoryOf(current) == THEORY_BOOL)
              {
                d_bvToIntCache[current] = d_nm->mkNode(oldKind, intized_children);
                break;
              } else {
                throw TypeCheckingException(
                  current.toExpr(),
                  string("Cannot translate to BV: ") + current.toString());
              }
	    }
          }
	}
        toVisit.pop_back();
      }
    }


  }
  return d_bvToIntCache[n];
}


BVToInt::BVToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-to-int"),
      d_binarizeCache(),
      d_eliminationCache(),
      d_bvToIntCache(),
      d_rangeAssertions()
{
  d_nm = NodeManager::currentNM();
  //TODO the following line is a hack because the mkNode may complain
  d_rangeAssertions.push_back(d_nm->mkConst<bool>(true));
  d_rangeAssertions.push_back(d_nm->mkConst<bool>(true));
};

PreprocessingPassResult BVToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  AlwaysAssert(!options::incrementalSolving());
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, Rewriter::rewrite(bvToInt((*assertionsToPreprocess)[i])));
  }
  Node rangeAssertions = Rewriter::rewrite(d_nm->mkNode(kind::AND, d_rangeAssertions));
  assertionsToPreprocess->push_back(rangeAssertions);
  return PreprocessingPassResult::NO_CONFLICT;
}

Node BVToInt::createShiftNode(vector<Node> children, uint32_t bvsize, bool isLeftShift) {
  Node x = children[0];
  Node y = children[1];
  Node ite = pow2(d_nm->mkConst<Rational>(0));
  for (uint32_t i=1; i < bvsize; i++) {
    ite = d_nm->mkNode(kind::ITE, d_nm->mkNode(kind::EQUAL, y, d_nm->mkConst<Rational>(i)), pow2(d_nm->mkConst<Rational>(i)), ite);
  }
  //from smtlib:
  //[[(bvshl s t)]] := nat2bv[m](bv2nat([[s]]) * 2^(bv2nat([[t]])))
  // [[(bvlshr s t)]] := nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
  Node result;
  if (isLeftShift) {
    result = d_nm->mkNode(kind::ITE, d_nm->mkNode(kind::LT, y, d_nm->mkConst<Rational>(bvsize)), d_nm->mkNode(kind::INTS_MODULUS_TOTAL, d_nm->mkNode(kind::MULT, x, ite) , pow2(bvsize)), d_nm->mkConst<Rational>(0));
  } else {
    //logical right shift
    result = d_nm->mkNode(kind::ITE, d_nm->mkNode(kind::LT, y, d_nm->mkConst<Rational>(bvsize)), d_nm->mkNode(kind::INTS_MODULUS_TOTAL, d_nm->mkNode(kind::INTS_DIVISION_TOTAL, x, ite) , pow2(bvsize)), d_nm->mkConst<Rational>(0));
  }
  return result;
}

Node BVToInt::createITEFromTable(Node x, Node y, uint32_t bitwidth, std::map<std::pair<uint32_t, uint32_t>, uint32_t> table) {
  Node ite = d_nm->mkConst<Rational>(table[std::make_pair(0, 0)]);
  for (uint32_t i=0; i < pow(2, bitwidth); i++) {
    for (uint32_t j=0; j < pow(2, bitwidth); j++) {
      if ((i == 0) && (j == 0)) {
        continue;
      }
      ite = d_nm->mkNode(
          kind::ITE, 
          d_nm->mkNode(kind::AND, 
            d_nm->mkNode(kind::EQUAL, x, d_nm->mkConst<Rational>(i)), 
            d_nm->mkNode(kind::EQUAL, y, d_nm->mkConst<Rational>(j))), 
          d_nm->mkConst<Rational>(table[std::make_pair(i,j)]), 
          ite);
    }
  }
  return ite;
}

Node BVToInt::createBitwiseNode(vector<Node> children, uint32_t bvsize, uint32_t granularity, uint32_t (*f)(uint32_t, uint32_t)) {
  Assert(granularity > 0);
  if (granularity > bvsize) {
    granularity = bvsize;
  } else {
    while (bvsize % granularity != 0) {
      granularity = granularity - 1;
    }
  }
  Assert(children.size() == 2);
  Node x = children[0];
  Node y = children[1];
 
  //transform f into a table
  //f is defined over 1 bit, while the table is defined over `granularity` bits
  std::map<std::pair<uint32_t, uint32_t>, uint32_t> table;
  for (uint32_t i=0; i < pow(2, granularity); i++) {
    for (uint32_t j=0; j < pow(2, granularity); j++) {
      uint32_t sum = 0;
      for (uint32_t n=0; n < granularity; n++) {
        sum += f(((uint32_t) (i / pow(2, n))) % 2 , ((uint32_t) ( j / pow(2, n))) % 2) * pow(2,n);
      }
      table[std::make_pair(i, j)] = sum;      
    }
  }
  //transform the table into an ite
  
  //create the big sum
  uint32_t sumSize = bvsize / granularity;
  Node sumNode = d_nm->mkConst<Rational>(0);
  //extract definition
  //(define-fun intextract ((k Int) (i Int) (j Int) (a Int)) Int 
  //  (mod (div a (two_to_the j)) (two_to_the (+ (- i j) 1))))
  for (uint32_t i = 0; i < sumSize; i++) {
    Node xExtract = d_nm->mkNode(
        kind::INTS_MODULUS_TOTAL,
        d_nm->mkNode(kind::INTS_DIVISION_TOTAL, x, pow2(i*granularity)), 
        pow2(granularity));
    Node yExtract = d_nm->mkNode(
        kind::INTS_MODULUS_TOTAL, 
        d_nm->mkNode(kind::INTS_DIVISION_TOTAL, y, pow2(i*granularity)), 
        pow2(granularity));
    Node ite = createITEFromTable(xExtract, yExtract, granularity, table);
    sumNode = d_nm->mkNode(
        kind::PLUS,
        sumNode,
        d_nm->mkNode(kind::MULT, pow2(i), ite));
  }
  return sumNode;
}



}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
