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

#include "expr/node.h"
#include "theory/rewriter.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;
using namespace CVC4::theory::bv;


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
            k == kind::BITVECTOR_OR)) {
        Assert(d_binarizeCache.find(current[0]) != d_binarizeCache.end());
        Node result = d_binarizeCache[current[0]];
        for (unsigned i = 1; i < numChildren; i++)
        {
          Assert(d_binarizeCache.find(current[i]) != d_binarizeCache.end());
          Node child = d_binarizeCache[current[i]];
          result = d_nm->mkNode(current.getKind(), result, child);
        }
        d_binarizeCache[current] = result;
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
        for (size_t i=0; i<numChildren; i++) {
          Assert(d_eliminationCache.find(currentEliminated[i]) != d_eliminationCache.end());
          children.push_back(d_eliminationCache[currentEliminated[i]]);
        }
        d_eliminationCache[current] = d_nm->mkNode(currentEliminated.getOperator(), children);
      }
    } else {
        if (d_eliminationCache.find(current) != d_eliminationCache.end()) {
          continue;
        } else {
            currentEliminated = FixpointRewriteStrategy<
            	 RewriteRule<SdivEliminate>,
            	 RewriteRule<SremEliminate>,
            	 RewriteRule<SmodEliminate>,
            	 RewriteRule<RepeatEliminate>,
            	 RewriteRule<SignExtendEliminate>,
            	 RewriteRule<RotateRightEliminate>,
            	 RewriteRule<RotateLeftEliminate>,
            	 RewriteRule<CompEliminate>,
            	 RewriteRule<SleEliminate>,
            	 RewriteRule<SltEliminate>
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
              mod = Rewriter::rewrite(mod);
              d_bvToIntCache[current] = mod;
              break;
            }
            case kind::BITVECTOR_MULT: 
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              Node mul = d_nm->mkNode(kind::MULT, intized_children);
              vector<Node> children = {mul, pow2BvSize};
              d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(kind::INTS_MODULUS_TOTAL, children));
              break;
            }
            case kind::BITVECTOR_SUB:
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              Node sub = d_nm->mkNode(kind::MINUS, intized_children);
              vector<Node> children = {sub, pow2BvSize};
              d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(kind::INTS_MODULUS_TOTAL, children));
              break;
            }
            case kind::BITVECTOR_UDIV:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_UREM:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_UDIV_TOTAL:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_UREM_TOTAL:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_NEG: 
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              vector<Node> children = {pow2BvSize, intized_children[0]};
              d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(kind::MINUS, children));
              break;
            }  
            case kind::BITVECTOR_NOT: 
            {
       	      uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2BvSize = pow2(bvsize);
              vector<Node> children = {pow2BvSize, one_const};
              Node max = d_nm->mkNode(kind::MINUS, children);
              children = {pow2BvSize, intized_children[0]};
              d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(kind::MINUS, children));
              break;
            }  
            case kind::BITVECTOR_AND:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_OR:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_XOR:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_XNOR:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_NAND:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_NOR:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_SHL:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_LSHR:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_ASHR:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_ITE:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_CONCAT:
            {
              size_t bvsizeRight = current[1].getType().getBitVectorSize();
              Node pow2BvSizeRight = pow2(bvsizeRight);
              Node a = d_nm->mkNode(kind::MULT, intized_children[0], pow2BvSizeRight);
              Node b = intized_children[1];
              Node sum = d_nm->mkNode(kind::PLUS, a, b);
              d_bvToIntCache[current] = Rewriter::rewrite(sum);
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
              d_bvToIntCache[current] = Rewriter::rewrite(mod);
              break;
            }
            case kind::BITVECTOR_ZERO_EXTEND:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_SIGN_EXTEND:
            {
              Unimplemented();
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
              d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(kind::EQUAL, intized_children));
              break;
            }
            case kind::BITVECTOR_ULT:
            {
              d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(kind::LT, intized_children));
              break;
            }
            case kind::BITVECTOR_ULE:
            {
              d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(kind::LEQ, intized_children));
              break;
            }
            case kind::BITVECTOR_UGT:
            {
              d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(kind::GT, intized_children));
              break;
            }
            case kind::BITVECTOR_UGE:
            {
              d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(kind::GEQ, intized_children));
              break;
            }
            case kind::ITE:
	    {
                d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(oldKind, intized_children));
                break;
	    }
            default:
	    {
              if (Theory::theoryOf(current) == THEORY_BOOL)
              {
                d_bvToIntCache[current] = Rewriter::rewrite(d_nm->mkNode(oldKind, intized_children));
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
};

PreprocessingPassResult BVToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  AlwaysAssert(!options::incrementalSolving());
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, bvToInt((*assertionsToPreprocess)[i]));
  }
  Node rangeAssertions = Rewriter::rewrite(d_nm->mkNode(kind::AND, d_rangeAssertions));
  assertionsToPreprocess->push_back(rangeAssertions);
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
