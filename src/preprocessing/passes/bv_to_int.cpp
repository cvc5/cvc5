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

using NodeMap = std::unordered_map<Node, Node, NodeHashFunction>;
using NodeSet = std::unordered_set<Node, NodeHashFunction>;

namespace {

Node getNode(kind::Kind_t nodeKind, vector<Node> children) {
	NodeBuilder<> builder(nodeKind);
	uint32_t num_of_children = children.size();
	for (uint32_t i=0; i < num_of_children; i++) {
		builder << children[i];
	}
	Node result = builder;
	result = Rewriter::rewrite(result);
	return result;

}

Node pow2(uint32_t k, NodeManager* nm)
{
	  Node two_const = nm->mkConst<Rational>(2);
	  Node k_const = nm->mkConst<Rational>(k);
	  vector<Node> children{ two_const, k_const };
	  Node result = getNode(kind::POW, children);
	  return result;
}

Node makeBinary(Node n, NodeMap binarizeCache)
{
  vector<Node> toVisit;
  toVisit.push_back(n);
  Node result = n;
  while (!toVisit.empty())
  {
    // The current node we are processing
    Node current = toVisit.back();
    if (binarizeCache.find(current) == binarizeCache.end()) {
      binarizeCache[current] = Node();
      if (current.getNumChildren() > 0)
      {
        for (Node::iterator child_it = current.begin();
             child_it != current.end();
             ++child_it)
        {
          Node childNode = *child_it;
	  toVisit.push_back(childNode);
        }
      }
    }
    else if (binarizeCache[current].isNull())
    {
      NodeBuilder<> builder(current.getKind());
      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        builder << current[i];
      }
      if (current == n) {
        result = builder;
      }
      binarizeCache[current] = result;
      toVisit.pop_back();
    }
    else
    {
      continue;
    }
  }
  return result;
}

//eliminate many bit-vector operators before the translation to integers.
Node eliminationPass(Node n, NodeMap& eliminationCache){
  std::vector<Node> toVisit;
  toVisit.push_back(n);
  while (!toVisit.empty()) {
    Node current = toVisit.back();
    toVisit.pop_back();
    if (eliminationCache.find(current) == eliminationCache.end()) {
      //work
      Kind k = current.getKind();




      switch (k)
      {
        case kind::BITVECTOR_SDIV:
	{
	  Assert(RewriteRule<SdivEliminate>::applies(current));
	  eliminationCache[current] = RewriteRule<SdivEliminate>::run<false>(current);
          break;
	}
        case kind::BITVECTOR_SREM:
	{
	  Assert(RewriteRule<SremEliminate>::applies(current));
	  eliminationCache[current] = RewriteRule<SremEliminate>::run<false>(current);
          break;
	}
        case kind::BITVECTOR_SMOD:
	{
	  Assert(RewriteRule<SmodEliminate>::applies(current));
	  eliminationCache[current] = RewriteRule<SmodEliminate>::run<false>(current);
          break;
	}
	case kind::BITVECTOR_ITE:
	{
	  Unimplemented();
	  break;
	}
	case kind::BITVECTOR_REPEAT:
	{
	  Assert(RewriteRule<RepeatEliminate>::applies(current));
	  eliminationCache[current] = RewriteRule<RepeatEliminate>::run<false>(current);
          break;
	}
	case kind::BITVECTOR_SIGN_EXTEND:
	{
	  Assert(RewriteRule<SignExtendEliminate>::applies(current));
	  eliminationCache[current] = RewriteRule<SignExtendEliminate>::run<false>(current);
          break;
	}
	case kind::BITVECTOR_ROTATE_RIGHT:
	{
	  Assert(RewriteRule<RotateRightEliminate>::applies(current));
	  eliminationCache[current] = RewriteRule<RotateRightEliminate>::run<false>(current);
          break;
	}
	case kind::BITVECTOR_ROTATE_LEFT:
	{
	  Assert(RewriteRule<RotateLeftEliminate>::applies(current));
	  eliminationCache[current] = RewriteRule<RotateLeftEliminate>::run<false>(current);
          break;
	}
	case kind::BITVECTOR_COMP:
	{
	  Assert(RewriteRule<CompEliminate>::applies(current));
	  eliminationCache[current] = RewriteRule<CompEliminate>::run<false>(current);
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
	case kind::BITVECTOR_SLE:
	{
	  Assert(RewriteRule<SleEliminate>::applies(current));
	  eliminationCache[current] = RewriteRule<SleEliminate>::run<false>(current);
          break;
	}
	case kind::BITVECTOR_SLT:
	{
	  Assert(RewriteRule<SltEliminate>::applies(current));
	  eliminationCache[current] = RewriteRule<SltEliminate>::run<false>(current);
          break;
	}
	default: 
	{
	  eliminationCache[current] = current;
	  break;  
	}
      }
      if (eliminationCache.find(current) != eliminationCache.end() && current != eliminationCache[current]) {
	toVisit.push_back(eliminationCache[current]);
      } else {
        size_t numChildren = eliminationCache[current].getNumChildren();
        for (size_t i = 0; i < numChildren; i++) {
          toVisit.push_back(eliminationCache[current][i]);
        }
      }
    }
  }
  return eliminationCache[n];
}

Node bvToInt(Node n, NodeMap& binarizeCache, NodeMap& eliminationCache, NodeMap& bvToIntCache)
{
  NodeManager* nm = NodeManager::currentNM();
  n = makeBinary(n, binarizeCache);
  n = eliminationPass(n, eliminationCache);
  vector<Node> toVisit;
  toVisit.push_back(n);
  Node one_const = nm->mkConst<Rational>(1);
  while (!toVisit.empty())
  {
    Node current = toVisit.back();
    size_t currentNumChildren = current.getNumChildren();
    if (bvToIntCache.find(current) == bvToIntCache.end()) {
      bvToIntCache[current] = Node();
      for (size_t i=0; i < currentNumChildren; i++) {
	toVisit.push_back(current[i]);
      }
    } else {
      if (!bvToIntCache[current].isNull()) {
	//int version already computed. Do nothing.
	toVisit.pop_back();
      } else {
	//do actual work
        kind::Kind_t oldKind = current.getKind();
        if (currentNumChildren == 0) {
          if (current.isVar())
          {
            if (current.getType().isBitVector())
            {
              bvToIntCache[current] = nm->mkSkolem("__bvToInt_var",
                                    nm->integerType(),
                                    "Variable introduced in bvToInt pass instead of original variable" + current.toString());
            }
            else
            {
              AlwaysAssert(current.getType() == nm->booleanType());
	      bvToIntCache[current] = current;
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
                bvToIntCache[current] = nm->mkConst<Rational>(c);
                break;
              }
              case kind::CONST_BOOLEAN: 
	      {
                bvToIntCache[current] = current;
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
	    intized_children.push_back(bvToIntCache[current[i]]);
	  }
	  switch (oldKind)
          {
            case kind::BITVECTOR_PLUS: 
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2_bvsize = pow2(bvsize, nm);
              Node plus = getNode(kind::PLUS, intized_children);
              bvToIntCache[current] = getNode(kind::INTS_MODULUS_TOTAL, {plus, pow2_bvsize});
              break;
            }
            case kind::BITVECTOR_MULT: 
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2_bvsize = pow2(bvsize, nm);
              Node mul = getNode(kind::MULT, intized_children);
              bvToIntCache[current] = getNode(kind::INTS_MODULUS_TOTAL, {mul, pow2_bvsize});
              break;
            }
            case kind::BITVECTOR_SUB:
            {
              Unimplemented();
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
            case kind::BITVECTOR_SDIV:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_SREM:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_SMOD:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_NEG: 
            {
              uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2_bvsize = pow2(bvsize, nm);
              bvToIntCache[current] = getNode(kind::MINUS, {pow2_bvsize, intized_children[0]});
              break;
            }  
            case kind::BITVECTOR_NOT: 
            {
       	      uint32_t bvsize = current[0].getType().getBitVectorSize();
              Node pow2_bvsize = pow2(bvsize, nm);
              Node max = getNode(kind::MINUS, {pow2_bvsize, one_const});
              bvToIntCache[current] = getNode(kind::MINUS, {pow2_bvsize, intized_children[0]});
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
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_EXTRACT:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_REPEAT:
            {
              Unimplemented();
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
            case kind::BITVECTOR_ROTATE_RIGHT:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_ROTATE_LEFT:
            {
              Unimplemented();
              break;
            }
            case kind::BITVECTOR_COMP:
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
              bvToIntCache[current] = getNode(kind::EQUAL, intized_children);
              break;
            }
            case kind::BITVECTOR_ULT:
            {
              bvToIntCache[current] = getNode(kind::LT, intized_children);
              break;
            }
            case kind::BITVECTOR_ULE:
            {
              bvToIntCache[current] = getNode(kind::LEQ, intized_children);
              break;
            }
            case kind::BITVECTOR_UGT:
            {
              bvToIntCache[current] = getNode(kind::GT, intized_children);
              break;
            }
            case kind::BITVECTOR_UGE:
            {
              bvToIntCache[current] = getNode(kind::GEQ, intized_children);
              break;
            }
            case kind::ITE:
	    {
                bvToIntCache[current] = getNode(oldKind, intized_children);
                break;
	    }
            default:
	    {
              if (Theory::theoryOf(current) == THEORY_BOOL)
              {
                bvToIntCache[current] = getNode(oldKind, intized_children);
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
  return bvToIntCache[n];
}
}  // namespace

BVToInt::BVToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-to-int"){};

PreprocessingPassResult BVToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  AlwaysAssert(!options::incrementalSolving());
  NodeMap binarizeCache;
  NodeMap eliminationCache;
  NodeMap bvToIntCache;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, bvToInt((*assertionsToPreprocess)[i], binarizeCache, eliminationCache, bvToIntCache));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
