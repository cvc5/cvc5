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

struct bvToInt_stack_element
{
  TNode node;
  bool children_added;
  bvToInt_stack_element(TNode node) : node(node), children_added(false) {}
}; /* struct bvToInt_stack_element */

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

Node bvToIntMakeBinary(TNode n, NodeMap& cache)
{
  // Do a topological sort of the subexpressions and substitute them
  vector<bvToInt_stack_element> toVisit;
  toVisit.push_back(n);

  while (!toVisit.empty())
  {
    // The current node we are processing
    bvToInt_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    NodeMap::iterator find = cache.find(current);
    if (find != cache.end())
    {
      toVisit.pop_back();
      continue;
    }
    if (stackHead.children_added)
    {
      // Children have been processed, so rebuild this node
      Node result;
      NodeManager* nm = NodeManager::currentNM();
      if (current.getNumChildren() > 2
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
        for (unsigned i = 0; i < current.getNumChildren(); ++i)
        {
          Assert(cache.find(current[i]) != cache.end());
          builder << cache[current[i]];
        }
        result = builder;
      }
      cache[current] = result;
      toVisit.pop_back();
    }
    else
    {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0)
      {
        stackHead.children_added = true;
        // We need to add the children
        for (TNode::iterator child_it = current.begin();
             child_it != current.end();
             ++child_it)
        {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = cache.find(childNode);
          if (childFind == cache.end())
          {
            toVisit.push_back(childNode);
          }
        }
      }
      else
      {
        cache[current] = current;
        toVisit.pop_back();
      }
    }
  }
  return cache[n];
}

//eliminate many bit-vector operators before the translation to integers.
Node eliminationPass(TNode n) {
  std::vector<Node> toVisit;
  NodeSet cache;
  toVisit.push_back(n);
  Node newNode;
  while (!toVisit.empty()) {
    Node current = toVisit.back();
    toVisit.pop_back();
    if (cache.find(current) != cache.end()) {
      //work
      Kind k = current.getKind();
      switch (k)
      {
        case kind::BITVECTOR_SDIV:
	{
	  Assert(RewriteRule<SdivEliminate>::applies(current));
	  newNode = RewriteRule<SdivEliminate>::run<false>(current);
	  cache.insert(newNode);
          break;
	}
        case kind::BITVECTOR_SREM:
	{
	  Assert(RewriteRule<SremEliminate>::applies(current));
	  newNode = RewriteRule<SremEliminate>::run<false>(current);
	  cache.insert(newNode);
          break;
	}
        case kind::BITVECTOR_SMOD:
	{
	  Assert(RewriteRule<SmodEliminate>::applies(current));
	  newNode = RewriteRule<SmodEliminate>::run<false>(current);
	  cache.insert(newNode);
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
	  Assert(RewriteRule<RepeatEliminate>::applies(current));
	  newNode = RewriteRule<RepeatEliminate>::run<false>(current);
	  cache.insert(newNode);
          break;
	}
	case kind::BITVECTOR_SIGN_EXTEND:
	{
	  Assert(RewriteRule<SignExtendEliminate>::applies(current));
	  newNode = RewriteRule<SignExtendEliminate>::run<false>(current);
	  cache.insert(newNode);
          break;
	}
	case kind::BITVECTOR_ROTATE_RIGHT:
	{
	  Assert(RewriteRule<RotateRightEliminate>::applies(current));
	  newNode = RewriteRule<RotateRightEliminate>::run<false>(current);
	  cache.insert(newNode);
          break;
	}
	case kind::BITVECTOR_ROTATE_LEFT:
	{
	  Assert(RewriteRule<RotateLeftEliminate>::applies(current));
	  newNode = RewriteRule<RotateLeftEliminate>::run<false>(current);
	  cache.insert(newNode);
          break;
	}
	case kind::BITVECTOR_COMP:
	{
	  Assert(RewriteRule<CompEliminate>::applies(current));
	  newNode = RewriteRule<CompEliminate>::run<false>(current);
	  cache.insert(newNode);
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
	  newNode = RewriteRule<SleEliminate>::run<false>(current);
	  cache.insert(newNode);
          break;
	}
	default: Assert(false);  
      }
      if (current == n) {
	n = newNode;
      }
      size_t numChildren = current.getNumChildren();
      for (size_t i = 0; i < numChildren; i++) {
        toVisit.push_back(current[i]);
      }
    }
  }
  return n;
}

Node bvToInt(TNode n, NodeMap& cache)
{
  //first we rewrite n to eliminate some bv operators.
  n = Rewriter::rewrite(n);
  AlwaysAssert(!options::incrementalSolving());
  NodeManager* nm = NodeManager::currentNM();
  vector<bvToInt_stack_element> toVisit;
  NodeMap binaryCache;
  Node n_binary = bvToIntMakeBinary(n, binaryCache);
  Node n_eliminated = eliminationPass(n_binary);
  toVisit.push_back(TNode(n_eliminated));
  vector<Node> intized_children;
  Node one_const = nm->mkConst<Rational>(1);
  while (!toVisit.empty())
  {
    // The current node we are processing
    bvToInt_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    // If node is already in the cache we're done, pop from the stack
    NodeMap::iterator find = cache.find(current);
    if (find != cache.end())
    {
      toVisit.pop_back();
      continue;
    }

    // Not yet substituted, so process
    if (stackHead.children_added)
    {
      // Children have been processed, so rebuild this node.
      // First, save the rewritten children from the cache.
      intized_children.clear();
      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        TNode childRes = cache[current[i]];
        intized_children.push_back(childRes);
      }

      kind::Kind_t oldKind = current.getKind();
      Node intized_node = current;
      uint32_t bvsize = current.getType().getBitVectorSize();
      Node pow2_bvsize = pow2(bvsize, nm);
      switch (oldKind)
      {
        case kind::BITVECTOR_PLUS: 
	{
          Assert(intized_children.size() == 2);
      	  Node plus = getNode(kind::PLUS, intized_children);
	  intized_node = getNode(kind::INTS_MODULUS_TOTAL, {plus, pow2_bvsize});
	  break;
	}
        case kind::BITVECTOR_MULT: 
	{
          Assert(intized_children.size() == 2);
      	  Node mul = getNode(kind::MULT, intized_children);
	  intized_node = getNode(kind::INTS_MODULUS_TOTAL, {mul, pow2_bvsize});
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
	  Assert(intized_children.size() == 1);
	  intized_node = getNode(kind::MINUS, {pow2_bvsize, intized_children[0]});
          break;
	}  
        case kind::BITVECTOR_NOT: 
	{
	  Assert(intized_children.size() == 1);
	  Node max = getNode(kind::MINUS, {pow2_bvsize, one_const});
	  intized_node = getNode(kind::MINUS, {pow2_bvsize, intized_children[0]});
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
	  intized_node = getNode(kind::EQUAL, intized_children);
	  break;
	}
        case kind::BITVECTOR_ULT:
	{
	  intized_node = getNode(kind::LT, intized_children);
	  break;
	}
        case kind::BITVECTOR_ULE:
	{
	  intized_node = getNode(kind::LEQ, intized_children);
	  break;
	}
        case kind::BITVECTOR_UGT:
	{
	  intized_node = getNode(kind::GT, intized_children);
	  break;
	}
        case kind::BITVECTOR_UGE:
	{
	  intized_node = getNode(kind::GEQ, intized_children);
	  break;
	}
        case kind::ITE:
	    intized_node = getNode(oldKind, intized_children);
	    break;
        default:
          if (Theory::theoryOf(current) == THEORY_BOOL)
          {
	    intized_node = getNode(oldKind, intized_children);
            break;
          }
          throw TypeCheckingException(
              current.toExpr(),
              string("Cannot translate to BV: ") + current.toString());
      }
      toVisit.pop_back();
      cache[current] = intized_node;
    }
    else
    {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0)
      {
        stackHead.children_added = true;
        // We need to add the children
        for (TNode::iterator child_it = current.begin();
             child_it != current.end();
             ++child_it)
        {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = cache.find(childNode);
          if (childFind == cache.end())
          {
            toVisit.push_back(childNode);
          }
        }
      }
      else
      {
        // It's a leaf: could be a variable or a numeral
        Node result = current;
        if (current.isVar())
        {
          if (current.getType().isBitVector())
          {
            result = nm->mkSkolem("__bvToInt_var",
                                  nm->integerType(),
                                  "Variable introduced in bvToInt pass");
          }
          else
          {
            AlwaysAssert(current.getType() == nm->booleanType());
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
              result = nm->mkConst<Rational>(c);
              break;
            }
            case kind::CONST_BOOLEAN: break;
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
        cache[current] = result;
        toVisit.pop_back();
      }
    }
  }
  return cache[n_binary];
}
}  // namespace

BVToInt::BVToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-to-int"){};

PreprocessingPassResult BVToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  unordered_map<Node, Node, NodeHashFunction> cache;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, bvToInt((*assertionsToPreprocess)[i], cache));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
