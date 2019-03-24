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
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

using NodeMap = std::unordered_map<Node, Node, NodeHashFunction>;

namespace {

struct bvToInt_stack_element
{
  TNode node;
  bool children_added;
  bvToInt_stack_element(TNode node) : node(node), children_added(false) {}
}; /* struct bvToInt_stack_element */

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

Node bvToInt(TNode n, NodeMap& cache)
{
  AlwaysAssert(!options::incrementalSolving());

  vector<bvToInt_stack_element> toVisit;
  NodeMap binaryCache;
  Node n_binary = bvToIntMakeBinary(n, binaryCache);
  toVisit.push_back(TNode(n_binary));

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
    NodeManager* nm = NodeManager::currentNM();
    if (stackHead.children_added)
    {
      // Children have been processed, so rebuild this node
      vector<Node> children;

      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        Assert(cache.find(current[i]) != cache.end());
        TNode childRes = cache[current[i]];
        children.push_back(childRes);
      }

      kind::Kind_t oldKind = current.getKind();
      switch (oldKind)
      {
        case kind::BITVECTOR_PLUS: 
	{
          Assert(children.size() == 2);
	  uint32_t bvsize = current.getType().getBitVectorSize();
	  NodeBuilder<> powBuilder(kind::POW);
	  Node two_const = nm->mkConst<Rational>(2);
	  Node bvsize_const = nm->mkConst<Rational>(bvsize);
	  powBuilder << two_const;
	  powBuilder << bvsize_const;
	  Node pow = powBuilder; 
      	  NodeBuilder<> plusBuilder(kind::PLUS);
      	  for (unsigned i = 0; i < children.size(); ++i)
      	  {
      	    plusBuilder << children[i];
      	  }
      	  Node plus = plusBuilder;
          //plus = Rewriter::rewrite(plus);
	  NodeBuilder<> modBuilder(kind::INTS_MODULUS_TOTAL);
	  modBuilder << plus;
	  modBuilder << pow;
	  Node mod = modBuilder;
	  //mod = Rewriter::rewrite(mod);
          cache[current] = mod;
          toVisit.pop_back();
	  break;
	}
        case kind::BITVECTOR_MULT: 
	{
          Assert(children.size() == 2);
	  Assert(false);
          break;
	}
        case kind::BITVECTOR_SUB:
	{
          Assert(children.size() == 2);
	  Assert(false);
          break;
	}
        case kind::UMINUS: 
	{
          Assert(children.size() == 1);
	  Assert(false);
          break;
	}  
        case kind::BITVECTOR_ULT: 
	{
	  Assert(false);
	  break;
	}
        case kind::BITVECTOR_ULE: 
	{
	  Assert(false);
	  break;
	}
        case kind::BITVECTOR_UGT: 
	{
	  Assert(false);
	  break;
	}
        case kind::BITVECTOR_UGE: 
	{
	  Assert(false);
	  break;
	}
        case kind::EQUAL:
	{
      	  NodeBuilder<> builder(oldKind);
      	  for (unsigned i = 0; i < children.size(); ++i)
      	  {
      	    builder << children[i];
      	  }
      	  // Mark the substitution and continue
      	  Node result = builder;

      	  result = Rewriter::rewrite(result);
      	  cache[current] = result;
      	  toVisit.pop_back();
	  break;
	}
        case kind::ITE: break;
        default:
	  std::cout << "panda " << current << " " << Theory::theoryOf(current) << std::endl;
          if (Theory::theoryOf(current) == THEORY_BOOL)
          {
	    toVisit.pop_back();
            break;
          }
          throw TypeCheckingException(
              current.toExpr(),
              string("Cannot translate to BV: ") + current.toString());
      }
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
