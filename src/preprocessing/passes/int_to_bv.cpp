/*********************                                                        */
/*! \file int_to_bv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;


namespace {

struct intToBV_stack_element
{
  TNode d_node;
  bool d_children_added;
  intToBV_stack_element(TNode node) : d_node(node), d_children_added(false) {}
}; /* struct intToBV_stack_element */



Node intToBVMakeBinary(TNode n, NodeMap& cache)
{
  // Do a topological sort of the subexpressions and substitute them
  vector<intToBV_stack_element> toVisit;
  toVisit.push_back(n);

  while (!toVisit.empty())
  {
    // The current node we are processing
    intToBV_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.d_node;

    NodeMap::iterator find = cache.find(current);
    if (find != cache.end())
    {
      toVisit.pop_back();
      continue;
    }
    if (stackHead.d_children_added)
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
        if (current.getKind() == kind::APPLY_UF) {
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
      toVisit.pop_back();
    }
    else
    {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0)
      {
        stackHead.d_children_added = true;
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

}  // namespace

Node IntToBV::intToBV(TNode n, NodeMap& cache)
{
  NodeManager* nm = NodeManager::currentNM();
  int size = options::solveIntAsBV();
  AlwaysAssert(size > 0);
  AlwaysAssert(!options::incrementalSolving());

  vector<intToBV_stack_element> toVisit;
  NodeMap binaryCache;
  NodeMap divModElimCache;
  Node n_no_div_mod = intToBVElimDivMod(n, divModElimCache);
  Node n_binary = intToBVMakeBinary(n_no_div_mod, binaryCache);
  Node n_new;
  vector<Node> vec_divmod;
  vec_divmod.assign(d_divModAssertions.begin(), d_divModAssertions.end());
  if (vec_divmod.size() >= 1) {
    Node divmod;
    if (vec_divmod.size() > 1) {
      divmod = nm->mkNode(kind::AND, vec_divmod);
    } else {
      divmod = vec_divmod[0];
    }
    n_new = nm->mkNode(kind::AND, n_binary, divmod);
  } else {
    n_new = n;
  }
  toVisit.push_back(TNode(n_new));

  while (!toVisit.empty())
  {
    // The current node we are processing
    intToBV_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.d_node;

    // If node is already in the cache we're done, pop from the stack
    NodeMap::iterator find = cache.find(current);
    if (find != cache.end())
    {
      toVisit.pop_back();
      continue;
    }

    // Not yet substituted, so process
    if (stackHead.d_children_added)
    {
      // Children have been processed, so rebuild this node
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

      /**
       * The following switch statement calculates:
       * 1. The new operator: This is the BV variant of the integer operator.
       *    For some operators, it stays the same (e.g., equality).
       *    For others, the correspondence is straightforward (e.g., PLUS).
       *    For div and mod no new operator is specified.
       *    A more complicated Node is built in the construction stage.
       * 2. The necessary width to avoid overflows.
       */
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
          case kind::APPLY_UF:
          {
            /* The domain and range of UFs are changed.
             * If an argument is of type INT, it it changed
             * to BV. 
             * Otherwise, it stays intact.
             */
            newKind = kind::APPLY_UF;
            Node intUF = current.getOperator();
            TypeNode tn = intUF.getType();
            TypeNode intRange = tn.getRangeType();
            vector<TypeNode> intDomain = tn.getArgTypes();
          
            Node bvUF;
            TypeNode bvRange;
            vector<TypeNode> bvDomain;

            if (cache.find(intUF) != cache.end()) {
              bvUF = cache[intUF];
            } else {
              bvRange = intRange.isInteger() ? nm->mkBitVectorType(size) : intRange;
              for (TypeNode d: intDomain) {
                bvDomain.push_back(d.isInteger() ? nm->mkBitVectorType(size) : d);
              }
              ostringstream os;
              os << "__intToBV_fun_" << bvUF << "_bv";
              bvUF = nm->mkSkolem(os.str(), nm->mkFunctionType(bvDomain, bvRange), "int2bv function");
              cache[intUF] = bvUF;
            }
            break;
          }
          case kind::LT: newKind = kind::BITVECTOR_SLT; break;
          case kind::LEQ: newKind = kind::BITVECTOR_SLE; break;
          case kind::GT: newKind = kind::BITVECTOR_SGT; break;
          case kind::GEQ: newKind = kind::BITVECTOR_SGE; break;
          case kind::EQUAL:
          case kind::ITE: break;
          default:
            if (Theory::theoryOf(current) == THEORY_BOOL)
            {
              break;
            }
            throw TypeCheckingException(
                current.toExpr(),
                string("Cannot translate to BV: ") + current.toString());
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
      if (newKind == kind::APPLY_UF) {
        builder << cache[current.getOperator()];
      }
      for (unsigned i = 0; i < children.size(); ++i)
      {
        builder << children[i];
      }
      // Mark the substitution and continue
      Node result = builder;

      result = Rewriter::rewrite(result);
      cache[current] = result;
      toVisit.pop_back();
    }
    else
    {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0)
      {
        stackHead.d_children_added = true;
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
          if (current.getType() == nm->integerType())
          {
            result = nm->mkSkolem("__intToBV_var",
                                  nm->mkBitVectorType(size),
                                  "Variable introduced in intToBV pass");
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
            case kind::CONST_RATIONAL:
            {
              Rational constant = current.getConst<Rational>();
              AlwaysAssert(constant.isIntegral());
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
              break;
            }
            case kind::CONST_BOOLEAN: break;
            default:
              throw TypeCheckingException(
                  current.toExpr(),
                  string("Cannot translate const to BV: ")
                      + current.toString());
          }
        }
        else
        {
          throw TypeCheckingException(
              current.toExpr(),
              string("Cannot translate to BV: ") + current.toString());
        }
        cache[current] = result;
        toVisit.pop_back();
      }
    }
  }
  return cache[n_new];
}


void IntToBV::saveDivModEliminationAssertion(Node current, Node skolem) {
  /** from SMT-LIB:
  * (for all ((m Int) (n Int))
  *    (=> (distinct n 0)
  *        (let ((q (div m n)) (r (mod m n)))
  *          (and (= m (+ (* n q) r))
  *               (<= 0 r (- (abs n) 1))))))
  */
  NodeManager* nm = NodeManager::currentNM();
  kind::Kind_t k = current.getKind();
  Assert(k == kind::INTS_DIVISION_TOTAL || k == kind::INTS_MODULUS_TOTAL);
  Node m = current[0];
  Node n = current[1];
  Node q;
  Node r;
  if (k == kind::INTS_DIVISION_TOTAL) {
    q = skolem;
    r = nm->mkSkolem("__intToBV_var_mod", 
            nm->integerType(), 
            "Variable introduced in intToBV preprocessing pass to represent a mod term");
  } else {
    q = nm->mkSkolem("__intToBV_var_mod", 
            nm->integerType(), 
            "Variable introduced in intToBV preprocessing pass to represent a mod term");
    r = skolem;
  }
  Node mul = nm->mkNode(kind::MULT, n, q);
  Node plus = nm->mkNode(kind::PLUS, mul, r);
  Node eq = nm->mkNode(kind::EQUAL, m, plus);
  Node zero = nm->mkConst<Rational>(0);
  Node one= nm->mkConst<Rational>(1);
  Node leq1 = nm->mkNode(kind::LEQ, zero, r);
  Node cond = nm->mkNode(kind::LT, n, zero);
  Node then_branch = nm->mkNode(kind::UMINUS, n);
  Node else_branch = n;
  Node abs = nm->mkNode(kind::ITE, cond, then_branch, else_branch);
  Node upper_bound = nm->mkNode(kind::MINUS, abs, one);
  Node leq2 = nm->mkNode(kind::LEQ, r, upper_bound);
  Node lemma = nm->mkNode(kind::AND, eq, leq1, leq2);
  d_divModAssertions.insert(lemma);
}

Node IntToBV::intToBVElimDivMod(TNode n, NodeMap& cache) 
{
  vector<intToBV_stack_element> toVisit;
  toVisit.push_back(n);

  while (!toVisit.empty())
  {
    // The current node we are processing
    intToBV_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.d_node;

    NodeMap::iterator find = cache.find(current);
    if (find != cache.end())
    {
      toVisit.pop_back();
      continue;
    }
    if (stackHead.d_children_added)
    {
      NodeManager* nm = NodeManager::currentNM();
      // Children have been processed, so rebuild this node
      kind::Kind_t k = current.getKind();
      if (k == kind::INTS_DIVISION_TOTAL) {
        Node divSkolem = nm->mkSkolem("__intToBV_var_mod", 
            nm->integerType(), 
            "Variable introduced in intToBV preprocessing pass to represent a mod term");
        cache[current] = divSkolem;
        saveDivModEliminationAssertion(current, divSkolem);
      } else if (k == kind::INTS_MODULUS_TOTAL) {
        Node modSkolem = nm->mkSkolem("__intToBV_var_mod", 
            nm->integerType(), 
            "Variable introduced in intToBV preprocessing pass to represent a mod term");
        cache[current] = modSkolem;
        saveDivModEliminationAssertion(current, modSkolem);
      } else {
        NodeBuilder<> builder(k);
        if (k == kind::APPLY_UF) {
          builder << current.getOperator();
        }
        for (unsigned i = 0; i < current.getNumChildren(); ++i)
        {
          Assert(cache.find(current[i]) != cache.end());
          builder << cache[current[i]];
        }
        cache[current] = builder;
      }
      toVisit.pop_back();
    }
    else
    {
      if (current.getNumChildren() > 0)
      {
        stackHead.d_children_added = true;
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
        //Node has no children, it does not need to change.
        cache[current] = current;
        toVisit.pop_back();
      }
    }
  }
  return cache[n];
}

IntToBV::IntToBV(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "int-to-bv"){};


PreprocessingPassResult IntToBV::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  unordered_map<Node, Node, NodeHashFunction> cache;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    Trace("int-to-bv-debug") << "processing: " << (*assertionsToPreprocess)[i];
    assertionsToPreprocess->replace(
        i, intToBV((*assertionsToPreprocess)[i], cache));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
