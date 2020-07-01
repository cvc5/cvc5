/*********************                                                        */
/*! \file unconstrained_simplifier.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Andres Noetzli, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simplifications based on unconstrained variables
 **
 ** This module implements a preprocessing phase which replaces certain
 ** "unconstrained" expressions by variables.  Based on Roberto
 ** Bruttomesso's PhD thesis.
 **/

#include "preprocessing/passes/unconstrained_simplifier.h"

#include "smt/smt_statistics_registry.h"
#include "theory/logic_info.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

UnconstrainedSimplifier::UnconstrainedSimplifier(
    PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "unconstrained-simplifier"),
      d_numUnconstrainedElim("preprocessor::number of unconstrained elims", 0),
      d_context(preprocContext->getDecisionContext()),
      d_substitutions(preprocContext->getDecisionContext()),
      d_logicInfo(preprocContext->getLogicInfo())
{
  smtStatisticsRegistry()->registerStat(&d_numUnconstrainedElim);
}

UnconstrainedSimplifier::~UnconstrainedSimplifier()
{
  smtStatisticsRegistry()->unregisterStat(&d_numUnconstrainedElim);
}

struct unc_preprocess_stack_element
{
  TNode node;
  TNode parent;
  unc_preprocess_stack_element(TNode n) : node(n) {}
  unc_preprocess_stack_element(TNode n, TNode p) : node(n), parent(p) {}
}; /* struct unc_preprocess_stack_element */

void UnconstrainedSimplifier::visitAll(TNode assertion)
{
  // Do a topological sort of the subexpressions and substitute them
  vector<unc_preprocess_stack_element> toVisit;
  toVisit.push_back(assertion);

  while (!toVisit.empty())
  {
    // The current node we are processing
    TNode current = toVisit.back().node;
    TNode parent = toVisit.back().parent;
    toVisit.pop_back();

    TNodeCountMap::iterator find = d_visited.find(current);
    if (find != d_visited.end())
    {
      if (find->second == 1)
      {
        d_visitedOnce.erase(current);
        if (current.isVar())
        {
          d_unconstrained.erase(current);
        }
        else
        {
          // Also erase the children from the visited-once set when we visit a
          // node a second time, otherwise variables in this node are not
          // erased from the set of unconstrained variables.
          for (TNode childNode : current)
          {
            toVisit.push_back(unc_preprocess_stack_element(childNode, current));
          }
        }
      }
      ++find->second;
      continue;
    }

    d_visited[current] = 1;
    d_visitedOnce[current] = parent;

    if (current.getNumChildren() == 0)
    {
      if (current.getKind() == kind::VARIABLE
          || current.getKind() == kind::SKOLEM)
      {
        d_unconstrained.insert(current);
      }
    }
    else if (current.isClosure())
    {
      // Throw an exception. This should never happen in practice unless the
      // user specifically enabled unconstrained simplification in an illegal
      // logic.
      throw LogicException(
          "Cannot use unconstrained simplification in this logic, due to "
          "(possibly internally introduced) quantified formula.");
    }
    else
    {
      for (TNode childNode : current)
      {
        toVisit.push_back(unc_preprocess_stack_element(childNode, current));
      }
    }
  }
}

Node UnconstrainedSimplifier::newUnconstrainedVar(TypeNode t, TNode var)
{
  Node n = NodeManager::currentNM()->mkSkolem(
      "unconstrained",
      t,
      "a new var introduced because of unconstrained variable "
          + var.toString());
  return n;
}

void UnconstrainedSimplifier::processUnconstrained()
{
  NodeManager* nm = NodeManager::currentNM();

  vector<TNode> workList(d_unconstrained.begin(), d_unconstrained.end());
  Node currentSub;
  TNode parent;
  bool swap;
  bool isSigned;
  bool strict;
  vector<TNode> delayQueueLeft;
  vector<Node> delayQueueRight;

  TNode current = workList.back();
  workList.pop_back();
  for (;;)
  {
    Assert(d_visitedOnce.find(current) != d_visitedOnce.end());
    parent = d_visitedOnce[current];
    if (!parent.isNull())
    {
      swap = isSigned = strict = false;
      bool checkParent = false;
      switch (parent.getKind())
      {
        // If-then-else operator - any two unconstrained children makes the
        // parent unconstrained
        case kind::ITE:
        {
          Assert(parent[0] == current || parent[1] == current
                 || parent[2] == current);
          bool uCond =
              parent[0] == current
              || d_unconstrained.find(parent[0]) != d_unconstrained.end();
          bool uThen =
              parent[1] == current
              || d_unconstrained.find(parent[1]) != d_unconstrained.end();
          bool uElse =
              parent[2] == current
              || d_unconstrained.find(parent[2]) != d_unconstrained.end();
          if ((uCond && uThen) || (uCond && uElse) || (uThen && uElse))
          {
            if (d_unconstrained.find(parent) == d_unconstrained.end()
                && !d_substitutions.hasSubstitution(parent))
            {
              ++d_numUnconstrainedElim;
              if (uThen)
              {
                if (parent[1] != current)
                {
                  if (parent[1].isVar())
                  {
                    currentSub = parent[1];
                  }
                  else
                  {
                    Assert(d_substitutions.hasSubstitution(parent[1]));
                    currentSub = d_substitutions.apply(parent[1]);
                  }
                }
                else if (currentSub.isNull())
                {
                  currentSub = current;
                }
              }
              else if (parent[2] != current)
              {
                if (parent[2].isVar())
                {
                  currentSub = parent[2];
                }
                else
                {
                  Assert(d_substitutions.hasSubstitution(parent[2]));
                  currentSub = d_substitutions.apply(parent[2]);
                }
              }
              else if (currentSub.isNull())
              {
                currentSub = current;
              }
              current = parent;
            }
            else
            {
              currentSub = Node();
            }
          }
          else if (uCond)
          {
            Cardinality card = parent.getType().getCardinality();
            if (card.isFinite() && !card.isLargeFinite()
                && card.getFiniteCardinality() == 2)
            {
              // Special case: condition is unconstrained, then and else are
              // different, and total cardinality of the type is 2, then the
              // result is unconstrained
              Node test = Rewriter::rewrite(parent[1].eqNode(parent[2]));
              if (test == nm->mkConst<bool>(false))
              {
                ++d_numUnconstrainedElim;
                if (currentSub.isNull())
                {
                  currentSub = current;
                }
                currentSub = newUnconstrainedVar(parent.getType(), currentSub);
                current = parent;
              }
            }
          }
          break;
        }

        // Comparisons that return a different type - assuming domains are
        // larger than 1, any unconstrained child makes parent unconstrained as
        // well
        case kind::EQUAL:
          if (parent[0].getType() != parent[1].getType())
          {
            TNode other = (parent[0] == current) ? parent[1] : parent[0];
            if (current.getType().isSubtypeOf(other.getType()))
            {
              break;
            }
          }
          if (parent[0].getType().getCardinality().isOne())
          {
            break;
          }
          if (parent[0].getType().isDatatype())
          {
            TypeNode tn = parent[0].getType();
            const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
            if (dt.isRecursiveSingleton(tn.toType()))
            {
              // domain size may be 1
              break;
            }
          }
          if (parent[0].getType().isBoolean())
          {
            checkParent = true;
            break;
          }
          CVC4_FALLTHROUGH;
        case kind::BITVECTOR_COMP:
        case kind::LT:
        case kind::LEQ:
        case kind::GT:
        case kind::GEQ:
        {
          if (d_unconstrained.find(parent) == d_unconstrained.end()
              && !d_substitutions.hasSubstitution(parent))
          {
            ++d_numUnconstrainedElim;
            Assert(parent[0] != parent[1]
                   && (parent[0] == current || parent[1] == current));
            if (currentSub.isNull())
            {
              currentSub = current;
            }
            currentSub = newUnconstrainedVar(parent.getType(), currentSub);
            current = parent;
          }
          else
          {
            currentSub = Node();
          }
          break;
        }

        // Unary operators that propagate unconstrainedness
        case kind::NOT:
        case kind::BITVECTOR_NOT:
        case kind::BITVECTOR_NEG:
        case kind::UMINUS:
          ++d_numUnconstrainedElim;
          Assert(parent[0] == current);
          if (currentSub.isNull())
          {
            currentSub = current;
          }
          current = parent;
          break;

        // Unary operators that propagate unconstrainedness and return a
        // different type
        case kind::BITVECTOR_EXTRACT:
          ++d_numUnconstrainedElim;
          Assert(parent[0] == current);
          if (currentSub.isNull())
          {
            currentSub = current;
          }
          currentSub = newUnconstrainedVar(parent.getType(), currentSub);
          current = parent;
          break;

        // Operators returning same type requiring all children to be
        // unconstrained
        case kind::AND:
        case kind::OR:
        case kind::IMPLIES:
        case kind::BITVECTOR_AND:
        case kind::BITVECTOR_OR:
        case kind::BITVECTOR_NAND:
        case kind::BITVECTOR_NOR:
        {
          bool allUnconstrained = true;
          for (TNode child : parent)
          {
            if (d_unconstrained.find(child) == d_unconstrained.end())
            {
              allUnconstrained = false;
              break;
            }
          }
          if (allUnconstrained)
          {
            checkParent = true;
          }
        }
        break;

        // Require all children to be unconstrained and different
        case kind::BITVECTOR_SHL:
        case kind::BITVECTOR_LSHR:
        case kind::BITVECTOR_ASHR:
        case kind::BITVECTOR_UDIV_TOTAL:
        case kind::BITVECTOR_UREM_TOTAL:
        case kind::BITVECTOR_SDIV:
        case kind::BITVECTOR_SREM:
        case kind::BITVECTOR_SMOD:
        {
          bool allUnconstrained = true;
          bool allDifferent = true;
          for (TNode::iterator child_it = parent.begin();
               child_it != parent.end();
               ++child_it)
          {
            if (d_unconstrained.find(*child_it) == d_unconstrained.end())
            {
              allUnconstrained = false;
              break;
            }
            for (TNode::iterator child_it2 = child_it + 1;
                 child_it2 != parent.end();
                 ++child_it2)
            {
              if (*child_it == *child_it2)
              {
                allDifferent = false;
                break;
              }
            }
          }
          if (allUnconstrained && allDifferent)
          {
            checkParent = true;
          }
          break;
        }

        // Requires all children to be unconstrained and different, and returns
        // a different type
        case kind::BITVECTOR_CONCAT:
        {
          bool allUnconstrained = true;
          bool allDifferent = true;
          for (TNode::iterator child_it = parent.begin();
               child_it != parent.end();
               ++child_it)
          {
            if (d_unconstrained.find(*child_it) == d_unconstrained.end())
            {
              allUnconstrained = false;
              break;
            }
            for (TNode::iterator child_it2 = child_it + 1;
                 child_it2 != parent.end();
                 ++child_it2)
            {
              if (*child_it == *child_it2)
              {
                allDifferent = false;
                break;
              }
            }
          }
          if (allUnconstrained && allDifferent)
          {
            if (d_unconstrained.find(parent) == d_unconstrained.end()
                && !d_substitutions.hasSubstitution(parent))
            {
              ++d_numUnconstrainedElim;
              if (currentSub.isNull())
              {
                currentSub = current;
              }
              currentSub = newUnconstrainedVar(parent.getType(), currentSub);
              current = parent;
            }
            else
            {
              currentSub = Node();
            }
          }
        }
        break;

        // N-ary operators returning same type requiring at least one child to
        // be unconstrained
        case kind::PLUS:
        case kind::MINUS:
          if (current.getType().isInteger() && !parent.getType().isInteger())
          {
            break;
          }
          CVC4_FALLTHROUGH;
        case kind::XOR:
        case kind::BITVECTOR_XOR:
        case kind::BITVECTOR_XNOR:
        case kind::BITVECTOR_PLUS:
        case kind::BITVECTOR_SUB: checkParent = true; break;

        // Multiplication/division: must be non-integer and other operand must
        // be non-zero
        case kind::MULT:
        case kind::DIVISION:
        {
          Assert(parent.getNumChildren() == 2);
          TNode other;
          if (parent[0] == current)
          {
            other = parent[1];
          }
          else
          {
            Assert(parent[1] == current);
            other = parent[0];
          }
          if (d_unconstrained.find(other) != d_unconstrained.end())
          {
            if (d_unconstrained.find(parent) == d_unconstrained.end()
                && !d_substitutions.hasSubstitution(parent))
            {
              if (current.getType().isInteger() && other.getType().isInteger())
              {
                Assert(parent.getKind() == kind::DIVISION
                       || parent.getType().isInteger());
                if (parent.getKind() == kind::DIVISION)
                {
                  break;
                }
              }
              ++d_numUnconstrainedElim;
              if (currentSub.isNull())
              {
                currentSub = current;
              }
              current = parent;
            }
            else
            {
              currentSub = Node();
            }
          }
          else
          {
            // if only the denominator of a division is unconstrained, can't
            // set it to 0 so the result is not unconstrained
            if (parent.getKind() == kind::DIVISION && current == parent[1])
            {
              break;
            }
            // if we are an integer, the only way we are unconstrained is if
            // we are a MULT by -1
            if (current.getType().isInteger())
            {
              // div/mult by 1 should have been simplified
              Assert(other != nm->mkConst<Rational>(1));
              // div by -1 should have been simplified
              if (other != nm->mkConst<Rational>(-1))
              {
                break;
              }
              else
              {
                Assert(parent.getKind() == kind::MULT);
                Assert(parent.getType().isInteger());
              }
            }
            else
            {
              // TODO(#2377): could build ITE here
              Node test = other.eqNode(nm->mkConst<Rational>(0));
              if (Rewriter::rewrite(test) != nm->mkConst<bool>(false))
              {
                break;
              }
            }
            ++d_numUnconstrainedElim;
            if (currentSub.isNull())
            {
              currentSub = current;
            }
            current = parent;
          }
          break;
        }

        // Bitvector MULT - current must only appear once in the children:
        // all other children must be unconstrained or odd
        case kind::BITVECTOR_MULT:
        {
          bool found = false;
          bool done = false;

          for (TNode child : parent)
          {
            if (child == current)
            {
              if (found)
              {
                done = true;
                break;
              }
              found = true;
              continue;
            }
            else if (d_unconstrained.find(child) == d_unconstrained.end())
            {
              Node extractOp =
                  nm->mkConst<BitVectorExtract>(BitVectorExtract(0, 0));
              vector<Node> children;
              children.push_back(child);
              Node test = nm->mkNode(extractOp, children);
              BitVector one(1, unsigned(1));
              test = test.eqNode(nm->mkConst<BitVector>(one));
              if (Rewriter::rewrite(test) != nm->mkConst<bool>(true))
              {
                done = true;
                break;
              }
            }
          }
          if (done)
          {
            break;
          }
          checkParent = true;
          break;
        }

        // Uninterpreted function - if domain is infinite, no quantifiers are
        // used, and any child is unconstrained, result is unconstrained
        case kind::APPLY_UF:
          if (d_logicInfo.isQuantified()
              || !current.getType().getCardinality().isInfinite())
          {
            break;
          }
          if (d_unconstrained.find(parent) == d_unconstrained.end()
              && !d_substitutions.hasSubstitution(parent))
          {
            ++d_numUnconstrainedElim;
            if (currentSub.isNull())
            {
              currentSub = current;
            }
            // always introduce a new variable; it is unsound to try to reuse
            // currentSub as the variable, see issue #4469.
            currentSub = newUnconstrainedVar(parent.getType(), currentSub);
            current = parent;
          }
          else
          {
            currentSub = Node();
          }
          break;

        // Array select - if array is unconstrained, so is result
        case kind::SELECT:
          if (parent[0] == current)
          {
            ++d_numUnconstrainedElim;
            Assert(current.getType().isArray());
            if (currentSub.isNull())
            {
              currentSub = current;
            }
            currentSub = newUnconstrainedVar(
                current.getType().getArrayConstituentType(), currentSub);
            current = parent;
          }
          break;

        // Array store - if both store and value are unconstrained, so is
        // resulting store
        case kind::STORE:
          if (((parent[0] == current
                && d_unconstrained.find(parent[2]) != d_unconstrained.end())
               || (parent[2] == current
                   && d_unconstrained.find(parent[0])
                          != d_unconstrained.end())))
          {
            if (d_unconstrained.find(parent) == d_unconstrained.end()
                && !d_substitutions.hasSubstitution(parent))
            {
              ++d_numUnconstrainedElim;
              if (parent[0] != current)
              {
                if (parent[0].isVar())
                {
                  currentSub = parent[0];
                }
                else
                {
                  Assert(d_substitutions.hasSubstitution(parent[0]));
                  currentSub = d_substitutions.apply(parent[0]);
                }
              }
              else if (currentSub.isNull())
              {
                currentSub = current;
              }
              current = parent;
            }
            else
            {
              currentSub = Node();
            }
          }
          break;

        // Bit-vector comparisons: replace with new Boolean variable, but have
        // to also conjoin with a side condition as there is always one case
        // when the comparison is forced to be false
        case kind::BITVECTOR_ULT:
        case kind::BITVECTOR_UGE:
        case kind::BITVECTOR_UGT:
        case kind::BITVECTOR_ULE:
        case kind::BITVECTOR_SLT:
        case kind::BITVECTOR_SGE:
        case kind::BITVECTOR_SGT:
        case kind::BITVECTOR_SLE:
        {
          // Tuples over (signed, swap, strict).
          switch (parent.getKind())
          {
            case kind::BITVECTOR_UGE: break;
            case kind::BITVECTOR_ULT: strict = true; break;
            case kind::BITVECTOR_ULE: swap = true; break;
            case kind::BITVECTOR_UGT:
              swap = true;
              strict = true;
              break;
            case kind::BITVECTOR_SGE: isSigned = true; break;
            case kind::BITVECTOR_SLT:
              isSigned = true;
              strict = true;
              break;
            case kind::BITVECTOR_SLE:
              isSigned = true;
              swap = true;
              break;
            case kind::BITVECTOR_SGT:
              isSigned = true;
              swap = true;
              strict = true;
              break;
            default: Unreachable();
          }
          TNode other;
          bool left = false;
          if (parent[0] == current)
          {
            other = parent[1];
            left = true;
          }
          else
          {
            Assert(parent[1] == current);
            other = parent[0];
          }
          if (d_unconstrained.find(other) != d_unconstrained.end())
          {
            if (d_unconstrained.find(parent) == d_unconstrained.end()
                && !d_substitutions.hasSubstitution(parent))
            {
              ++d_numUnconstrainedElim;
              if (currentSub.isNull())
              {
                currentSub = current;
              }
              currentSub = newUnconstrainedVar(parent.getType(), currentSub);
              current = parent;
            }
            else
            {
              currentSub = Node();
            }
          }
          else
          {
            unsigned size = current.getType().getBitVectorSize();
            BitVector bv =
                isSigned ? BitVector(size, Integer(1).multiplyByPow2(size - 1))
                         : BitVector(size, unsigned(0));
            if (swap == left)
            {
              bv = ~bv;
            }
            if (currentSub.isNull())
            {
              currentSub = current;
            }
            currentSub = newUnconstrainedVar(parent.getType(), currentSub);
            current = parent;
            Node test =
                Rewriter::rewrite(other.eqNode(nm->mkConst<BitVector>(bv)));
            if (test == nm->mkConst<bool>(false))
            {
              break;
            }
            currentSub = strict ? currentSub.andNode(test.notNode())
                                : currentSub.orNode(test);
            // Delay adding this substitution - see comment at end of function
            delayQueueLeft.push_back(current);
            delayQueueRight.push_back(currentSub);
            currentSub = Node();
            parent = TNode();
          }
          break;
        }

        // Do nothing
        case kind::BITVECTOR_SIGN_EXTEND:
        case kind::BITVECTOR_ZERO_EXTEND:
        case kind::BITVECTOR_REPEAT:
        case kind::BITVECTOR_ROTATE_LEFT:
        case kind::BITVECTOR_ROTATE_RIGHT:

        default: break;
      }
      if (checkParent)
      {
        // run for various cases from above
        if (d_unconstrained.find(parent) == d_unconstrained.end()
            && !d_substitutions.hasSubstitution(parent))
        {
          ++d_numUnconstrainedElim;
          if (currentSub.isNull())
          {
            currentSub = current;
          }
          current = parent;
        }
        else
        {
          currentSub = Node();
        }
      }
      if (current == parent && d_visited[parent] == 1)
      {
        d_unconstrained.insert(parent);
        continue;
      }
    }
    if (!currentSub.isNull())
    {
      Trace("unc-simp")
          << "UnconstrainedSimplifier::processUnconstrained: introduce "
          << currentSub << " for " << current << ", parent " << parent
          << std::endl;
      Assert(currentSub.isVar());
      d_substitutions.addSubstitution(current, currentSub, false);
    }
    if (workList.empty())
    {
      break;
    }
    current = workList.back();
    currentSub = Node();
    workList.pop_back();
  }
  TNode left;
  Node right;
  // All substitutions except those arising from bitvector comparisons are
  // substitutions t -> x where x is a variable.  This allows us to build the
  // substitution very quickly (never invalidating the substitution cache).
  // Bitvector comparisons are more complicated and may require
  // back-substitution and cache-invalidation.  So we do these last.
  while (!delayQueueLeft.empty())
  {
    left = delayQueueLeft.back();
    if (!d_substitutions.hasSubstitution(left))
    {
      right = d_substitutions.apply(delayQueueRight.back());
      d_substitutions.addSubstitution(delayQueueLeft.back(), right);
    }
    delayQueueLeft.pop_back();
    delayQueueRight.pop_back();
  }
}

PreprocessingPassResult UnconstrainedSimplifier::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(ResourceManager::Resource::PreprocessStep);

  std::vector<Node>& assertions = assertionsToPreprocess->ref();

  d_context->push();

  for (const Node& assertion : assertions)
  {
    visitAll(assertion);
  }

  if (!d_unconstrained.empty())
  {
    processUnconstrained();
    //    d_substitutions.print(Message.getStream());
    for (Node& assertion : assertions)
    {
      assertion = Rewriter::rewrite(d_substitutions.apply(assertion));
    }
  }

  // to clear substitutions map
  d_context->pop();

  d_visited.clear();
  d_visitedOnce.clear();
  d_unconstrained.clear();

  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
