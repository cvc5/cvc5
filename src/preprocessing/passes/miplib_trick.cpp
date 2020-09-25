/*********************                                                        */
/*! \file miplib_trick.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The MIPLIB trick preprocessing pass
 **
 **/

#include "preprocessing/passes/miplib_trick.h"

#include <vector>

#include "expr/node_self_iterator.h"
#include "options/arith_options.h"
#include "smt/smt_statistics_registry.h"
#include "smt_util/boolean_simplification.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

namespace {

/**
 * Remove conjuncts in toRemove from conjunction n. Return # of removed
 * conjuncts.
 */
size_t removeFromConjunction(Node& n,
                             const std::unordered_set<unsigned long>& toRemove)
{
  Assert(n.getKind() == kind::AND);
  Node trueNode = NodeManager::currentNM()->mkConst(true);
  size_t removals = 0;
  for (Node::iterator j = n.begin(); j != n.end(); ++j)
  {
    size_t subremovals = 0;
    Node sub = *j;
    if (toRemove.find(sub.getId()) != toRemove.end()
        || (sub.getKind() == kind::AND
            && (subremovals = removeFromConjunction(sub, toRemove)) > 0))
    {
      NodeBuilder<> b(kind::AND);
      b.append(n.begin(), j);
      if (subremovals > 0)
      {
        removals += subremovals;
        b << sub;
      }
      else
      {
        ++removals;
      }
      for (++j; j != n.end(); ++j)
      {
        if (toRemove.find((*j).getId()) != toRemove.end())
        {
          ++removals;
        }
        else if ((*j).getKind() == kind::AND)
        {
          sub = *j;
          if ((subremovals = removeFromConjunction(sub, toRemove)) > 0)
          {
            removals += subremovals;
            b << sub;
          }
          else
          {
            b << *j;
          }
        }
        else
        {
          b << *j;
        }
      }
      if (b.getNumChildren() == 0)
      {
        n = trueNode;
        b.clear();
      }
      else if (b.getNumChildren() == 1)
      {
        n = b[0];
        b.clear();
      }
      else
      {
        n = b;
      }
      n = Rewriter::rewrite(n);
      return removals;
    }
  }

  Assert(removals == 0);
  return 0;
}

/**
 * Trace nodes back to their assertions using CircuitPropagator's
 * BackEdgesMap.
 */
void traceBackToAssertions(booleans::CircuitPropagator* propagator,
                           const std::vector<Node>& nodes,
                           std::vector<TNode>& assertions)
{
  const booleans::CircuitPropagator::BackEdgesMap& backEdges =
      propagator->getBackEdges();
  for (vector<Node>::const_iterator i = nodes.begin(); i != nodes.end(); ++i)
  {
    booleans::CircuitPropagator::BackEdgesMap::const_iterator j =
        backEdges.find(*i);
    // term must appear in map, otherwise how did we get here?!
    Assert(j != backEdges.end());
    // if term maps to empty, that means it's a top-level assertion
    if (!(*j).second.empty())
    {
      traceBackToAssertions(propagator, (*j).second, assertions);
    }
    else
    {
      assertions.push_back(*i);
    }
  }
}

}  // namespace

MipLibTrick::MipLibTrick(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "miplib-trick")
{
  if (!options::incrementalSolving())
  {
    NodeManager::currentNM()->subscribeEvents(this);
  }
}

MipLibTrick::~MipLibTrick()
{
  if (!options::incrementalSolving())
  {
    NodeManager::currentNM()->unsubscribeEvents(this);
  }
}

void MipLibTrick::nmNotifyNewVar(TNode n, uint32_t flags)
{
  if (n.getType().isBoolean())
  {
    d_boolVars.push_back(n);
  }
}

void MipLibTrick::nmNotifyNewSkolem(TNode n,
                                    const std::string& comment,
                                    uint32_t flags)
{
  if (n.getType().isBoolean())
  {
    d_boolVars.push_back(n);
  }
}

PreprocessingPassResult MipLibTrick::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Assert(assertionsToPreprocess->getRealAssertionsEnd()
         == assertionsToPreprocess->size());
  Assert(!options::incrementalSolving());

  context::Context fakeContext;
  TheoryEngine* te = d_preprocContext->getTheoryEngine();
  booleans::CircuitPropagator* propagator =
      d_preprocContext->getCircuitPropagator();
  const booleans::CircuitPropagator::BackEdgesMap& backEdges =
      propagator->getBackEdges();
  unordered_set<unsigned long> removeAssertions;
  SubstitutionMap& top_level_substs =
      d_preprocContext->getTopLevelSubstitutions();

  NodeManager* nm = NodeManager::currentNM();
  Node zero = nm->mkConst(Rational(0)), one = nm->mkConst(Rational(1));
  Node trueNode = nm->mkConst(true);

  unordered_map<TNode, Node, TNodeHashFunction> intVars;
  for (TNode v0 : d_boolVars)
  {
    if (propagator->isAssigned(v0))
    {
      Debug("miplib") << "ineligible: " << v0 << " because assigned "
                      << propagator->getAssignment(v0) << endl;
      continue;
    }

    vector<TNode> assertions;
    booleans::CircuitPropagator::BackEdgesMap::const_iterator j0 =
        backEdges.find(v0);
    // if not in back edges map, the bool var is unconstrained, showing up in no
    // assertions. if maps to an empty vector, that means the bool var was
    // asserted itself.
    if (j0 != backEdges.end())
    {
      if (!(*j0).second.empty())
      {
        traceBackToAssertions(propagator, (*j0).second, assertions);
      }
      else
      {
        assertions.push_back(v0);
      }
    }
    Debug("miplib") << "for " << v0 << endl;
    bool eligible = true;
    map<pair<Node, Node>, uint64_t> marks;
    map<pair<Node, Node>, vector<Rational> > coef;
    map<pair<Node, Node>, vector<Rational> > checks;
    map<pair<Node, Node>, vector<TNode> > asserts;
    for (vector<TNode>::const_iterator j1 = assertions.begin();
         j1 != assertions.end();
         ++j1)
    {
      Debug("miplib") << "  found: " << *j1 << endl;
      if ((*j1).getKind() != kind::IMPLIES)
      {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (not =>)" << endl;
        break;
      }
      Node conj = BooleanSimplification::simplify((*j1)[0]);
      if (conj.getKind() == kind::AND && conj.getNumChildren() > 6)
      {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (N-ary /\\ too big)" << endl;
        break;
      }
      if (conj.getKind() != kind::AND && !conj.isVar()
          && !(conj.getKind() == kind::NOT && conj[0].isVar()))
      {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (not /\\ or literal)" << endl;
        break;
      }
      if ((*j1)[1].getKind() != kind::EQUAL
          || !(((*j1)[1][0].isVar()
                && (*j1)[1][1].getKind() == kind::CONST_RATIONAL)
               || ((*j1)[1][0].getKind() == kind::CONST_RATIONAL
                   && (*j1)[1][1].isVar())))
      {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (=> (and X X) X)" << endl;
        break;
      }
      if (conj.getKind() == kind::AND)
      {
        vector<Node> posv;
        bool found_x = false;
        map<TNode, bool> neg;
        for (Node::iterator ii = conj.begin(); ii != conj.end(); ++ii)
        {
          if ((*ii).isVar())
          {
            posv.push_back(*ii);
            neg[*ii] = false;
            found_x = found_x || v0 == *ii;
          }
          else if ((*ii).getKind() == kind::NOT && (*ii)[0].isVar())
          {
            posv.push_back((*ii)[0]);
            neg[(*ii)[0]] = true;
            found_x = found_x || v0 == (*ii)[0];
          }
          else
          {
            eligible = false;
            Debug("miplib")
                << "  -- INELIGIBLE -- (non-var: " << *ii << ")" << endl;
            break;
          }
          if (propagator->isAssigned(posv.back()))
          {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (" << posv.back()
                            << " asserted)" << endl;
            break;
          }
        }
        if (!eligible)
        {
          break;
        }
        if (!found_x)
        {
          eligible = false;
          Debug("miplib") << "  --INELIGIBLE -- (couldn't find " << v0
                          << " in conjunction)" << endl;
          break;
        }
        sort(posv.begin(), posv.end());
        const Node pos = NodeManager::currentNM()->mkNode(kind::AND, posv);
        const TNode var = ((*j1)[1][0].getKind() == kind::CONST_RATIONAL)
                              ? (*j1)[1][1]
                              : (*j1)[1][0];
        const pair<Node, Node> pos_var(pos, var);
        const Rational& constant =
            ((*j1)[1][0].getKind() == kind::CONST_RATIONAL)
                ? (*j1)[1][0].getConst<Rational>()
                : (*j1)[1][1].getConst<Rational>();
        uint64_t mark = 0;
        unsigned countneg = 0, thepos = 0;
        for (unsigned ii = 0; ii < pos.getNumChildren(); ++ii)
        {
          if (neg[pos[ii]])
          {
            ++countneg;
          }
          else
          {
            thepos = ii;
            mark |= (0x1 << ii);
          }
        }
        if ((marks[pos_var] & (1lu << mark)) != 0)
        {
          eligible = false;
          Debug("miplib") << "  -- INELIGIBLE -- (remarked)" << endl;
          break;
        }
        Debug("miplib") << "mark is " << mark << " -- " << (1lu << mark)
                        << endl;
        marks[pos_var] |= (1lu << mark);
        Debug("miplib") << "marks[" << pos << "," << var << "] now "
                        << marks[pos_var] << endl;
        if (countneg == pos.getNumChildren())
        {
          if (constant != 0)
          {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (nonzero constant)" << endl;
            break;
          }
        }
        else if (countneg == pos.getNumChildren() - 1)
        {
          Assert(coef[pos_var].size() <= 6 && thepos < 6);
          if (coef[pos_var].size() <= thepos)
          {
            coef[pos_var].resize(thepos + 1);
          }
          coef[pos_var][thepos] = constant;
        }
        else
        {
          if (checks[pos_var].size() <= mark)
          {
            checks[pos_var].resize(mark + 1);
          }
          checks[pos_var][mark] = constant;
        }
        asserts[pos_var].push_back(*j1);
      }
      else
      {
        TNode x = conj;
        if (x != v0 && x != (v0).notNode())
        {
          eligible = false;
          Debug("miplib")
              << "  -- INELIGIBLE -- (x not present where I expect it)" << endl;
          break;
        }
        const bool xneg = (x.getKind() == kind::NOT);
        x = xneg ? x[0] : x;
        Debug("miplib") << "  x:" << x << "  " << xneg << endl;
        const TNode var = ((*j1)[1][0].getKind() == kind::CONST_RATIONAL)
                              ? (*j1)[1][1]
                              : (*j1)[1][0];
        const pair<Node, Node> x_var(x, var);
        const Rational& constant =
            ((*j1)[1][0].getKind() == kind::CONST_RATIONAL)
                ? (*j1)[1][0].getConst<Rational>()
                : (*j1)[1][1].getConst<Rational>();
        unsigned mark = (xneg ? 0 : 1);
        if ((marks[x_var] & (1u << mark)) != 0)
        {
          eligible = false;
          Debug("miplib") << "  -- INELIGIBLE -- (remarked)" << endl;
          break;
        }
        marks[x_var] |= (1u << mark);
        if (xneg)
        {
          if (constant != 0)
          {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (nonzero constant)" << endl;
            break;
          }
        }
        else
        {
          Assert(coef[x_var].size() <= 6);
          coef[x_var].resize(6);
          coef[x_var][0] = constant;
        }
        asserts[x_var].push_back(*j1);
      }
    }
    if (eligible)
    {
      for (map<pair<Node, Node>, uint64_t>::const_iterator j = marks.begin();
           j != marks.end();
           ++j)
      {
        const TNode pos = (*j).first.first;
        const TNode var = (*j).first.second;
        const pair<Node, Node>& pos_var = (*j).first;
        const uint64_t mark = (*j).second;
        const unsigned numVars =
            pos.getKind() == kind::AND ? pos.getNumChildren() : 1;
        uint64_t expected = (uint64_t(1) << (1 << numVars)) - 1;
        expected = (expected == 0) ? -1 : expected;  // fix for overflow
        Debug("miplib") << "[" << pos << "] => " << hex << mark << " expect "
                        << expected << dec << endl;
        Assert(pos.getKind() == kind::AND || pos.isVar());
        if (mark != expected)
        {
          Debug("miplib") << "  -- INELIGIBLE " << pos
                          << " -- (insufficiently marked, got " << mark
                          << " for " << numVars << " vars, expected "
                          << expected << endl;
        }
        else
        {
          if (mark != 3)
          {  // exclude single-var case; nothing to check there
            uint64_t sz = (uint64_t(1) << checks[pos_var].size()) - 1;
            sz = (sz == 0) ? -1 : sz;  // fix for overflow
            Assert(sz == mark) << "expected size " << sz << " == mark " << mark;
            for (size_t k = 0; k < checks[pos_var].size(); ++k)
            {
              if ((k & (k - 1)) != 0)
              {
                Rational sum = 0;
                Debug("miplib") << k << " => " << checks[pos_var][k] << endl;
                for (size_t v1 = 1, kk = k; kk != 0; ++v1, kk >>= 1)
                {
                  if ((kk & 0x1) == 1)
                  {
                    Assert(pos.getKind() == kind::AND);
                    Debug("miplib")
                        << "var " << v1 << " : " << pos[v1 - 1]
                        << " coef:" << coef[pos_var][v1 - 1] << endl;
                    sum += coef[pos_var][v1 - 1];
                  }
                }
                Debug("miplib") << "checkSum is " << sum << " input says "
                                << checks[pos_var][k] << endl;
                if (sum != checks[pos_var][k])
                {
                  eligible = false;
                  Debug("miplib") << "  -- INELIGIBLE " << pos
                                  << " -- (nonlinear combination)" << endl;
                  break;
                }
              }
              else
              {
                Assert(checks[pos_var][k] == 0)
                    << "checks[(" << pos << "," << var << ")][" << k
                    << "] should be 0, but it's "
                    << checks[pos_var]
                             [k];  // we never set for single-positive-var
              }
            }
          }
          if (!eligible)
          {
            eligible = true;  // next is still eligible
            continue;
          }

          Debug("miplib") << "  -- ELIGIBLE " << v0 << " , " << pos << " --"
                          << endl;
          vector<Node> newVars;
          expr::NodeSelfIterator ii, iiend;
          if (pos.getKind() == kind::AND)
          {
            ii = pos.begin();
            iiend = pos.end();
          }
          else
          {
            ii = expr::NodeSelfIterator::self(pos);
            iiend = expr::NodeSelfIterator::selfEnd(pos);
          }
          for (; ii != iiend; ++ii)
          {
            Node& varRef = intVars[*ii];
            if (varRef.isNull())
            {
              stringstream ss;
              ss << "mipvar_" << *ii;
              Node newVar = nm->mkSkolem(
                  ss.str(),
                  nm->integerType(),
                  "a variable introduced due to scrubbing a miplib encoding",
                  NodeManager::SKOLEM_EXACT_NAME);
              Node geq = Rewriter::rewrite(nm->mkNode(kind::GEQ, newVar, zero));
              Node leq = Rewriter::rewrite(nm->mkNode(kind::LEQ, newVar, one));

              Node n = Rewriter::rewrite(geq.andNode(leq));
              assertionsToPreprocess->push_back(n);
              if (options::unsatCores())
              {
                ProofManager::currentPM()->addDependence(n, Node::null());
              }
              SubstitutionMap nullMap(&fakeContext);
              Theory::PPAssertStatus status CVC4_UNUSED;  // just for assertions
              status = te->solve(geq, nullMap);
              Assert(status == Theory::PP_ASSERT_STATUS_UNSOLVED)
                  << "unexpected solution from arith's ppAssert()";
              Assert(nullMap.empty())
                  << "unexpected substitution from arith's ppAssert()";
              status = te->solve(leq, nullMap);
              Assert(status == Theory::PP_ASSERT_STATUS_UNSOLVED)
                  << "unexpected solution from arith's ppAssert()";
              Assert(nullMap.empty())
                  << "unexpected substitution from arith's ppAssert()";
              te->getModel()->addSubstitution(*ii, newVar.eqNode(one));
              newVars.push_back(newVar);
              varRef = newVar;
            }
            else
            {
              newVars.push_back(varRef);
            }
            d_preprocContext->enableIntegers();
          }
          Node sum;
          if (pos.getKind() == kind::AND)
          {
            NodeBuilder<> sumb(kind::PLUS);
            for (size_t jj = 0; jj < pos.getNumChildren(); ++jj)
            {
              sumb << nm->mkNode(
                  kind::MULT, nm->mkConst(coef[pos_var][jj]), newVars[jj]);
            }
            sum = sumb;
          }
          else
          {
            sum = nm->mkNode(
                kind::MULT, nm->mkConst(coef[pos_var][0]), newVars[0]);
          }
          Debug("miplib") << "vars[] " << var << endl
                          << "    eq " << Rewriter::rewrite(sum) << endl;
          Node newAssertion = var.eqNode(Rewriter::rewrite(sum));
          if (top_level_substs.hasSubstitution(newAssertion[0]))
          {
            // Warning() << "RE-SUBSTITUTION " << newAssertion[0] << endl;
            // Warning() << "REPLACE         " << newAssertion[1] << endl;
            // Warning() << "ORIG            " <<
            // top_level_substs.getSubstitution(newAssertion[0]) << endl;
            Assert(top_level_substs.getSubstitution(newAssertion[0])
                   == newAssertion[1]);
          }
          else if (pos.getNumChildren() <= options::arithMLTrickSubstitutions())
          {
            top_level_substs.addSubstitution(newAssertion[0], newAssertion[1]);
            Debug("miplib") << "addSubs: " << newAssertion[0] << " to "
                            << newAssertion[1] << endl;
          }
          else
          {
            Debug("miplib")
                << "skipSubs: " << newAssertion[0] << " to " << newAssertion[1]
                << " (threshold is " << options::arithMLTrickSubstitutions()
                << ")" << endl;
          }
          newAssertion = Rewriter::rewrite(newAssertion);
          Debug("miplib") << "  " << newAssertion << endl;

          assertionsToPreprocess->push_back(newAssertion);
          if (options::unsatCores())
          {
            ProofManager::currentPM()->addDependence(newAssertion,
                                                     Node::null());
          }
          Debug("miplib") << "  assertions to remove: " << endl;
          for (vector<TNode>::const_iterator k = asserts[pos_var].begin(),
                                             k_end = asserts[pos_var].end();
               k != k_end;
               ++k)
          {
            Debug("miplib") << "    " << *k << endl;
            removeAssertions.insert((*k).getId());
          }
        }
      }
    }
  }
  if (!removeAssertions.empty())
  {
    Debug("miplib") << " scrubbing miplib encoding..." << endl;
    for (size_t i = 0, size = assertionsToPreprocess->getRealAssertionsEnd();
         i < size;
         ++i)
    {
      Node assertion = (*assertionsToPreprocess)[i];
      if (removeAssertions.find(assertion.getId()) != removeAssertions.end())
      {
        Debug("miplib") << " - removing " << assertion << endl;
        assertionsToPreprocess->replace(i, trueNode);
        ++d_statistics.d_numMiplibAssertionsRemoved;
      }
      else if (assertion.getKind() == kind::AND)
      {
        size_t removals = removeFromConjunction(assertion, removeAssertions);
        if (removals > 0)
        {
          Debug("miplib") << " - reduced " << assertion << endl;
          Debug("miplib") << " -      by " << removals << " conjuncts" << endl;
          d_statistics.d_numMiplibAssertionsRemoved += removals;
        }
      }
      Debug("miplib") << "had: " << assertion[i] << endl;
      assertionsToPreprocess->replace(
          i, Rewriter::rewrite(top_level_substs.apply(assertion)));
      Debug("miplib") << "now: " << assertion << endl;
    }
  }
  else
  {
    Debug("miplib") << " miplib pass found nothing." << endl;
  }
  assertionsToPreprocess->updateRealAssertionsEnd();
  return PreprocessingPassResult::NO_CONFLICT;
}

MipLibTrick::Statistics::Statistics()
    : d_numMiplibAssertionsRemoved(
          "preprocessing::passes::MipLibTrick::numMiplibAssertionsRemoved", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numMiplibAssertionsRemoved);
}

MipLibTrick::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_numMiplibAssertionsRemoved);
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
