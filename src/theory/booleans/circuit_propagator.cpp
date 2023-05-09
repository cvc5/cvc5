/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Morgan Deters, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A non-clausal circuit propagator for Boolean simplification.
 */

#include "theory/booleans/circuit_propagator.h"

#include <algorithm>
#include <stack>
#include <vector>

#include "expr/node_algorithm.h"
#include "proof/eager_proof_generator.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "theory/booleans/proof_circuit_propagator.h"
#include "theory/theory.h"
#include "util/hash.h"
#include "util/utility.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace booleans {

CircuitPropagator::CircuitPropagator(Env& env, bool enableForward, bool enableBackward)
    : EnvObj(env),
      d_context(),
      d_propagationQueue(),
      d_propagationQueueClearer(&d_context, d_propagationQueue),
      d_conflict(&d_context, TrustNode()),
      d_learnedLiterals(),
      d_learnedLiteralClearer(&d_context, d_learnedLiterals),
      d_backEdges(),
      d_backEdgesClearer(&d_context, d_backEdges),
      d_seen(&d_context),
      d_state(&d_context),
      d_forwardPropagation(enableForward),
      d_backwardPropagation(enableBackward),
      d_needsFinish(false),
      d_epg(nullptr),
      d_proofInternal(nullptr),
      d_proofExternal(nullptr)
{
}

void CircuitPropagator::initialize()
{
  if (d_needsFinish)
  {
    d_context.pop();
  }
  d_context.push();
  d_needsFinish = true;
}

void CircuitPropagator::assertTrue(TNode assertion)
{
  Trace("circuit-prop") << "TRUE: " << assertion << std::endl;
  if (assertion.getKind() == kind::CONST_BOOLEAN && !assertion.getConst<bool>())
  {
    makeConflict(assertion);
  }
  else if (assertion.getKind() == kind::AND)
  {
    ProofCircuitPropagatorBackward prover{
        d_env.getProofNodeManager(), assertion, true};
    if (isProofEnabled())
    {
      addProof(assertion, prover.assume(assertion));
    }
    for (auto it = assertion.begin(); it != assertion.end(); ++it)
    {
      addProof(*it, prover.andTrue(it));
      assertTrue(*it);
    }
  }
  else
  {
    // Analyze the assertion for back-edges and all that
    computeBackEdges(assertion);
    // Assign the given assertion to true
    assignAndEnqueue(assertion,
                     true,
                     isProofEnabled()
                         ? d_env.getProofNodeManager()->mkAssume(assertion)
                         : nullptr);
  }
}

void CircuitPropagator::assignAndEnqueue(TNode n,
                                         bool value,
                                         std::shared_ptr<ProofNode> proof)
{
  Trace("circuit-prop") << "CircuitPropagator::assign(" << n << ", "
                        << (value ? "true" : "false") << ")" << std::endl;

  if (n.getKind() == kind::CONST_BOOLEAN)
  {
    // Assigning a constant to the opposite value is dumb
    if (value != n.getConst<bool>())
    {
      makeConflict(n);
      return;
    }
  }

  if (isProofEnabled())
  {
    if (proof == nullptr)
    {
      warning() << "CircuitPropagator: Proof is missing for " << n << std::endl;
      Assert(false);
    }
    else
    {
      Assert(!proof->getResult().isNull());
      Node expected = value ? Node(n) : n.negate();
      if (proof->getResult() != expected)
      {
        warning() << "CircuitPropagator: Incorrect proof: " << expected
                  << " vs. " << proof->getResult() << std::endl
                  << *proof << std::endl;
      }
      addProof(expected, std::move(proof));
    }
  }

  // Get the current assignment
  AssignmentStatus state = d_state[n];

  if (state != UNASSIGNED)
  {
    // If the node is already assigned we might have a conflict
    if (value != (state == ASSIGNED_TO_TRUE))
    {
      makeConflict(n);
    }
  }
  else
  {
    // If unassigned, mark it as assigned
    d_state[n] = value ? ASSIGNED_TO_TRUE : ASSIGNED_TO_FALSE;
    // Add for further propagation
    d_propagationQueue.push_back(n);
  }
}

void CircuitPropagator::makeConflict(Node n)
{
  auto bfalse = NodeManager::currentNM()->mkConst(false);
  ProofGenerator* g = nullptr;
  if (isProofEnabled())
  {
    if (d_epg->hasProofFor(bfalse))
    {
      return;
    }
    ProofCircuitPropagator pcp(d_env.getProofNodeManager());
    if (n == bfalse)
    {
      d_epg->setProofFor(bfalse, pcp.assume(bfalse));
    }
    else
    {
      d_epg->setProofFor(bfalse,
                         pcp.conflict(pcp.assume(n), pcp.assume(n.negate())));
    }
    g = d_proofInternal.get();
    Trace("circuit-prop") << "Added conflict " << *d_epg->getProofFor(bfalse)
                          << std::endl;
    Trace("circuit-prop") << "\texpanded " << *g->getProofFor(bfalse)
                          << std::endl;
  }
  d_conflict = TrustNode::mkTrustLemma(bfalse, g);
}

void CircuitPropagator::computeBackEdges(TNode node)
{
  Trace("circuit-prop") << "CircuitPropagator::computeBackEdges(" << node << ")"
                        << endl;

  // Vector of nodes to visit
  vector<TNode> toVisit;

  // Start with the top node
  if (d_seen.find(node) == d_seen.end())
  {
    toVisit.push_back(node);
    d_seen.insert(node);
  }

  // Initialize the back-edges for the root, so we don't have a special case
  d_backEdges[node];

  // Go through the visit list
  for (unsigned i = 0; i < toVisit.size(); ++i)
  {
    // Node we need to visit
    TNode current = toVisit[i];
    Trace("circuit-prop")
        << "CircuitPropagator::computeBackEdges(): processing " << current
        << endl;
    Assert(d_seen.find(current) != d_seen.end());

    // If this not an atom visit all the children and compute the back edges
    if (Theory::theoryOf(current) == THEORY_BOOL)
    {
      for (unsigned child = 0, child_end = current.getNumChildren();
           child < child_end;
           ++child)
      {
        TNode childNode = current[child];
        // Add the back edge
        d_backEdges[childNode].push_back(current);
        // Add to the queue if not seen yet
        if (d_seen.find(childNode) == d_seen.end())
        {
          toVisit.push_back(childNode);
          d_seen.insert(childNode);
        }
      }
    }
  }
}

void CircuitPropagator::propagateBackward(TNode parent, bool parentAssignment)
{
  Trace("circuit-prop") << "CircuitPropagator::propagateBackward(" << parent
                        << ", " << parentAssignment << ")" << endl;
  ProofCircuitPropagatorBackward prover{
      d_env.getProofNodeManager(), parent, parentAssignment};

  // backward rules
  switch (parent.getKind())
  {
    case kind::AND:
      if (parentAssignment)
      {
        // AND = TRUE: forall children c, assign(c = TRUE)
        for (TNode::iterator i = parent.begin(), i_end = parent.end();
             i != i_end;
             ++i)
        {
          assignAndEnqueue(*i, true, prover.andTrue(i));
        }
      }
      else
      {
        // AND = FALSE: if all children BUT ONE == TRUE, assign(c = FALSE)
        TNode::iterator holdout =
            find_if_unique(parent.begin(), parent.end(), [this](TNode x) {
              return !isAssignedTo(x, true);
            });
        if (holdout != parent.end())
        {
          assignAndEnqueue(*holdout, false, prover.andFalse(parent, holdout));
        }
      }
      break;
    case kind::OR:
      if (parentAssignment)
      {
        // OR = TRUE: if all children BUT ONE == FALSE, assign(c = TRUE)
        TNode::iterator holdout =
            find_if_unique(parent.begin(), parent.end(), [this](TNode x) {
              return !isAssignedTo(x, false);
            });
        if (holdout != parent.end())
        {
          assignAndEnqueue(*holdout, true, prover.orTrue(parent, holdout));
        }
      }
      else
      {
        // OR = FALSE: forall children c, assign(c = FALSE)
        for (TNode::iterator i = parent.begin(), i_end = parent.end();
             i != i_end;
             ++i)
        {
          assignAndEnqueue(*i, false, prover.orFalse(i));
        }
      }
      break;
    case kind::NOT:
      // NOT = b: assign(c = !b)
      assignAndEnqueue(
          parent[0], !parentAssignment, prover.Not(!parentAssignment, parent));
      break;
    case kind::ITE:
      if (isAssignedTo(parent[0], true))
      {
        // ITE c x y = v: if c is assigned and TRUE, assign(x = v)
        assignAndEnqueue(parent[1], parentAssignment, prover.iteC(true));
      }
      else if (isAssignedTo(parent[0], false))
      {
        // ITE c x y = v: if c is assigned and FALSE, assign(y = v)
        assignAndEnqueue(parent[2], parentAssignment, prover.iteC(false));
      }
      else if (isAssigned(parent[1]) && isAssigned(parent[2]))
      {
        if (getAssignment(parent[1]) == parentAssignment
            && getAssignment(parent[2]) != parentAssignment)
        {
          // ITE c x y = v: if c is unassigned, x and y are assigned, x==v and
          // y!=v, assign(c = TRUE)
          assignAndEnqueue(parent[0], true, prover.iteIsCase(1));
        }
        else if (getAssignment(parent[1]) != parentAssignment
                 && getAssignment(parent[2]) == parentAssignment)
        {
          // ITE c x y = v: if c is unassigned, x and y are assigned, x!=v and
          // y==v, assign(c = FALSE)
          assignAndEnqueue(parent[0], false, prover.iteIsCase(0));
        }
      }
      break;
    case kind::EQUAL:
      Assert(parent[0].getType().isBoolean());
      if (parentAssignment)
      {
        // IFF x y = TRUE: if x [resp y] is assigned, assign(y = x.assignment
        // [resp x = y.assignment])
        if (isAssigned(parent[0]))
        {
          assignAndEnqueue(parent[1],
                           getAssignment(parent[0]),
                           prover.eqYFromX(getAssignment(parent[0]), parent));
        }
        else if (isAssigned(parent[1]))
        {
          assignAndEnqueue(parent[0],
                           getAssignment(parent[1]),
                           prover.eqXFromY(getAssignment(parent[1]), parent));
        }
      }
      else
      {
        // IFF x y = FALSE: if x [resp y] is assigned, assign(y = !x.assignment
        // [resp x = !y.assignment])
        if (isAssigned(parent[0]))
        {
          assignAndEnqueue(parent[1],
                           !getAssignment(parent[0]),
                           prover.neqYFromX(getAssignment(parent[0]), parent));
        }
        else if (isAssigned(parent[1]))
        {
          assignAndEnqueue(parent[0],
                           !getAssignment(parent[1]),
                           prover.neqXFromY(getAssignment(parent[1]), parent));
        }
      }
      break;
    case kind::IMPLIES:
      if (parentAssignment)
      {
        if (isAssignedTo(parent[0], true))
        {
          // IMPLIES x y = TRUE, and x == TRUE: assign(y = TRUE)
          assignAndEnqueue(parent[1], true, prover.impliesYFromX(parent));
        }
        if (isAssignedTo(parent[1], false))
        {
          // IMPLIES x y = TRUE, and y == FALSE: assign(x = FALSE)
          assignAndEnqueue(parent[0], false, prover.impliesXFromY(parent));
        }
      }
      else
      {
        // IMPLIES x y = FALSE: assign(x = TRUE) and assign(y = FALSE)
        assignAndEnqueue(parent[0], true, prover.impliesNegX());
        assignAndEnqueue(parent[1], false, prover.impliesNegY());
      }
      break;
    case kind::XOR:
      if (parentAssignment)
      {
        if (isAssigned(parent[0]))
        {
          // XOR x y = TRUE, and x assigned, assign(y = !assignment(x))
          assignAndEnqueue(
              parent[1],
              !getAssignment(parent[0]),
              prover.xorYFromX(
                  !parentAssignment, getAssignment(parent[0]), parent));
        }
        else if (isAssigned(parent[1]))
        {
          // XOR x y = TRUE, and y assigned, assign(x = !assignment(y))
          assignAndEnqueue(
              parent[0],
              !getAssignment(parent[1]),
              prover.xorXFromY(
                  !parentAssignment, getAssignment(parent[1]), parent));
        }
      }
      else
      {
        if (isAssigned(parent[0]))
        {
          // XOR x y = FALSE, and x assigned, assign(y = assignment(x))
          assignAndEnqueue(
              parent[1],
              getAssignment(parent[0]),
              prover.xorYFromX(
                  !parentAssignment, getAssignment(parent[0]), parent));
        }
        else if (isAssigned(parent[1]))
        {
          // XOR x y = FALSE, and y assigned, assign(x = assignment(y))
          assignAndEnqueue(
              parent[0],
              getAssignment(parent[1]),
              prover.xorXFromY(
                  !parentAssignment, getAssignment(parent[1]), parent));
        }
      }
      break;
    default: Unhandled();
  }
}

void CircuitPropagator::propagateForward(TNode child, bool childAssignment)
{
  // The assignment we have
  Trace("circuit-prop") << "CircuitPropagator::propagateForward(" << child
                        << ", " << childAssignment << ")" << endl;

  // Get the back any nodes where this is child
  const vector<Node>& parents = d_backEdges.find(child)->second;

  // Go through the parents and see if there is anything to propagate
  vector<Node>::const_iterator parent_it = parents.begin();
  vector<Node>::const_iterator parent_it_end = parents.end();
  for (; parent_it != parent_it_end && d_conflict.get().isNull(); ++parent_it)
  {
    // The current parent of the child
    TNode parent = *parent_it;
    Trace("circuit-prop") << "Parent: " << parent << endl;
    Assert(expr::hasSubterm(parent, child));

    ProofCircuitPropagatorForward prover{
        d_env.getProofNodeManager(), child, childAssignment, parent};

    // Forward rules
    switch (parent.getKind())
    {
      case kind::AND:
        if (childAssignment)
        {
          TNode::iterator holdout;
          holdout = find_if(parent.begin(), parent.end(), [this](TNode x) {
            return !isAssignedTo(x, true);
          });

          if (holdout == parent.end())
          {  // all children are assigned TRUE
            // AND ...(x=TRUE)...: if all children now assigned to TRUE,
            // assign(AND = TRUE)
            assignAndEnqueue(parent, true, prover.andAllTrue());
          }
          else if (isAssignedTo(parent, false))
          {  // the AND is FALSE
            // is the holdout unique ?
            TNode::iterator other =
                find_if(holdout + 1, parent.end(), [this](TNode x) {
                  return !isAssignedTo(x, true);
                });
            if (other == parent.end())
            {  // the holdout is unique
              // AND ...(x=TRUE)...: if all children BUT ONE now assigned to
              // TRUE, and AND == FALSE, assign(last_holdout = FALSE)
              assignAndEnqueue(
                  *holdout, false, prover.andFalse(parent, holdout));
            }
          }
        }
        else
        {
          // AND ...(x=FALSE)...: assign(AND = FALSE)
          assignAndEnqueue(parent, false, prover.andOneFalse());
        }
        break;
      case kind::OR:
        if (childAssignment)
        {
          // OR ...(x=TRUE)...: assign(OR = TRUE)
          assignAndEnqueue(parent, true, prover.orOneTrue());
        }
        else
        {
          TNode::iterator holdout;
          holdout = find_if(parent.begin(), parent.end(), [this](TNode x) {
            return !isAssignedTo(x, false);
          });
          if (holdout == parent.end())
          {  // all children are assigned FALSE
            // OR ...(x=FALSE)...: if all children now assigned to FALSE,
            // assign(OR = FALSE)
            assignAndEnqueue(parent, false, prover.orFalse());
          }
          else if (isAssignedTo(parent, true))
          {  // the OR is TRUE
            // is the holdout unique ?
            TNode::iterator other =
                find_if(holdout + 1, parent.end(), [this](TNode x) {
                  return !isAssignedTo(x, false);
                });
            if (other == parent.end())
            {  // the holdout is unique
              // OR ...(x=FALSE)...: if all children BUT ONE now assigned to
              // FALSE, and OR == TRUE, assign(last_holdout = TRUE)
              assignAndEnqueue(*holdout, true, prover.orTrue(parent, holdout));
            }
          }
        }
        break;

      case kind::NOT:
        // NOT (x=b): assign(NOT = !b)
        assignAndEnqueue(
            parent, !childAssignment, prover.Not(childAssignment, parent));
        break;

      case kind::ITE:
        if (child == parent[0])
        {
          if (childAssignment)
          {
            if (isAssigned(parent[1]))
            {
              // ITE (c=TRUE) x y: if x is assigned, assign(ITE = x.assignment)
              assignAndEnqueue(parent,
                               getAssignment(parent[1]),
                               prover.iteEvalThen(getAssignment(parent[1])));
            }
          }
          else
          {
            if (isAssigned(parent[2]))
            {
              // ITE (c=FALSE) x y: if y is assigned, assign(ITE = y.assignment)
              assignAndEnqueue(parent,
                               getAssignment(parent[2]),
                               prover.iteEvalElse(getAssignment(parent[2])));
            }
          }
        }
        if (child == parent[1])
        {
          if (isAssignedTo(parent[0], true))
          {
            // ITE c (x=v) y: if c is assigned and TRUE, assign(ITE = v)
            assignAndEnqueue(
                parent, childAssignment, prover.iteEvalThen(childAssignment));
          }
        }
        if (child == parent[2])
        {
          Assert(child == parent[2]);
          if (isAssignedTo(parent[0], false))
          {
            // ITE c x (y=v): if c is assigned and FALSE, assign(ITE = v)
            assignAndEnqueue(
                parent, childAssignment, prover.iteEvalElse(childAssignment));
          }
        }
        break;
      case kind::EQUAL:
        Assert(parent[0].getType().isBoolean());
        if (isAssigned(parent[0]) && isAssigned(parent[1]))
        {
          // IFF x y: if x and y is assigned, assign(IFF = (x.assignment <=>
          // y.assignment))
          assignAndEnqueue(parent,
                           getAssignment(parent[0]) == getAssignment(parent[1]),
                           prover.eqEval(getAssignment(parent[0]),
                                         getAssignment(parent[1])));
        }
        else
        {
          if (isAssigned(parent))
          {
            if (child == parent[0])
            {
              if (getAssignment(parent))
              {
                // IFF (x = b) y: if IFF is assigned to TRUE, assign(y = b)
                assignAndEnqueue(parent[1],
                                 childAssignment,
                                 prover.eqYFromX(childAssignment, parent));
              }
              else
              {
                // IFF (x = b) y: if IFF is assigned to FALSE, assign(y = !b)
                assignAndEnqueue(parent[1],
                                 !childAssignment,
                                 prover.neqYFromX(childAssignment, parent));
              }
            }
            else
            {
              Assert(child == parent[1]);
              if (getAssignment(parent))
              {
                // IFF x y = b: if IFF is assigned to TRUE, assign(x = b)
                assignAndEnqueue(parent[0],
                                 childAssignment,
                                 prover.eqXFromY(childAssignment, parent));
              }
              else
              {
                // IFF x y = b y: if IFF is assigned to FALSE, assign(x = !b)
                assignAndEnqueue(parent[0],
                                 !childAssignment,
                                 prover.neqXFromY(childAssignment, parent));
              }
            }
          }
        }
        break;
      case kind::IMPLIES:
        if (isAssigned(parent[0]) && isAssigned(parent[1]))
        {
          // IMPLIES (x=v1) (y=v2): assign(IMPLIES = (!v1 || v2))
          assignAndEnqueue(
              parent,
              !getAssignment(parent[0]) || getAssignment(parent[1]),
              prover.impliesEval(getAssignment(parent[0]),
                                 getAssignment(parent[1])));
        }
        else
        {
          if (child == parent[0] && childAssignment
              && isAssignedTo(parent, true))
          {
            // IMPLIES (x=TRUE) y [with IMPLIES == TRUE]: assign(y = TRUE)
            assignAndEnqueue(parent[1], true, prover.impliesYFromX(parent));
          }
          if (child == parent[1] && !childAssignment
              && isAssignedTo(parent, true))
          {
            // IMPLIES x (y=FALSE) [with IMPLIES == TRUE]: assign(x = FALSE)
            assignAndEnqueue(parent[0], false, prover.impliesXFromY(parent));
          }
          // Note that IMPLIES == FALSE doesn't need any cases here
          // because if that assignment has been done, we've already
          // propagated all the children (in back-propagation).
        }
        break;
      case kind::XOR:
        if (isAssigned(parent))
        {
          if (child == parent[0])
          {
            // XOR (x=v) y [with XOR assigned], assign(y = (v ^ XOR)
            assignAndEnqueue(
                parent[1],
                childAssignment != getAssignment(parent),
                prover.xorYFromX(
                    !getAssignment(parent), childAssignment, parent));
          }
          else
          {
            Assert(child == parent[1]);
            // XOR x (y=v) [with XOR assigned], assign(x = (v ^ XOR))
            assignAndEnqueue(
                parent[0],
                childAssignment != getAssignment(parent),
                prover.xorXFromY(
                    !getAssignment(parent), childAssignment, parent));
          }
        }
        if (isAssigned(parent[0]) && isAssigned(parent[1]))
        {
          assignAndEnqueue(parent,
                           getAssignment(parent[0]) != getAssignment(parent[1]),
                           prover.xorEval(getAssignment(parent[0]),
                                          getAssignment(parent[1])));
        }
        break;
      default: Unhandled();
    }
  }
}

TrustNode CircuitPropagator::propagate()
{
  Trace("circuit-prop") << "CircuitPropagator::propagate()" << std::endl;

  for (unsigned i = 0;
       i < d_propagationQueue.size() && d_conflict.get().isNull();
       ++i)
  {
    // The current node we are propagating
    TNode current = d_propagationQueue[i];
    Trace("circuit-prop") << "CircuitPropagator::propagate(): processing "
                          << current << std::endl;
    bool assignment = getAssignment(current);
    Trace("circuit-prop") << "CircuitPropagator::propagate(): assigned to "
                          << (assignment ? "true" : "false") << std::endl;

    // Is this an atom
    bool atom = Theory::theoryOf(current) != THEORY_BOOL || current.isVar()
                || (current.getKind() == kind::EQUAL
                    && (current[0].isVar() && current[1].isVar()));

    // If an atom, add to the list for simplification
    if (atom
        || (current.getKind() == kind::EQUAL
            && (current[0].isVar() || current[1].isVar())))
    {
      Trace("circuit-prop")
          << "CircuitPropagator::propagate(): adding to learned: "
          << (assignment ? (Node)current : current.notNode()) << std::endl;
      Node lit = assignment ? Node(current) : current.notNode();

      if (isProofEnabled())
      {
        if (d_epg->hasProofFor(lit))
        {
          // if we have a parent proof generator that provides proofs of the
          // inputs to this class, we must use the lazy proof chain
          ProofGenerator* pg = d_proofInternal.get();
          if (d_proofExternal != nullptr)
          {
            d_proofExternal->addLazyStep(lit, pg);
            pg = d_proofExternal.get();
          }
          TrustNode tlit = TrustNode::mkTrustLemma(lit, pg);
          d_learnedLiterals.push_back(tlit);
        }
        else
        {
          warning() << "CircuitPropagator: Proof is missing for " << lit
                    << std::endl;
          TrustNode tlit = TrustNode::mkTrustLemma(lit, nullptr);
          d_learnedLiterals.push_back(tlit);
        }
      }
      else
      {
        TrustNode tlit = TrustNode::mkTrustLemma(lit, nullptr);
        d_learnedLiterals.push_back(tlit);
      }
      Trace("circuit-prop") << "Added proof for " << lit << std::endl;
    }

    // Propagate this value to the children (if not an atom or a constant)
    if (d_backwardPropagation && !atom && !current.isConst())
    {
      propagateBackward(current, assignment);
    }
    // Propagate this value to the parents
    if (d_forwardPropagation)
    {
      propagateForward(current, assignment);
    }
  }

  // No conflict
  return d_conflict;
}

void CircuitPropagator::enableProofs(context::Context* ctx,
                                     ProofGenerator* defParent)
{
  d_epg.reset(new EagerProofGenerator(d_env, ctx));
  d_proofInternal.reset(new LazyCDProofChain(
      d_env, true, ctx, d_epg.get(), true, "CircuitPropInternalLazyChain"));
  if (defParent != nullptr)
  {
    // If we provide a parent proof generator (defParent), we want the ASSUME
    // leafs of proofs provided by this class to call the getProofFor method on
    // the parent. To do this, we use a LazyCDProofChain.
    d_proofExternal.reset(new LazyCDProofChain(
        d_env, true, ctx, defParent, false, "CircuitPropExternalLazyChain"));
  }
}

bool CircuitPropagator::isProofEnabled() const
{
  return d_proofInternal != nullptr;
}

void CircuitPropagator::addProof(TNode f, std::shared_ptr<ProofNode> pf)
{
  if (isProofEnabled())
  {
    if (!d_epg->hasProofFor(f))
    {
      Trace("circuit-prop") << "Adding proof for " << f << std::endl
                            << "\t" << *pf << std::endl;
      d_epg->setProofFor(f, std::move(pf));
    }
    else if (TraceIsOn("circuit-prop"))
    {
      auto prf = d_epg->getProofFor(f);
      Trace("circuit-prop") << "Ignoring proof\n\t" << *pf
                            << "\nwe already have\n\t" << *prf << std::endl;
    }
  }
}

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5::internal
