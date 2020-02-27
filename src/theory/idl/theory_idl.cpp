/*********************                                                        */
/*! \file theory_idl.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/idl/theory_idl.h"

#include <set>
#include <queue>

#include "options/idl_options.h"
#include "theory/rewriter.h"


using namespace std;

namespace CVC4 {
namespace theory {
namespace idl {

TheoryIdl::TheoryIdl(context::Context* c, context::UserContext* u,
                     OutputChannel& out, Valuation valuation,
                     const LogicInfo& logicInfo)
    : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo)
    , d_model(c)
    , d_assertionsDB(c)
{}

Node TheoryIdl::ppRewrite(TNode atom) {
  if (atom.getKind() == kind::EQUAL  && options::idlRewriteEq()) {
    // If the option is turned on, each equality into two inequalities. This in
    // effect removes equalities, and theorefore dis-equalities too.
    Node leq = NodeBuilder<2>(kind::LEQ) << atom[0] << atom[1];
    Node geq = NodeBuilder<2>(kind::GEQ) << atom[0] << atom[1];
    Node rewritten = Rewriter::rewrite(leq.andNode(geq));
    return rewritten;
  } else {
    return atom;
  }
}

void TheoryIdl::check(Effort level) {
  if (done() && !fullEffort(level)) {
    return;
  }

  TimerStat::CodeTimer checkTimer(d_checkTime);

  while(!done()) {

    // Get the next assertion
    Assertion assertion = get();
    Debug("theory::idl") << "TheoryIdl::check(): processing "
                         << assertion.d_assertion << std::endl;

    // Convert the assertion into the internal representation
    IDLAssertion idlAssertion(assertion.d_assertion);
    Debug("theory::idl") << "TheoryIdl::check(): got " << idlAssertion << std::endl;

    if (idlAssertion.ok()) {
      if (idlAssertion.getOp() == kind::DISTINCT) {
        // We don't handle dis-equalities
        d_out->setIncomplete();
      } else {
        // Process the convex assertions immediately
        bool ok = processAssertion(idlAssertion);
        if (!ok) {
          // In conflict, we're done
          return;
        }
      }
    } else {
      // Not an IDL assertion, set incomplete
      d_out->setIncomplete();
    }
  }

}

bool TheoryIdl::processAssertion(const IDLAssertion& assertion) {

  Debug("theory::idl") << "TheoryIdl::processAssertion(" << assertion << ")" << std::endl;

  // Add the constraint (x - y op c) to the list assertions of x
  d_assertionsDB.add(assertion, assertion.getX());

  // Update the model, if forced by the assertion
  bool y_updated = assertion.propagate(d_model);

  // If the value of y was updated, we might need to update further
  if (y_updated) {

    std::queue<TNode> queue; // Queue of variables to consider
    std::set<TNode> inQueue; // Current elements of the queue

    // Add the first updated variable to the queue
    queue.push(assertion.getY());
    inQueue.insert(assertion.getY());

    while (!queue.empty()) {
      // Pop a new variable x off the queue
      TNode x = queue.front();
      queue.pop();
      inQueue.erase(x);

      // Go through the constraint (x - y op c), and update values of y
      IDLAssertionDB::iterator it(d_assertionsDB, x);
      while (!it.done()) {
        // Get the assertion and update y
        IDLAssertion x_y_assertion = it.get();
        y_updated = x_y_assertion.propagate(d_model);
        // If updated add to the queue
        if (y_updated) {
          // If the variable that we updated is the same as the first
          // variable that we updated, it's a cycle of updates => conflict
          if (x_y_assertion.getY() == assertion.getX()) {
            std::vector<TNode> reasons;
            d_model.getReasonCycle(x_y_assertion.getY(), reasons);
            // Construct the reason of the conflict
            Node conflict = NodeManager::currentNM()->mkNode(kind::AND, reasons);
            d_out->conflict(conflict);
            return false;
          } else {
            // No cycle, just a model update, so we add to the queue
            TNode y = x_y_assertion.getY();
            if (inQueue.count(y) == 0) {
              queue.push(y);
              inQueue.insert(x_y_assertion.getY());
            }
          }
        }
        // Go to the next constraint
        it.next();
      }
    }
  }

  // Everything fine, no conflict
  return true;
}

} /* namepsace CVC4::theory::idl */
} /* namepsace CVC4::theory */
} /* namepsace CVC4 */
