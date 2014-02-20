/*********************                                                        */
/*! \file theory_rewriterules.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Francois Bobot
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Deals with rewrite rules ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/rewriterules/theory_rewriterules.h"
#include "theory/rewriter.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::rewriterules;
using namespace CVC4::theory::rrinst;


namespace CVC4 {
namespace theory {
namespace rewriterules {


TheoryRewriteRules::TheoryRewriteRules(context::Context* c,
                                       context::UserContext* u,
                                       OutputChannel& out,
                                       Valuation valuation,
                                       const LogicInfo& logicInfo) :
  Theory(THEORY_REWRITERULES, c, u, out, valuation, logicInfo)
{

}

void TheoryRewriteRules::check(Effort level) {
  CodeTimer codeTimer(d_theoryTime);

  while(!done()) {
    // Get all the assertions
    // TODO: Test that it have already been ppAsserted

    //if we are here and ppAssert has not been done
    // that means that ppAssert is off so we need to assert now
    Assertion assertion = get();
    // Assertion assertion = get();
    // TNode fact = assertion.assertion;

    // Debug("rewriterules") << "TheoryRewriteRules::check(): processing " << fact << std::endl;
    //   if (getValuation().getDecisionLevel()>0)
    //     Unhandled(getValuation().getDecisionLevel());
    //   addRewriteRule(fact);

    }
};

Node TheoryRewriteRules::explain(TNode n){

  return Node::null();
}

void TheoryRewriteRules::collectModelInfo( TheoryModel* m, bool fullModel ){

}

}/* CVC4::theory::rewriterules namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
