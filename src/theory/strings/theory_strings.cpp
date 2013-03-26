/*********************                                                        */
/*! \file theory_strings.cpp
 ** \verbatim
 ** Original author: tiliang
 ** Major contributors: tiliang
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2013-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of arrays.
 **
 ** Implementation of the theory of arrays.
 **/


#include "theory/strings/theory_strings.h"
#include "theory/valuation.h"
#include "expr/kind.h"
#include "theory/rewriter.h"
#include "expr/command.h"
#include "theory/model.h"
#include "smt/logic_exception.h"


using namespace std;

namespace CVC4 {
namespace theory {
namespace strings {

TheoryStrings::TheoryStrings(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe)
	: Theory(THEORY_STRINGS, c, u, out, valuation, logicInfo, qe)
{

}

TheoryStrings::~TheoryStrings() {

}

void TheoryStrings::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  //d_equalityEngine.setMasterEqualityEngine(eq);
}

void TheoryStrings::propagate(Effort e)
{
  // direct propagation now
}


Node TheoryStrings::explain(TNode literal)
{
	return Node::null();
}

/////////////////////////////////////////////////////////////////////////////
// MODEL GENERATION
/////////////////////////////////////////////////////////////////////////////


void TheoryStrings::collectModelInfo( TheoryModel* m, bool fullModel )
{
}

/////////////////////////////////////////////////////////////////////////////
// MAIN SOLVER
/////////////////////////////////////////////////////////////////////////////


void TheoryStrings::check(Effort e) {

  while ( !done() )
  {
    // Get all the assertions
    Assertion assertion = get();
    TNode fact = assertion.assertion;

  }
}


}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
