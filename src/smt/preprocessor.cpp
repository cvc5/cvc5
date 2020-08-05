/*********************                                                        */
/*! \file assertions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for storing assertions for an SMT engine.
 **/

#include "smt/preprocessor.h"

#include "smt/smt_engine.h"
#include "options/smt_options.h"
#include "smt/assertions.h"
#include "smt/abstract_values.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

Preprocessor::Preprocessor(SmtEngine& smt, context::UserContext* u, AbstractValues& abs)
    :  d_propagator(true, true),
        d_assertionsProcessed(u, false),
        d_processor(smt, *smt.getResourceManager()),
        d_rtf(u),
        d_absValues(abs)
{
}

Preprocessor::~Preprocessor()
{
}

void Preprocessor::finishInit()
{
  
}

bool Preprocessor::processAssertions(Assertions& as)
{
  AssertionPipeline& ap = as.getAssertionPipeline();

  Assert (ap.size()!=0);
  
  if (d_assertionsProcessed && options::incrementalSolving()) {
    // TODO(b/1255): Substitutions in incremental mode should be managed with a
    // proper data structure.
    ap.enableStoreSubstsInAsserts();
  }
  else
  {
    ap.disableStoreSubstsInAsserts();
  }

  // process the assertions
  bool noConflict = d_processor.apply(as);
  
  // mark that we've processed assertions
  d_assertionsProcessed = true;
}

RemoveTermFormulas& getTermFormulaRemover()
{
  return d_rtf;
}

Node Preprocessor::expandDefinitions(const Node& ex)
{
  Trace("smt") << "SMT expandDefinitions(" << ex << ")" << endl;
  // Substitute out any abstract values in ex.
  Node e = d_absValues.substituteAbstractValues(ex);
  if(options::typeChecking()) 
  {
    // Ensure expr is type-checked at this point.
    e.getType(true);
  }
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  // expand only = true
  return d_processor->expandDefinitions( e, cache, true);
}

Node Preprocessor::simplify(const Node& ex)
{
  Trace("smt") << "SMT simplify(" << ex << ")" << endl;
  if(Dump.isOn("benchmark")) 
  {
    Dump("benchmark") << SimplifyCommand(ex);
  }
  Node e = d_absValues.substituteAbstractValues(ex);
  if( options::typeChecking() ) 
  {
    // ensure expr is type-checked at this point
    e.getType(true);
  }
  // Make sure all preprocessing is done
  d_private->processAssertions(*d_asserts);
  Node n = d_private->simplify(Node::fromExpr(e));
  return n.toExpr();
}

Node Preprocessor::applySubstitutions(TNode node)
{
  return Rewriter::rewrite(
      d_preprocessingPassContext->getTopLevelSubstitutions().apply(node));
}

}  // namespace smt
}  // namespace CVC4
