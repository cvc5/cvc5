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

#include "options/smt_options.h"
#include "smt/abstract_values.h"
#include "smt/assertions.h"
#include "smt/smt_engine.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

Preprocessor::Preprocessor(SmtEngine& smt,
                           context::UserContext* u,
                           AbstractValues& abs)
    : d_propagator(true, true),
      d_assertionsProcessed(u, false),
      d_processor(smt, *smt.getResourceManager()),
      d_rtf(u),
      d_absValues(abs)
{
}

Preprocessor::~Preprocessor()
{
  if (d_propagator.getNeedsFinish())
  {
    d_propagator.finish();
    d_propagator.setNeedsFinish(false);
  }
}

void Preprocessor::finishInit()
{
  d_preprocessingPassContext.reset(
      new PreprocessingPassContext(&d_smt, &d_iteRemover, &d_propagator));

  // initialize the preprocessing passes
  d_processor.finishInit(d_preprocessingPassContext.get());
}

bool Preprocessor::process(Assertions& as)
{
  AssertionPipeline& ap = as.getAssertionPipeline();

  // should not be called if empty
  Assert(ap.size() != 0);

  if (d_assertionsProcessed && options::incrementalSolving())
  {
    // TODO(b/1255): Substitutions in incremental mode should be managed with a
    // proper data structure.
    ap.enableStoreSubstsInAsserts();
  }
  else
  {
    ap.disableStoreSubstsInAsserts();
  }

  // process the assertions, return true if no conflict is discovered
  return d_processor.apply(as);
}

void Preprocessor::postprocess(Assertions& as)
{
  AssertionPipeline& ap = as.getAssertionPipeline();
  // if incremental, compute which variables are assigned
  if (options::incrementalSolving())
  {
    d_preprocessingPassContext->recordSymbolsInAssertions(ap.ref());
  }

  // mark that we've processed assertions
  d_assertionsProcessed = true;
}

void Preprocessor::clearLearnedLiterals()
{
  d_propagator.getLearnedLiterals().clear();
}

RemoveTermFormulas& getTermFormulaRemover() { return d_rtf; }

Node Preprocessor::expandDefinitions(const Node& ex)
{
  Trace("smt") << "SMT expandDefinitions(" << ex << ")" << endl;
  // Substitute out any abstract values in ex.
  Node e = d_absValues.substituteAbstractValues(ex);
  if (options::typeChecking())
  {
    // Ensure expr is type-checked at this point.
    e.getType(true);
  }
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  // expand only = true
  return d_processor->expandDefinitions(e, cache, true);
}

Node Preprocessor::simplify(const Node& ex, bool removeItes)
{
  Trace("smt") << "SMT simplify(" << ex << ")" << endl;
  if (Dump.isOn("benchmark"))
  {
    Dump("benchmark") << SimplifyCommand(ex);
  }
  Node e = d_absValues.substituteAbstractValues(ex);
  if (options::typeChecking())
  {
    // ensure expr is type-checked at this point
    e.getType(true);
  }
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  Node n = d_processor.expandDefinitions(in, cache);
  Node ns = applySubstitutions(n);
  if (removeItes)
  {
    // also remove ites if asked
    ns = d_iteRemover.replace(ns);
  }
  return ns;
}

Node Preprocessor::removeTermFormulas(const Node& e)
{
  return d_rtf.replace(e);
}

Node Preprocessor::applySubstitutions(TNode node)
{
  return Rewriter::rewrite(
      d_preprocessingPassContext->getTopLevelSubstitutions().apply(node));
}

}  // namespace smt
}  // namespace CVC4
