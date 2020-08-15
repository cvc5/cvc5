/*********************                                                        */
/*! \file preprocessor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessor of the SMT engine.
 **/

#include "smt/preprocessor.h"

#include "options/smt_options.h"
#include "smt/abstract_values.h"
#include "smt/assertions.h"
#include "smt/command.h"
#include "smt/smt_engine.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

Preprocessor::Preprocessor(SmtEngine& smt,
                           context::UserContext* u,
                           AbstractValues& abs)
    : d_smt(smt),
      d_absValues(abs),
      d_propagator(true, true),
      d_assertionsProcessed(u, false),
      d_processor(smt, *smt.getResourceManager()),
      d_rtf(u)
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
  d_ppContext.reset(new preprocessing::PreprocessingPassContext(
      &d_smt, &d_rtf, &d_propagator));

  // initialize the preprocessing passes
  d_processor.finishInit(d_ppContext.get());
}

bool Preprocessor::process(Assertions& as)
{
  preprocessing::AssertionPipeline& ap = as.getAssertionPipeline();

  // should not be called if empty
  Assert(ap.size() != 0) << "Can only preprocess a non-empty list of assertions";

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
  preprocessing::AssertionPipeline& ap = as.getAssertionPipeline();
  // if incremental, compute which variables are assigned
  if (options::incrementalSolving())
  {
    d_ppContext->recordSymbolsInAssertions(ap.ref());
  }

  // mark that we've processed assertions
  d_assertionsProcessed = true;
}

void Preprocessor::clearLearnedLiterals()
{
  d_propagator.getLearnedLiterals().clear();
}

void Preprocessor::cleanup() { d_processor.cleanup(); }

RemoveTermFormulas& Preprocessor::getTermFormulaRemover() { return d_rtf; }

Node Preprocessor::expandDefinitions(const Node& n, bool expandOnly)
{
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  return expandDefinitions(n, cache, expandOnly);
}

Node Preprocessor::expandDefinitions(
    const Node& node,
    std::unordered_map<Node, Node, NodeHashFunction>& cache,
    bool expandOnly)
{
  Trace("smt") << "SMT expandDefinitions(" << node << ")" << endl;
  // Substitute out any abstract values in node.
  Node n = d_absValues.substituteAbstractValues(node);
  if (options::typeChecking())
  {
    // Ensure node is type-checked at this point.
    n.getType(true);
  }
  // expand only = true
  return d_processor.expandDefinitions(n, cache, expandOnly);
}

Node Preprocessor::simplify(const Node& node, bool removeItes)
{
  Trace("smt") << "SMT simplify(" << node << ")" << endl;
  if (Dump.isOn("benchmark"))
  {
    Dump("benchmark") << SimplifyCommand(node.toExpr());
  }
  Node nas = d_absValues.substituteAbstractValues(node);
  if (options::typeChecking())
  {
    // ensure node is type-checked at this point
    nas.getType(true);
  }
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  Node n = d_processor.expandDefinitions(nas, cache);
  Node ns = applySubstitutions(n);
  if (removeItes)
  {
    // also remove ites if asked
    ns = d_rtf.replace(ns);
  }
  return ns;
}

Node Preprocessor::applySubstitutions(TNode node)
{
  return Rewriter::rewrite(d_ppContext->getTopLevelSubstitutions().apply(node));
}

}  // namespace smt
}  // namespace CVC4
