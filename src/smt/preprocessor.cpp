/*********************                                                        */
/*! \file preprocessor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessor of the SMT engine.
 **/

#include "smt/preprocessor.h"

#include "options/smt_options.h"
#include "printer/printer.h"
#include "smt/abstract_values.h"
#include "smt/assertions.h"
#include "smt/dump.h"
#include "smt/smt_engine.h"

using namespace CVC4::theory;
using namespace CVC4::kind;

namespace CVC4 {
namespace smt {

Preprocessor::Preprocessor(SmtEngine& smt,
                           context::UserContext* u,
                           AbstractValues& abs,
                           SmtEngineStatistics& stats)
    : d_context(u),
      d_smt(smt),
      d_absValues(abs),
      d_propagator(true, true),
      d_assertionsProcessed(u, false),
      d_exDefs(smt, *smt.getResourceManager(), stats),
      d_processor(smt, d_exDefs, *smt.getResourceManager(), stats),
      d_pnm(nullptr)
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
      &d_smt, &d_propagator, d_pnm));

  // initialize the preprocessing passes
  d_processor.finishInit(d_ppContext.get());
}

bool Preprocessor::process(Assertions& as)
{
  preprocessing::AssertionPipeline& ap = as.getAssertionPipeline();

  // should not be called if empty
  Assert(ap.size() != 0)
      << "Can only preprocess a non-empty list of assertions";

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
  bool noConflict = d_processor.apply(as);

  // now, post-process the assertions

  // if incremental, compute which variables are assigned
  if (options::incrementalSolving())
  {
    d_ppContext->recordSymbolsInAssertions(ap.ref());
  }

  // mark that we've processed assertions
  d_assertionsProcessed = true;

  return noConflict;
}

void Preprocessor::clearLearnedLiterals()
{
  d_propagator.getLearnedLiterals().clear();
}

void Preprocessor::cleanup() { d_processor.cleanup(); }

Node Preprocessor::expandDefinitions(const Node& n, bool expandOnly)
{
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  return d_exDefs.expandDefinitions(n, cache, expandOnly);
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
  return d_exDefs.expandDefinitions(n, cache, expandOnly);
}

Node Preprocessor::simplify(const Node& node)
{
  Trace("smt") << "SMT simplify(" << node << ")" << endl;
  if (Dump.isOn("benchmark"))
  {
    d_smt.getOutputManager().getPrinter().toStreamCmdSimplify(
        d_smt.getOutputManager().getDumpOut(), node);
  }
  Node nas = d_absValues.substituteAbstractValues(node);
  if (options::typeChecking())
  {
    // ensure node is type-checked at this point
    nas.getType(true);
  }
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  Node n = d_exDefs.expandDefinitions(nas, cache);
  TrustNode ts = d_ppContext->getTopLevelSubstitutions().apply(n);
  Node ns = ts.isNull() ? n : ts.getNode();
  return ns;
}

void Preprocessor::setProofGenerator(PreprocessProofGenerator* pppg)
{
  Assert(pppg != nullptr);
  d_pnm = pppg->getManager();
  d_exDefs.setProofNodeManager(d_pnm);
  d_propagator.setProof(d_pnm, d_context, pppg);
}

}  // namespace smt
}  // namespace CVC4
