/*********************                                                        */
/*! \file term_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term registry class
 **/

#include "theory/quantifiers/term_registry.h"

#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "theory/quantifiers/quantifiers_state.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

TermRegistry::TermRegistry(QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersRegistry& qr)
    : d_presolve(qs.getUserContext(), true),
      d_presolveCache(qs.getUserContext()),
      d_termEnum(new TermEnumeration),
      d_termDb(new TermDb(qs, qim, qr)),
      d_sygusTdb(nullptr)
{
  if (options::sygus() || options::sygusInst())
  {
    // must be constructed here since it is required for datatypes finistInit
    d_sygusTdb.reset(new TermDbSygus(qs, qim));
  }
}

void TermRegistry::presolve()
{
  d_termDb->presolve();
  d_presolve = false;
  // add all terms to database
  if (options::incrementalSolving() && !options::termDbCd())
  {
    Trace("quant-engine-proc")
        << "Add presolve cache " << d_presolveCache.size() << std::endl;
    for (const Node& t : d_presolveCache)
    {
      addTerm(t);
    }
    Trace("quant-engine-proc") << "Done add presolve cache " << std::endl;
  }
}

void TermRegistry::addTerm(Node n, bool withinQuant)
{
  // don't add terms in quantifier bodies
  if (withinQuant && !options::registerQuantBodyTerms())
  {
    return;
  }
  if (options::incrementalSolving() && !options::termDbCd())
  {
    d_presolveCache.insert(n);
  }
  // only wait if we are doing incremental solving
  if (!d_presolve || !options::incrementalSolving() || options::termDbCd())
  {
    d_termDb->addTerm(n);
    if (d_sygusTdb.get() && options::sygusEvalUnfold())
    {
      d_sygusTdb->getEvalUnfold()->registerEvalTerm(n);
    }
  }
}

TermDb* TermRegistry::getTermDatabase() const { return d_termDb.get(); }

TermDbSygus* TermRegistry::getTermDatabaseSygus() const
{
  return d_sygusTdb.get();
}

TermEnumeration* TermRegistry::getTermEnumeration() const
{
  return d_termEnum.get();
}
}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
