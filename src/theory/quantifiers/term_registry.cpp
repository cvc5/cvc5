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

namespace CVC4 {
namespace theory {
namespace quantifiers {

TermRegistry::TermRegistry(QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersRegistry& qr) : 
                           d_termEnum(),
      d_termDb(qs, qim, qr)
      
{
  if (options::sygus() || options::sygusInst())
  {
    // must be constructed here since it is required for datatypes finistInit
    d_sygusTdb.reset(new quantifiers::TermDbSygus(qstate, qim));
  }
}

void TermRegistry::presolve()
{
  d_termDb.presolve();
  d_presolve = false;
  //add all terms to database
  if (options::incrementalSolving() && !options::termDbCd())
  {
    Trace("quant-engine-proc") << "Add presolve cache " << d_presolve_cache.size() << std::endl;
    for (const Node& t : d_presolve_cache)
    {
      addTermToDatabase(t);
    }
    Trace("quant-engine-proc") << "Done add presolve cache " << std::endl;
  }
}
  
void TermRegistry::addTerm(Node n, bool withinQuant) {
  // don't add terms in quantifier bodies
  if (withinQuant && !options::registerQuantBodyTerms())
  {
    return;
  }
  if (options::incrementalSolving() && !options::termDbCd())
  {
    if( d_presolve_in.find( n )==d_presolve_in.end() ){
      d_presolve_in.insert( n );
      d_presolve_cache.push_back( n );
    }
  }
  //only wait if we are doing incremental solving
  if (!d_presolve || !options::incrementalSolving() || options::termDbCd())
  {
    d_termDb.addTerm(n);
    if (d_sygusTdb.get() && options::sygusEvalUnfold())
    {
      d_sygusTdb->getEvalUnfold()->registerEvalTerm(n);
    }
  }
}

TermDb* TermRegistry::getTermDatabase() const
{
  return &d_termDb;
}

TermDbSygus* TermRegistry::getTermDatabaseSygus() const
{
  return d_sygusTdb.get();
}

TermEnumeration* TermRegistry::getTermEnumeration() const
{
  return &d_termEnum;
}
}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
