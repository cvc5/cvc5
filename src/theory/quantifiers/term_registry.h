/*********************                                                        */
/*! \file term_registry.h
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

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__TERM_REGISTRY_H
#define CVC4__THEORY__QUANTIFIERS__TERM_REGISTRY_H

#include <map>
#include <unordered_set>

#include "context/cdhashset.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * Term Registry, which manages notifying modules within quantifiers about
 * (ground) terms that exist in the current context.
 */
class TermRegistry
{
  using NodeSet = context::CDHashSet<Node, NodeHashFunction>;

 public:
  TermRegistry(QuantifiersState& qs,
               QuantifiersInferenceManager& qim,
               QuantifiersRegistry& qr);
  /** Presolve */
  void presolve();

  /**
   * Add term n, which notifies the term database that the ground term n
   * exists in the current context.
   *
   * @param n the term to add
   * @param withinQuant whether n occurs within a quantified formula body
   */
  void addTerm(Node n, bool withinQuant = false);

  /** get term database */
  TermDb* getTermDatabase() const;
  /** get term database sygus */
  TermDbSygus* getTermDatabaseSygus() const;
  /** get term enumeration utility */
  TermEnumeration* getTermEnumeration() const;

 private:
  /** has presolve been called */
  context::CDO<bool> d_presolve;
  /** the set of terms we have seen before presolve */
  NodeSet d_presolveCache;
  /** term enumeration utility */
  std::unique_ptr<TermEnumeration> d_termEnum;
  /** term database */
  std::unique_ptr<TermDb> d_termDb;
  /** sygus term database */
  std::unique_ptr<TermDbSygus> d_sygusTdb;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__TERM_REGISTRY_H */
