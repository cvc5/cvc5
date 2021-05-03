/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term registry class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TERM_REGISTRY_H
#define CVC5__THEORY__QUANTIFIERS__TERM_REGISTRY_H

#include <map>
#include <unordered_set>

#include "context/cdhashset.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_pools.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

class FirstOrderModel;

/**
 * Term Registry, which manages notifying modules within quantifiers about
 * (ground) terms that exist in the current context.
 */
class TermRegistry
{
  using NodeSet = context::CDHashSet<Node, NodeHashFunction>;

 public:
  TermRegistry(QuantifiersState& qs,
               QuantifiersRegistry& qr);
  /** Finish init, which sets the inference manager on modules of this class */
  void finishInit(QuantifiersInferenceManager* qim);
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

  /** get term for type
   *
   * This returns an arbitrary term for type tn.
   * This term is chosen heuristically to be the best
   * term for instantiation. Currently, this
   * heuristic enumerates the first term of the
   * type if the type is closed enumerable, otherwise
   * an existing ground term from the term database if
   * one exists, or otherwise a fresh variable.
   */
  Node getTermForType(TypeNode tn);
  /**
   * Declare pool p with initial value initValue.
   */
  void declarePool(Node p, const std::vector<Node>& initValue);
  /**
   * Process instantiation
   */
  void processInstantiation(Node q, const std::vector<Node>& terms);
  void processSkolemization(Node q, const std::vector<Node>& skolems);

  /** Whether we use the full model check builder and corresponding model */
  bool useFmcModel() const;

  /** get term database */
  TermDb* getTermDatabase() const;
  /** get term database sygus */
  TermDbSygus* getTermDatabaseSygus() const;
  /** get term enumeration utility */
  TermEnumeration* getTermEnumeration() const;
  /** get the term pools utility */
  TermPools* getTermPools() const;
  /** get the model utility */
  FirstOrderModel* getModel() const;

 private:
  /** has presolve been called */
  context::CDO<bool> d_presolve;
  /** Whether we are using the fmc model */
  bool d_useFmcModel;
  /** the set of terms we have seen before presolve */
  NodeSet d_presolveCache;
  /** term enumeration utility */
  std::unique_ptr<TermEnumeration> d_termEnum;
  /** term enumeration utility */
  std::unique_ptr<TermPools> d_termPools;
  /** term database */
  std::unique_ptr<TermDb> d_termDb;
  /** sygus term database */
  std::unique_ptr<TermDbSygus> d_sygusTdb;
  /** extended model object */
  std::unique_ptr<FirstOrderModel> d_qmodel;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__TERM_REGISTRY_H */
