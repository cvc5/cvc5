/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "smt/env_obj.h"
#include "theory/quantifiers/bv_inverter.h"
#include "theory/quantifiers/cegqi/vts_term_cache.h"
#include "theory/quantifiers/entailment_check.h"
#include "theory/quantifiers/ieval/inst_evaluator_manager.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_pools.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class FirstOrderModel;
class OracleChecker;

/**
 * Term Registry, which manages notifying modules within quantifiers about
 * (ground) terms that exist in the current context.
 */
class TermRegistry : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  TermRegistry(Env& env, QuantifiersState& qs, QuantifiersRegistry& qr);
  /** Finish init, which sets the inference manager on modules of this class */
  void finishInit(FirstOrderModel* fm, QuantifiersInferenceManager* qim);
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
  /** Get terms for pool p, adds them to the vector terms. */
  void getTermsForPool(Node p, std::vector<Node>& terms);
  /**
   * Declare pool p with initial value initValue.
   */
  void declarePool(Node p, const std::vector<Node>& initValue);
  /**
   * Process instantiation, called when q is instantiated.
   *
   * @param q The quantified formula
   * @param terms The terms it was instantiated with
   * @param success Whether the instantiation was successfully added
   */
  void processInstantiation(Node q,
                            const std::vector<Node>& terms,
                            bool success);
  /**
   * Process skolemization, called when q is skolemized.
   *
   * @param q The quantified formula
   * @param skolems The skolem variables used for skolemizing q
   */
  void processSkolemization(Node q, const std::vector<Node>& skolems);

  /** get term database */
  TermDb* getTermDatabase() const;
  /** get term database sygus */
  TermDbSygus* getTermDatabaseSygus() const;
  /** get oracle checker */
  OracleChecker* getOracleChecker() const;
  /** get entailment check utility */
  EntailmentCheck* getEntailmentCheck() const;
  /** get term enumeration utility */
  TermEnumeration* getTermEnumeration() const;
  /** get the term pools utility */
  TermPools* getTermPools() const;
  /** get the virtual term substitution term cache utility */
  VtsTermCache* getVtsTermCache() const;
  /** get the bv inverter utility */
  BvInverter* getBvInverter() const;
  /** get the instantiation evaluator manager */
  ieval::InstEvaluatorManager* getInstEvaluatorManager() const;
  /**
   * Get evaluator for quantified formula q and evaluator mode tev. We require
   * that an evaluator is only used by one user at a time. The user of an
   * evaluator has the responsibility to ensure it is cleaned (via a soft
   * resetAll or push) when it is finished using it.
   *
   * Note the returned inst evaluator can be assumed to be watching quantified
   * formula q only. It may or may not be initialized (i.e. such that the
   * evaluation of ground terms is already computed), although the InstEvaluator
   * interface automatically manages this initialization internally.
   */
  ieval::InstEvaluator* getEvaluator(Node q, ieval::TermEvaluatorMode tev);
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
  /** entailment check */
  std::unique_ptr<EntailmentCheck> d_echeck;
  /** sygus term database */
  std::unique_ptr<TermDbSygus> d_sygusTdb;
  /** oracle checker */
  std::unique_ptr<OracleChecker> d_ochecker;
  /** virtual term substitution term cache for arithmetic instantiation */
  std::unique_ptr<VtsTermCache> d_vtsCache;
  /** the instantiation evaluator manager */
  std::unique_ptr<ieval::InstEvaluatorManager> d_ievalMan;
  /** inversion utility for BV instantiation */
  std::unique_ptr<BvInverter> d_bvInvert;
  /** extended model object */
  FirstOrderModel* d_qmodel;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__TERM_REGISTRY_H */
