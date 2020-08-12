/*********************                                                        */
/*! \file instantiate.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief instantiate
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H
#define CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H

#include <map>

#include "expr/node.h"
#include "theory/quantifiers/inst_match_trie.h"
#include "theory/quantifiers/quant_util.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class TermDb;
class TermUtil;

/** Instantiation rewriter
 *
 * This class is used for cases where instantiation lemmas can be rewritten by
 * external utilities. Examples of this include virtual term substitution and
 * nested quantifier elimination techniques.
 */
class InstantiationRewriter
{
 public:
  InstantiationRewriter() {}
  virtual ~InstantiationRewriter() {}

  /** rewrite instantiation
   *
   * The node inst is the instantiation of quantified formula q for terms.
   * This method returns the rewritten form of the instantiation.
   *
   * The flag doVts is whether we must apply virtual term substitution to the
   * instantiation.
   */
  virtual Node rewriteInstantiation(Node q,
                                    std::vector<Node>& terms,
                                    Node inst,
                                    bool doVts) = 0;
};

/** Instantiate
 *
 * This class is used for generating instantiation lemmas.  It maintains an
 * instantiation trie, which is represented by a different data structure
 * depending on whether incremental solving is enabled (see d_inst_match_trie
 * and d_c_inst_match_trie).
 *
 * Below, we say an instantiation lemma for q = forall x. F under substitution
 * { x -> t } is the formula:
 *   ( ~forall x. F V F * { x -> t } )
 * where * is application of substitution.
 *
 * Its main interface is ::addInstantiation(...), which is called by many of
 * the quantifiers modules, which enqueues instantiation lemmas in quantifiers
 * engine via calls to QuantifiersEngine::addLemma.
 *
 * It also has utilities for constructing instantiations, and interfaces for
 * getting the results of the instantiations produced during check-sat calls.
 */
class Instantiate : public QuantifiersUtil
{
  typedef context::CDHashMap<Node, uint32_t, NodeHashFunction> NodeUIntMap;

 public:
  Instantiate(QuantifiersEngine* qe, context::UserContext* u);
  ~Instantiate();

  /** reset */
  bool reset(Theory::Effort e) override;
  /** register quantifier */
  void registerQuantifier(Node q) override;
  /** identify */
  std::string identify() const override { return "Instantiate"; }
  /** check incomplete */
  bool checkComplete() override;

  //--------------------------------------rewrite objects
  /** add instantiation rewriter */
  void addRewriter(InstantiationRewriter* ir);
  /** notify flush lemmas
   *
   * This is called just before the quantifiers engine flushes its lemmas to
   * the output channel.
   */
  void notifyFlushLemmas();
  //--------------------------------------end rewrite objects

  /** do instantiation specified by m
   *
   * This function returns true if the instantiation lemma for quantified
   * formula q for the substitution specified by m is successfully enqueued
   * via a call to QuantifiersEngine::addLemma.
   *   mkRep : whether to take the representatives of the terms in the range of
   *           the substitution m,
   *   modEq : whether to check for duplication modulo equality in instantiation
   *           tries (for performance),
   *   doVts : whether we must apply virtual term substitution to the
   *           instantiation lemma.
   *
   * This call may fail if it can be determined that the instantiation is not
   * relevant or legal in the current context. This happens if:
   * (1) The substitution is not well-typed,
   * (2) The substitution involves terms whose instantiation level is above the
   *     allowed limit,
   * (3) The resulting instantiation is entailed in the current context using a
   *     fast entailment check (see TermDb::isEntailed),
   * (4) The range of the substitution is a duplicate of that of a previously
   *     added instantiation,
   * (5) The instantiation lemma is a duplicate of previously added lemma.
   *
   */
  bool addInstantiation(Node q,
                        InstMatch& m,
                        bool mkRep = false,
                        bool modEq = false,
                        bool doVts = false);
  /** add instantiation
   *
   * Same as above, but the substitution we are considering maps the variables
   * of q to the vector terms, in order.
   */
  bool addInstantiation(Node q,
                        std::vector<Node>& terms,
                        bool mkRep = false,
                        bool modEq = false,
                        bool doVts = false);
  /** remove pending instantiation
   *
   * Removes the instantiation lemma lem from the instantiation trie.
   */
  bool removeInstantiation(Node q, Node lem, std::vector<Node>& terms);
  /** record instantiation
   *
   * Explicitly record that q has been instantiated with terms. This is the
   * same as addInstantiation, but does not enqueue an instantiation lemma.
   */
  bool recordInstantiation(Node q,
                           std::vector<Node>& terms,
                           bool modEq = false,
                           bool addedLem = true);
  /** exists instantiation
   *
   * Returns true if and only if the instantiation already was added or
   * recorded by this class.
   *   modEq : whether to check for duplication modulo equality
   */
  bool existsInstantiation(Node q,
                           std::vector<Node>& terms,
                           bool modEq = false);
  //--------------------------------------general utilities
  /** get instantiation
   *
   * Returns the instantiation lemma for q under substitution { vars -> terms }.
   * doVts is whether to apply virtual term substitution to its body.
   */
  Node getInstantiation(Node q,
                        std::vector<Node>& vars,
                        std::vector<Node>& terms,
                        bool doVts = false);
  /** get instantiation
   *
   * Same as above, but with vars/terms specified by InstMatch m.
   */
  Node getInstantiation(Node q, InstMatch& m, bool doVts = false);
  /** get instantiation
   *
   * Same as above but with vars equal to the bound variables of q.
   */
  Node getInstantiation(Node q, std::vector<Node>& terms, bool doVts = false);
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
  //--------------------------------------end general utilities

  /**
   * Debug print, called once per instantiation round. This prints
   * instantiations added this round to trace inst-per-quant-round, if
   * applicable, and prints to out if the option debug-inst is enabled.
   */
  void debugPrint(std::ostream& out);
  /** debug print model, called once, before we terminate with sat/unknown. */
  void debugPrintModel();

  //--------------------------------------user-level interface utilities
  /** print instantiations
   *
   * Print all instantiations for all quantified formulas on out,
   * returns true if at least one instantiation was printed. The type of output
   * (list, num, etc.) is determined by printInstMode.
   */
  bool printInstantiations(std::ostream& out);
  /** get instantiated quantified formulas
   *
   * Get the list of quantified formulas that were instantiated in the current
   * user context, store them in qs.
   */
  void getInstantiatedQuantifiedFormulas(std::vector<Node>& qs);
  /** get instantiations
   *
   * Get the body of all instantiation lemmas added in the current user context
   * for quantified formula q, store them in insts.
   */
  void getInstantiations(Node q, std::vector<Node>& insts);
  /** get instantiations
   *
   * Get the body of all instantiation lemmas added in the current user context
   * for all quantified formulas stored in the domain of insts, store them in
   * the range of insts.
   */
  void getInstantiations(std::map<Node, std::vector<Node> >& insts);
  /** get instantiation term vectors
   *
   * Get term vectors corresponding to for all instantiations lemmas added in
   * the current user context for quantified formula q, store them in tvecs.
   */
  void getInstantiationTermVectors(Node q,
                                   std::vector<std::vector<Node> >& tvecs);
  /** get instantiation term vectors
   *
   * Get term vectors for all instantiations lemmas added in the current user
   * context for quantified formula q, store them in tvecs.
   */
  void getInstantiationTermVectors(
      std::map<Node, std::vector<std::vector<Node> > >& insts);
  /** get instantiated conjunction
   *
   * This gets a conjunction of the bodies of instantiation lemmas added in the
   * current user context for quantified formula q.  For example, if we added:
   *   ~forall x. P( x ) V P( a )
   *   ~forall x. P( x ) V P( b )
   * Then, this method returns P( a ) ^ P( b ).
   */
  Node getInstantiatedConjunction(Node q);
  /** get unsat core lemmas
   *
   * If this method returns true, then it appends to active_lemmas all lemmas
   * that are in the unsat core that originated from the theory of quantifiers.
   * This method returns false if the unsat core is not available.
   */
  bool getUnsatCoreLemmas(std::vector<Node>& active_lemmas);
  /** get unsat core lemmas
   *
   * If this method returns true, then it appends to active_lemmas all lemmas
   * that are in the unsat core that originated from the theory of quantifiers.
   * This method returns false if the unsat core is not available.
   *
   * It also computes a weak implicant for each of these lemmas. For each lemma
   * L in active_lemmas, this is a formula L' such that:
   *   L => L'
   * and replacing L by L' in the unsat core results in a set that is still
   * unsatisfiable. The map weak_imp stores this formula for each formula in
   * active_lemmas.
   */
  bool getUnsatCoreLemmas(std::vector<Node>& active_lemmas,
                          std::map<Node, Node>& weak_imp);
  /** get explanation for instantiation lemmas
   *
   *
   */
  void getExplanationForInstLemmas(const std::vector<Node>& lems,
                                   std::map<Node, Node>& quant,
                                   std::map<Node, std::vector<Node> >& tvec);
  //--------------------------------------end user-level interface utilities

  /** statistics class
   *
   * This tracks statistics on the number of instantiations successfully
   * enqueued on the quantifiers output channel, and the number of redundant
   * instantiations encountered by various criteria.
   */
  class Statistics
  {
   public:
    IntStat d_instantiations;
    IntStat d_inst_duplicate;
    IntStat d_inst_duplicate_eq;
    IntStat d_inst_duplicate_ent;
    Statistics();
    ~Statistics();
  }; /* class Instantiate::Statistics */
  Statistics d_statistics;

 private:
  /** record instantiation, return true if it was not a duplicate
   *
   * addedLem : whether an instantiation lemma was added for the vector we are
   *            recording. If this is false, we bookkeep the vector.
   * modEq : whether to check for duplication modulo equality in instantiation
   *         tries (for performance),
   */
  bool recordInstantiationInternal(Node q,
                                   std::vector<Node>& terms,
                                   bool modEq = false,
                                   bool addedLem = true);
  /** remove instantiation from the cache */
  bool removeInstantiationInternal(Node q, std::vector<Node>& terms);
  /**
   * Ensure that n has type tn, return a term equivalent to it for that type
   * if possible.
   */
  static Node ensureType(Node n, TypeNode tn);
  /** print instantiations in list format */
  bool printInstantiationsList(std::ostream& out);
  /** print instantiations in num format */
  bool printInstantiationsNum(std::ostream& out);
  /**
   * Print quantified formula q on output out. If isFull is false, then we print
   * the identifier of the quantified formula if it has one, or print
   * nothing and return false otherwise.
   */
  bool printQuant(Node q, std::ostream& out, bool isFull);

  /** pointer to the quantifiers engine */
  QuantifiersEngine* d_qe;
  /** cache of term database for quantifiers engine */
  TermDb* d_term_db;
  /** cache of term util for quantifiers engine */
  TermUtil* d_term_util;
  /** instantiation rewriter classes */
  std::vector<InstantiationRewriter*> d_instRewrite;

  /** statistics for debugging total instantiations per quantifier */
  NodeUIntMap d_total_inst_debug;
  /** statistics for debugging total instantiations per quantifier per round */
  std::map<Node, uint32_t> d_temp_inst_debug;

  /** list of all instantiations produced for each quantifier
   *
   * We store context (dependent, independent) versions. If incremental solving
   * is disabled, we use d_inst_match_trie for performance reasons.
   */
  std::map<Node, inst::InstMatchTrie> d_inst_match_trie;
  std::map<Node, inst::CDInstMatchTrie*> d_c_inst_match_trie;
  /**
   * The list of quantified formulas for which the domain of d_c_inst_match_trie
   * is valid.
   */
  context::CDHashSet<Node, NodeHashFunction> d_c_inst_match_trie_dom;

  /** explicitly recorded instantiations
   *
   * Sometimes an instantiation is recorded internally but not sent out as a
   * lemma, for instance, for partial quantifier elimination. This is a map
   * of these instantiations, for each quantified formula.
   */
  std::vector<std::pair<Node, std::vector<Node> > > d_recorded_inst;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H */
