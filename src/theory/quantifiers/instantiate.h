/*********************                                                        */
/*! \file instantiate.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief instantiate
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H
#define __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H

#include <map>

#include "expr/node.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/quant_util.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermDb;
class TermUtil;

/** instantiation notify 
 * 
 * This class is a listener for all instantiations generated with quantifiers.
 * No instances of notify classes are enabled by default in CVC4.
 */
class InstantiationNotify {
public:
  InstantiationNotify(){}
  virtual ~InstantiationNotify() {}
  /** notify instantiation  
   * 
   * This is called when an instantiation of quantified formula q is 
   * instantiated by a substitution whose range is terms at quantifier effort 
   * quant_e. Furthermore:
   *   body is the substituted, preprocessed body of the quantified formula,
   *   lem is the instantiation lemma ( ~q V body ) after rewriting.
   */
  virtual bool notifyInstantiation(QuantifiersModule::QEffort quant_e,
                                   Node q,
                                   Node lem,
                                   std::vector<Node>& terms,
                                   Node body) = 0;
  /** filter instantiations 
   * 
   * This is called just before the quantifiers engine flushes its lemmas to the
   * output channel. During this call, the instantiation notify object may
   * call, e.g. QuantifiersEngine::getInstantiate()->removeInstantiation
   * to remove instantiations that should not be sent on the output channel.
   */
  virtual void filterInstantiations() = 0;
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
 * getting the results of 
 */
class Instantiate : public QuantifiersUtil
{
public:
  Instantiate( QuantifiersEngine * qe, context::UserContext* u );
  ~Instantiate();
  
  /** reset */
  virtual bool reset(Theory::Effort e) override;
  /** register quantifier */
  virtual void registerQuantifier(Node q) override;
  /** identify */
  virtual std::string identify() const override { return "Instantiate"; }
  /** check incomplete */
  virtual bool checkComplete() override;
  
  /** add instantiation notify */
  void addNotify( InstantiationNotify* in );
  /** get num instantiation notify */
  bool hasNotify() const { return !d_inst_notify.empty(); }
  /** notify flush lemmas */
  void notifyFlushLemmas();
  
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
  bool addInstantiation( Node q, InstMatch& m, bool mkRep = false, bool modEq = false, bool doVts = false );
  /** add instantiation 
   * 
   * Same as above, but the substitution we are considering maps the variables 
   * of q to the vector terms, in order.
   */
  bool addInstantiation( Node q, std::vector< Node >& terms, bool mkRep = false, bool modEq = false, bool doVts = false );
  /** remove pending instantiation 
   * 
   * Removes the instantiation lemma lem from the instantiation trie.
   */
  bool removeInstantiation( Node q, Node lem, std::vector< Node >& terms );
  /** record instantiation 
   * 
   * Explicitly record that q has been instantiated with terms.
   * This is the same as addInstantiation, but does not enqueue an instantiation
   * lemma.
   */
  bool recordInstantiation( Node q, std::vector< Node >& terms, bool modEq = false, bool addedLem = true );
  
  //--------------------------------------general utilities
  /** get instantiation 
   * 
   * Returns the instantiation lemma for q under substitution { vars -> terms }.
   * doVts is whether to apply virtual term substitution to its body.
   */
  Node getInstantiation( Node q, std::vector< Node >& vars, std::vector< Node >& terms, bool doVts = false );
  /** get instantiation 
   * 
   * Same as above, but with vars/terms specified by InstMatch m.
   */
  Node getInstantiation( Node q, InstMatch& m, bool doVts = false );
  /** get instantiation 
   * 
   * Same as above but with vars equal to the bound variables of q.
   */
  Node getInstantiation( Node q, std::vector< Node >& terms, bool doVts = false );
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
  
  /** debug print, called once per instantiation round. */
  void debugPrint();
  /** debug print model, called once, before we terminate with sat/unknown. */
  void debugPrintModel();
  
  //--------------------------------------user-level interface utilities
  /** print instantiations
   * 
   * Print all instantiations for all quantified formulas on out,
   * returns true if at least one instantiation was printed.
   */
  bool printInstantiations( std::ostream& out );  
  /** get instantiated quantified formulas 
   *
   * Get the list of quantified formulas that were instantiated in the current 
   * user context, store them in qs. 
   */
  void getInstantiatedQuantifiedFormulas( std::vector< Node >& qs );
  /** get instantiations 
   *
   * Get all instantiation lemmas added in the current user context for 
   * quantified formula q, store them in insts.
   */
  void getInstantiations( Node q, std::vector< Node >& insts );
  /** get instantiations 
   * 
   * Get all instantiation lemmas added in the current user context for all 
   * quantified formulas stored in the domain of insts, store them in the range 
   * of insts.
   */
  void getInstantiations( std::map< Node, std::vector< Node > >& insts );
  /** get instantiation term vectors 
   * 
   * Get term vectors corresponding to for all instantiations lemmas added in 
   * the current user context for quantified formula q, store them in tvecs.
   */
  void getInstantiationTermVectors( Node q, std::vector< std::vector< Node > >& tvecs );
  /** get instantiation term vectors 
   * 
   * Get term vectors for all instantiations lemmas added in the current user 
   * context for quantified formula q, store them in tvecs.
   */
  void getInstantiationTermVectors( std::map< Node, std::vector< std::vector< Node > > >& insts );
  /** get instantiated conjunction */
  Node getInstantiatedConjunction( Node q );
  /** get unsat core lemmas */
  bool getUnsatCoreLemmas( std::vector< Node >& active_lemmas );
  bool getUnsatCoreLemmas( std::vector< Node >& active_lemmas, std::map< Node, Node >& weak_imp );
  /** get inst for lemmas */
  void getExplanationForInstLemmas( std::vector< Node >& lems, std::map< Node, Node >& quant, std::map< Node, std::vector< Node > >& tvec ); 
  //--------------------------------------end user-level interface utilities
  
  /** statistics class */
  class Statistics {
  public:
    IntStat d_instantiations;
    IntStat d_inst_duplicate;
    IntStat d_inst_duplicate_eq;
    IntStat d_inst_duplicate_ent;
    IntStat d_inst_duplicate_model_true;
    Statistics();
    ~Statistics();
  };/* class Instantiate::Statistics */
  Statistics d_statistics;
private:
  /** compute term vector
   * 
   */
  void computeTermVector( Node q, InstMatch& m, std::vector< Node >& vars, std::vector< Node >& terms );
  /** record instantiation, return true if it was not a duplicate */
  bool recordInstantiationInternal( Node q, std::vector< Node >& terms, bool modEq = false, bool addedLem = true );
  /** remove instantiation from the cache */
  bool removeInstantiationInternal( Node q, std::vector< Node >& terms );

  /** pointer to the quantifiers engine */
  QuantifiersEngine * d_qe;
  /** cache of term database for quantifiers engine */
  TermDb * d_term_db;
  /** cache of term util for quantifiers engine */
  TermUtil * d_term_util;
  /** instantiation notify classes */
  std::vector< InstantiationNotify* > d_inst_notify;
  
  /** statistics for debugging total instantiation */
  int d_total_inst_count_debug;
  /** statistics for debugging total instantiations per quantifier */
  std::map< Node, int > d_total_inst_debug;
  /** statistics for debugging total instantiations per quantifier per round */
  std::map< Node, int > d_temp_inst_debug;
  
  /** list of all instantiations produced for each quantifier 
   * 
   * We store context (dependent, independent) versions. Depending on whether
   * incremental solving is enabled, we use one or the other.
   */
  std::map< Node, inst::InstMatchTrie > d_inst_match_trie;
  std::map< Node, inst::CDInstMatchTrie* > d_c_inst_match_trie;
  
  /** explicitly recorded instantiations 
   * 
   * Sometimes an instantiation is recorded internally but not sent out as a
   * lemma, for instance, for partial quantifier elimination. This is a map
   * of these instantiations, for each quantified formula.
   */
  std::vector< std::pair< Node, std::vector< Node > > > d_recorded_inst;
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATE_H */
