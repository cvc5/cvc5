/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory uf candidate generator.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CANDIDATE_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__CANDIDATE_GENERATOR_H

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class TermRegistry;

namespace inst {

/** Candidate generator
 *
 * This is the base class for generating a stream of candidate terms for
 * E-matching. Depending on the kind of trigger we are processing and its
 * overall context, we are interested in several different criteria for
 * terms. This includes:
 * - Generating a stream of all ground terms with a given operator,
 * - Generating a stream of all ground terms with a given operator in a
 * particular equivalence class,
 * - Generating a stream of all terms of a particular type,
 * - Generating all terms that are disequal from a fixed ground term,
 * and so on.
 *
 * A typical use case of an instance cg of this class is the following. Given
 * an equivalence class representative eqc:
 *
 *  cg->reset( eqc );
 *  do{
 *    Node cand = cg->getNextCandidate();
 *    ; ...if non-null, cand is a candidate...
 *  }while( !cand.isNull() );
 *
 */
class CandidateGenerator {
 public:
  CandidateGenerator(QuantifiersState& qs, TermRegistry& tr);
  virtual ~CandidateGenerator(){}
  /** reset instantiation round
   *
   * This is called at the beginning of each instantiation round.
   */
  virtual void resetInstantiationRound() {}
  /** reset for equivalence class eqc
   *
   * This indicates that this class should generate a stream of candidate terms
   * based on its criteria that occur in the equivalence class of eqc, or
   * any equivalence class if eqc is null.
   */
  virtual void reset( Node eqc ) = 0;
  /** get the next candidate */
  virtual Node getNextCandidate() = 0;
  /** is n a legal candidate? */
  bool isLegalCandidate(Node n);

 protected:
  /** Reference to the quantifiers state */
  QuantifiersState& d_qs;
  /** Reference to the term registry */
  TermRegistry& d_treg;
};

/* the default candidate generator class
 *
 * This class may generate candidates for E-matching based on several modes:
 * (1) cand_term_db: iterate over all ground terms for the given operator,
 * (2) cand_term_ident: generate the given input term as a candidate,
 * (3) cand_term_eqc: iterate over all terms in an equivalence class, returning
 * those with the proper operator as candidates.
 */
class CandidateGeneratorQE : public CandidateGenerator
{
  friend class CandidateGeneratorQEDisequal;

 public:
  CandidateGeneratorQE(QuantifiersState& qs, TermRegistry& tr, Node pat);
  /** reset */
  void reset(Node eqc) override;
  /** get next candidate */
  Node getNextCandidate() override;
  /** tell this class to exclude candidates from equivalence class r */
  void excludeEqc(Node r) { d_exclude_eqc[r] = true; }
  /** is r an excluded equivalence class? */
  bool isExcludedEqc(Node r)
  {
    return d_exclude_eqc.find(r) != d_exclude_eqc.end();
  }
 protected:
  /** reset this class for matching operator op in equivalence class eqc */
  void resetForOperator(Node eqc, Node op);
  /** the default implementation of getNextCandidate. */
  Node getNextCandidateInternal();
  /** operator you are looking for */
  Node d_op;
  /** the equality class iterator (for cand_term_eqc) */
  eq::EqClassIterator d_eqc_iter;
  /** the TermDb index of the current ground term (for cand_term_db) */
  int d_term_iter;
  /** the TermDb index of the current ground term (for cand_term_db) */
  int d_term_iter_limit;
  /** the current equivalence class */
  Node d_eqc;
  /** candidate generation modes */
  enum {
    cand_term_db,
    cand_term_ident,
    cand_term_eqc,
    cand_term_none,
  };
  /** the current mode of this candidate generator */
  short d_mode;
  /** is n a legal candidate of the required operator? */
  virtual bool isLegalOpCandidate(Node n);
  /** the equivalence classes that we have excluded from candidate generation */
  std::map< Node, bool > d_exclude_eqc;

};

/**
 * Generate terms based on a disequality, that is, we match (= t[x] s[x])
 * with equalities (= g1 g2) in the equivalence class of false.
 */
class CandidateGeneratorQELitDeq : public CandidateGenerator
{
 public:
  /**
   * mpat is an equality that we are matching to equalities in the equivalence
   * class of false
   */
  CandidateGeneratorQELitDeq(QuantifiersState& qs, TermRegistry& tr, Node mpat);
  /** reset */
  void reset(Node eqc) override;
  /** get next candidate */
  Node getNextCandidate() override;

 private:
  /** the equality class iterator for false */
  eq::EqClassIterator d_eqc_false;
  /**
   * equality you are trying to match against ground equalities that are
   * assigned to false
   */
  Node d_match_pattern;
  /** type of the terms we are generating */
  TypeNode d_match_pattern_type;
};

/**
 * Generate all terms of the proper sort that occur in the current context.
 */
class CandidateGeneratorQEAll : public CandidateGenerator
{
 private:
  //the equality classes iterator
  eq::EqClassesIterator d_eq;
  //equality you are trying to match equalities for
  Node d_match_pattern;
  TypeNode d_match_pattern_type;
  // quantifier/index for the variable we are matching
  Node d_f;
  unsigned d_index;
  //first time
  bool d_firstTime;

 public:
  CandidateGeneratorQEAll(QuantifiersState& qs, TermRegistry& tr, Node mpat);
  /** reset */
  void reset(Node eqc) override;
  /** get next candidate */
  Node getNextCandidate() override;
};

/** candidate generation constructor expand
 *
 * This modifies the candidates t1, ..., tn generated by CandidateGeneratorQE
 * so that they are "expansions" of a fixed datatype constructor C. Assuming
 * C has arity m, we instead return the stream:
 *   C(sel_1( t1 ), ..., sel_m( tn )) ... C(sel_1( t1 ), ..., C( sel_m( tn ))
 * where sel_1 ... sel_m are the selectors of C.
 */
class CandidateGeneratorConsExpand : public CandidateGeneratorQE
{
 public:
  CandidateGeneratorConsExpand(QuantifiersState& qs,
                               TermRegistry& tr,
                               Node mpat);
  /** reset */
  void reset(Node eqc) override;
  /** get next candidate */
  Node getNextCandidate() override;

 protected:
  /** the (datatype) type of the input match pattern */
  TypeNode d_mpat_type;
  /** we don't care about the operator of n */
  bool isLegalOpCandidate(Node n) override;
};

/**
 * Candidate generator for selector applications, which considers both
 * internal terms corresponding to correctly and incorrectly applied selectors.
 */
class CandidateGeneratorSelector : public CandidateGeneratorQE
{
 public:
  CandidateGeneratorSelector(QuantifiersState& qs, TermRegistry& tr, Node mpat);
  /** reset */
  void reset(Node eqc) override;
  /**
   * Get next candidate, returns matching candidates that are ground terms
   * of the selector operator, followed by those that are applications of the
   * UF corresponding to an invocation of applying this selector to an
   * application of the wrong constructor.
   */
  Node getNextCandidate() override;
 protected:
  /** the selector operator */
  Node d_selOp;
  /** the UF operator */
  Node d_ufOp;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__CANDIDATE_GENERATOR_H */
