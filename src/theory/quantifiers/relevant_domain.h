/*********************                                                        */
/*! \file relevant_domain.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief relevant domain class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__RELEVANT_DOMAIN_H
#define __CVC4__THEORY__QUANTIFIERS__RELEVANT_DOMAIN_H

#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Relevant Domain
 *
 * This class computes the relevant domain of
 * functions and quantified formulas based on
 * techniques from "Complete Instantiation for Quantified
 * Formulas in SMT" by Ge et al., CAV 2009.
 *
 * Calling compute() will compute a representation
 * of relevant domain information, which be accessed
 * by getRDomain(...) calls. It is intended to be called
 * at full effort check, after we have initialized
 * the term database.
 */
class RelevantDomain : public QuantifiersUtil
{
 public:
  RelevantDomain(QuantifiersEngine* qe);
  virtual ~RelevantDomain();
  /** Reset. */
  bool reset(Theory::Effort e) override;
  /** Register the quantified formula q */
  void registerQuantifier(Node q) override;
  /** identify */
  std::string identify() const override { return "RelevantDomain"; }
  /** Compute the relevant domain */
  void compute();
  /** Relevant domain representation.
   *
   * This data structure is inspired by the paper
   * "Complete Instantiation for Quantified Formulas in SMT" by
   * Ge et al., CAV 2009.
   * Notice that relevant domains may be equated to one another,
   * for example, if the quantified formula forall x. P( x, x )
   * exists in the current context, then the relevant domain of
   * arguments 1 and 2 of P are equated.
   */
  class RDomain
  {
  public:
    RDomain() : d_parent( NULL ) {}
    /** the set of terms in this relevant domain */
    std::vector< Node > d_terms;
    /** reset this object */
    void reset()
    {
      d_parent = NULL;
      d_terms.clear();
    }
    /** merge this with r
     * This sets d_parent of this to r and
     * copies the terms of this to r.
     */
    void merge( RDomain * r );
    /** add term to the relevant domain */
    void addTerm( Node t );
    /** get the parent of this */
    RDomain * getParent();
    /** remove redundant terms for d_terms, removes
     * duplicates modulo equality.
     */
    void removeRedundantTerms( QuantifiersEngine * qe );
    /** is n in this relevant domain? */
    bool hasTerm( Node n ) { return std::find( d_terms.begin(), d_terms.end(), n )!=d_terms.end(); }

   private:
    /** the parent of this relevant domain */
    RDomain* d_parent;
  };
  /** get the relevant domain
   *
   * Gets object representing the relevant domain of the i^th argument of n.
   *
   * If getParent is true, we return the representative
   * of the equivalence class of relevant domain objects,
   * which is computed as a union find (see RDomain::d_parent).
   */
  RDomain* getRDomain(Node n, int i, bool getParent = true);

 private:
  /** the relevant domains for each quantified formula and function,
   * for each variable # and argument #.
   */
  std::map< Node, std::map< int, RDomain * > > d_rel_doms;
  /** stores the function or quantified formula associated with
   * each relevant domain object.
   */
  std::map< RDomain *, Node > d_rn_map;
  /** stores the argument or variable number associated with
   * each relevant domain object.
   */
  std::map< RDomain *, int > d_ri_map;
  /** Quantifiers engine associated with this utility. */
  QuantifiersEngine* d_qe;
  /** have we computed the relevant domain on this full effort check? */
  bool d_is_computed;
  /** relevant domain literal
   * Caches the effect of literals on the relevant domain.
   */
  class RDomainLit {
  public:
    RDomainLit() : d_merge(false){
      d_rd[0] = NULL;
      d_rd[1] = NULL;
    }
    ~RDomainLit(){}
    /** whether this literal forces the merge of two relevant domains */
    bool d_merge;
    /** the relevant domains that are merged as a result
     * of this literal
     */
    RDomain * d_rd[2];
    /** the terms that are added to
     * the relevant domain as a result of this literal
     */
    std::vector< Node > d_val;
  };
  /** Cache of the effect of literals on the relevant domain */
  std::map< bool, std::map< bool, std::map< Node, RDomainLit > > > d_rel_dom_lit;
  /** Compute the relevant domain for a subformula n of q,
   * whose polarity is given by hasPol/pol.
   */
  void computeRelevantDomain(Node q, Node n, bool hasPol, bool pol);
  /** Compute the relevant domain when the term n
   * is in a position to be included in relevant domain rf.
   */
  void computeRelevantDomainOpCh(RDomain* rf, Node n);
  /** compute relevant domain for literal.
   *
   * Updates the relevant domains based on a literal n in quantified
   * formula q whose polarity is given by hasPol/pol.
   */
  void computeRelevantDomainLit( Node q, bool hasPol, bool pol, Node n );
};/* class RelevantDomain */


}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__RELEVANT_DOMAIN_H */
