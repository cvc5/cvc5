/*********************                                                        */
/*! \file sygus_module.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_module
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_MODULE_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_MODULE_H

#include <map>
#include "expr/node.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class CegConjecture;

/** SygusModule
 *
 * This is the base class of sygus modules, owned by CegConjecture. The purpose
 * of this class is to, when applicable, suggest candidate solutions for
 * CegConjecture to test.
 *
 * In more detail, an instance of the conjecture class (CegConjecture) creates
 * the negated deep embedding form of the synthesis conjecture. In the
 * following, assume this is:
 *   forall d. exists x. P( d, x )
 * where d are of sygus datatype type. The "base instantiation" of this
 * conjecture (see CegConjecture::d_base_inst) is the formula:
 *   exists y. P( k, y )
 * where k are the "candidate" variables for the conjecture.
 *
 * Modules implement an initialize function, which determines whether the module
 * will take responsibility for the given conjecture.
 */
class SygusModule
{
 public:
  SygusModule(QuantifiersEngine* qe, CegConjecture* p);
  ~SygusModule() {}
  /** initialize
   *
   * n is the "base instantiation" of the deep-embedding version of the
   * synthesis conjecture under candidates (see CegConjecture::d_base_inst).
   *
   * This function may add lemmas to the argument lemmas, which should be
   * sent out on the output channel of quantifiers by the caller.
   *
   * This function returns true if this module will take responsibility for
   * constructing candidates for the given conjecture.
   */
  virtual bool initialize(Node n,
                          const std::vector<Node>& candidates,
                          std::vector<Node>& lemmas) = 0;
  /** get term list
   *
   * This gets the list of terms that will appear as arguments to a subsequent
   * call to constructCandidates.
   */
  virtual void getTermList(const std::vector<Node>& candidates,
                           std::vector<Node>& terms) = 0;
  /** construct candidate
   *
   * This function takes as input:
   *   terms : the terms returned by a call to getTermList,
   *   term_values : the current model values of terms,
   *   candidates : the list of candidates.
   *
   * If this function returns true, it adds to candidate_values a list of terms
   * of the same length and type as candidates that are candidate solutions
   * to the synthesis conjecture in question. This candidate { v } will then be
   * tested by testing the (un)satisfiablity of P( v, k' ) for fresh k' by the
   * caller.
   *
   * This function may also add lemmas to lems, which are sent out as lemmas
   * on the output channel of quantifiers by the caller. For an example of
   * such lemmas, see SygusPbe::constructCandidates.
   *
   * This function may return false if it does not have a candidate it wants
   * to test on this iteration. In this case, lems should be non-empty.
   */
  virtual bool constructCandidates(const std::vector<Node>& terms,
                                   const std::vector<Node>& term_values,
                                   const std::vector<Node>& candidates,
                                   std::vector<Node>& candidate_values,
                                   std::vector<Node>& lems) = 0;
  /** register refinement lemma
   *
   * Assume this module, on a previous call to constructCandidates, added the
   * value { v } to candidate_values for candidates = { k }. This function is
   * called if the base instantiation of the synthesis conjecture has a model
   * under this substitution. In particular, in the above example, this function
   * is called when the refinement lemma P( v, k' ) has a model. The argument
   * lem in the call to this function is P( v, k' ).
   */
  virtual void registerRefinementLemma(Node lem) {}
 protected:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** reference to the parent conjecture */
  CegConjecture* d_parent;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_MODULE_H */
