/*********************                                                        */
/*! \file sygus_module.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_module
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_MODULE_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_MODULE_H

#include <map>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class SynthConjecture;
class TermDbSygus;

/** SygusModule
 *
 * This is the base class of sygus modules, owned by SynthConjecture. The
 * purpose of this class is to, when applicable, suggest candidate solutions for
 * SynthConjecture to test.
 *
 * In more detail, an instance of the conjecture class (SynthConjecture) creates
 * the negated deep embedding form of the synthesis conjecture. In the
 * following, assume this is:
 *   forall d. exists x. P( d, x )
 * where d are of sygus datatype type. The "base instantiation" of this
 * conjecture (see SynthConjecture::d_base_inst) is the formula:
 *   exists y. P( k, y )
 * where k are the "candidate" variables for the conjecture.
 *
 * Modules implement an initialize function, which determines whether the module
 * will take responsibility for the given conjecture.
 */
class SygusModule
{
 public:
  SygusModule(QuantifiersEngine* qe, SynthConjecture* p);
  virtual ~SygusModule() {}
  /** initialize
   *
   * This function initializes the module for solving the given conjecture. This
   * typically involves registering enumerators (for constructing terms) via
   * calls to TermDbSygus::registerEnumerator.
   *
   * This function returns true if this module will take responsibility for
   * constructing candidates for the given conjecture.
   *
   * conj is the synthesis conjecture (prior to deep-embedding).
   *
   * n is the "base instantiation" of the deep-embedding version of the
   * synthesis conjecture under candidates (see SynthConjecture::d_base_inst).
   *
   * This function may add lemmas to the argument lemmas, which should be
   * sent out on the output channel of quantifiers by the caller.
   */
  virtual bool initialize(Node conj,
                          Node n,
                          const std::vector<Node>& candidates,
                          std::vector<Node>& lemmas) = 0;
  /** get term list
   *
   * This gets the list of terms that will appear as arguments to a subsequent
   * call to constructCandidates.
   */
  virtual void getTermList(const std::vector<Node>& candidates,
                           std::vector<Node>& terms) = 0;
  /** allow partial model
   *
   * This method returns true if this module does not require that all
   * terms returned by getTermList have "proper" model values when calling
   * constructCandidates. A term may have a model value that is not proper
   * if is excluded by symmetry breaking, e.g. x+0 is not proper. All model
   * values that are not proper are replaced by "null" when calling
   * constructCandidates.
   */
  virtual bool allowPartialModel() { return false; }
  /** construct candidate
   *
   * This function takes as input:
   *   terms : (a subset of) the terms returned by a call to getTermList,
   *   term_values : the current model values of terms,
   *   candidates : the list of candidates.
   *
   * In particular, notice that terms do not include inactive enumerators,
   * thus if inactive enumerators were added to getTermList, then the terms
   * list passed to this call will be a (strict) subset of that list.
   *
   * If this function returns true, it adds to candidate_values a list of terms
   * of the same length and type as candidates that are candidate solutions
   * to the synthesis conjecture in question. This candidate { v } will then be
   * tested by testing the (un)satisfiablity of P( v, cex ) for fresh cex by the
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
   * is called when the refinement lemma P( v, cex ) has a model M. In calls to
   * this function, the argument vars is cex and lem is P( k, cex^M ).
   *
   * This function may also add lemmas to lems, which are sent out as lemmas
   * on the output channel of quantifiers by the caller. For an example of
   * such lemmas, see Cegis::registerRefinementLemma.
   */
  virtual void registerRefinementLemma(const std::vector<Node>& vars,
                                       Node lem,
                                       std::vector<Node>& lems)
  {
  }
  /**
   * Are we trying to repair constants in candidate solutions?
   * If we return true for usingRepairConst is true, then this module has
   * attmepted to repair any solutions returned by constructCandidates.
   */
  virtual bool usingRepairConst() { return false; }

 protected:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** sygus term database of d_qe */
  quantifiers::TermDbSygus* d_tds;
  /** reference to the parent conjecture */
  SynthConjecture* d_parent;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_MODULE_H */
