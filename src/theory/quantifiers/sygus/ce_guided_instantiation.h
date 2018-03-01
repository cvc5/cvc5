/*********************                                                        */
/*! \file ce_guided_instantiation.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_INSTANTIATION_H
#define __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_INSTANTIATION_H

#include "context/cdhashmap.h"
#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class CegInstantiation : public QuantifiersModule
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
private:
  /** the quantified formula stating the synthesis conjecture */
  CegConjecture * d_conj;
  /** last instantiation by single invocation module? */
  bool d_last_inst_si;
private:
  /** check conjecture */
  void checkCegConjecture( CegConjecture * conj );
public:
  CegInstantiation( QuantifiersEngine * qe, context::Context* c );
  ~CegInstantiation();
public:
  bool needsCheck( Theory::Effort e );
  QEffort needsModel(Theory::Effort e);
  /* Call during quantifier engine's check */
  void check(Theory::Effort e, QEffort quant_e);
  /* Called for new quantifiers */
  void registerQuantifier( Node q );
  /** get the next decision request */
  Node getNextDecisionRequest( unsigned& priority );
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const { return "CegInstantiation"; }
  /** print solution for synthesis conjectures */
  void printSynthSolution( std::ostream& out );
  /** get synth solutions
   *
   * This function adds entries to sol_map that map functions-to-synthesize
   * with their solutions, for all active conjectures (currently just the one
   * assigned to d_conj). This should be called immediately after the solver
   * answers unsat for sygus input.
   *
   * For details on what is added to sol_map, see
   * CegConjecture::getSynthSolutions.
   */
  void getSynthSolutions(std::map<Node, Node>& sol_map);
  /** preregister assertion (before rewrite) */
  void preregisterAssertion( Node n );
public:
  class Statistics {
  public:
    IntStat d_cegqi_lemmas_ce;
    IntStat d_cegqi_lemmas_refine;
    IntStat d_cegqi_si_lemmas;
    IntStat d_solutions;
    IntStat d_candidate_rewrites_print;
    IntStat d_candidate_rewrites;
    Statistics();
    ~Statistics();
  };/* class CegInstantiation::Statistics */
  Statistics d_statistics;
}; /* class CegInstantiation */

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
