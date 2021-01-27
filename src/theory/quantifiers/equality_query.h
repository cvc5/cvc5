/*********************                                                        */
/*! \file equality_query.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Equality query class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS_EQUALITY_QUERY_H
#define CVC4__THEORY__QUANTIFIERS_EQUALITY_QUERY_H

#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/quantifiers_state.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** EqualityQueryQuantifiersEngine class
 *
 * The main method of this class is the function
 * getInternalRepresentative, which is used by instantiation-based methods
 * that are agnostic with respect to choosing terms within an equivalence class.
 * Examples of such methods are finite model finding and enumerative
 * instantiation. Method getInternalRepresentative returns the "best"
 * representative based on the internal heuristic, which is currently based on
 * choosing the term that was previously chosen as a representative earliest.
 */
class EqualityQueryQuantifiersEngine : public QuantifiersUtil
{
 public:
  EqualityQueryQuantifiersEngine(QuantifiersState& qs, QuantifiersEngine* qe);
  virtual ~EqualityQueryQuantifiersEngine();
  /** reset */
  bool reset(Theory::Effort e) override;
  /* Called for new quantifiers */
  void registerQuantifier(Node q) override {}
  /** identify */
  std::string identify() const override { return "EqualityQueryQE"; }
  /** gets the current best representative in the equivalence
   * class of a, based on some heuristic. Currently, the default heuristic
   * chooses terms that were previously chosen as representatives
   * on the earliest instantiation round.
   *
   * If q is non-null, then q/index is the quantified formula
   * and variable position that we are choosing for instantiation.
   *
   * This function avoids certain terms that are "ineligible" for instantiation.
   * If cbqi is active, we terms that contain instantiation constants
   * are ineligible. As a result, this function may return
   * Node::null() if all terms in the equivalence class of a
   * are ineligible.
   */
  Node getInternalRepresentative(Node a, Node q, int index);

 private:
  /** pointer to theory engine */
  QuantifiersEngine* d_qe;
  /** the quantifiers state */
  QuantifiersState& d_qstate;
  /** quantifiers equality inference */
  context::CDO< unsigned > d_eqi_counter;
  /** internal representatives */
  std::map< TypeNode, std::map< Node, Node > > d_int_rep;
  /** rep score */
  std::map< Node, int > d_rep_score;
  /** the number of times reset( e ) has been called */
  int d_reset_count;
  /** processInferences : will merge equivalence classes in master equality engine, if possible */
  bool processInferences( Theory::Effort e );
  /** node contains */
  Node getInstance( Node n, const std::vector< Node >& eqc, std::unordered_map<TNode, Node, TNodeHashFunction>& cache );
  /** get score */
  int getRepScore( Node n, Node f, int index, TypeNode v_tn );
}; /* EqualityQueryQuantifiersEngine */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS_EQUALITY_QUERY_H */
