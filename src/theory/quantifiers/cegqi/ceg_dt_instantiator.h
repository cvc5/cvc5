/*********************                                                        */
/*! \file ceg_dt_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ceg_dt_instantiator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CEG_DT_INSTANTIATOR_H
#define __CVC4__THEORY__QUANTIFIERS__CEG_DT_INSTANTIATOR_H

#include "expr/node.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Datatypes Instantiator
 * 
 */
class DtInstantiator : public Instantiator {
public:
  DtInstantiator( QuantifiersEngine * qe, TypeNode tn ) : Instantiator( qe, tn ){}
  virtual ~DtInstantiator(){}
  void reset(CegInstantiator* ci,
             SolvedForm& sf,
             Node pv,
             CegInstEffort effort) override;
  bool processEqualTerms(CegInstantiator* ci,
                         SolvedForm& sf,
                         Node pv,
                         std::vector<Node>& eqc,
                         CegInstEffort effort) override;
  bool hasProcessEquality(CegInstantiator* ci,
                          SolvedForm& sf,
                          Node pv,
                          CegInstEffort effort) override
  {
    return true;
  }
  bool processEquality(CegInstantiator* ci,
                       SolvedForm& sf,
                       Node pv,
                       std::vector<TermProperties>& term_props,
                       std::vector<Node>& terms,
                       CegInstEffort effort) override;
  std::string identify() const override { return "Dt"; }

 private:
  Node solve_dt(Node v, Node a, Node b, Node sa, Node sb);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__CEG_DT_INSTANTIATOR_H */
