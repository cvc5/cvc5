/*********************                                                        */
/*! \file cegis.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief cegis
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CEGIS_H
#define __CVC4__THEORY__QUANTIFIERS__CEGIS_H

#include <map>
#include "theory/quantifiers/sygus/sygus_module.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Cegis
 *
 * The default sygus module for synthesis, counterexample-guided inductive
 * synthesis (CEGIS).
 *
 * It initializes a list of sygus enumerators that are one-to-one with
 * candidates, and returns a list of candidates that are the model values
 * of these enumerators on calls to constructCandidates.
 */
class Cegis : public SygusModule
{
 public:
  Cegis(QuantifiersEngine* qe, CegConjecture* p);
  ~Cegis() {}
  /** initialize */
  virtual bool initialize(Node n,
                          const std::vector<Node>& candidates,
                          std::vector<Node>& lemmas) override;
  /** get term list */
  virtual void getTermList(const std::vector<Node>& candidates,
                           std::vector<Node>& enums) override;
  /** construct candidate */
  virtual bool constructCandidates(const std::vector<Node>& enums,
                                   const std::vector<Node>& enum_values,
                                   const std::vector<Node>& candidates,
                                   std::vector<Node>& candidate_values,
                                   std::vector<Node>& lems) override;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__CEGIS_H */
