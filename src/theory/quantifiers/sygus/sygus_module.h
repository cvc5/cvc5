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
 * This is the base class of sygus modules, owned by CegConjecture. 
 * An instance of the conjecture class (CegConjecture) contains a "candidate"
 * list, which are Skolem variables that are one-to-one with the functions to 
 * synthesize, and whose (sygus) types correspond to the types of the variables
 * in the deep embedded form of the synthesis conjecture.
 * 
 * Modules implement an initialize function, which determines whether the module
 * will take responsibility for the given conjecture.
 */
class SygusModule 
{
public:
  SygusModule( QuantifiersEngine * qe, CegConjecture* p );
  ~SygusModule(){}
  /** initialize 
   * 
   * n is the "base instantiation" of the deep-embedding version of the 
   * synthesis conjecture under candidates (see CegConjecture::d_base_inst).
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
   * terms : the terms returned by a call to getTermList,
   * term_values : the current model values of terms,
   * candidates : the list of candidates.
   * 
   * If this function returns true, it adds to candidate_values a list of terms
   * of the same length and type as candidates that are candidate solutions
   * to the synthesis conjecture in question. This candidate will then be tested
   * by 
   * 
   * This function may also add lemmas to lems, which are sent out as lemmas
   * on the output channel of QuantifiersEngine.
   */
  virtual bool constructCandidates(const std::vector<Node>& terms,
                                   const std::vector<Node>& term_values,
                                   const std::vector<Node>& candidates,
                                   std::vector<Node>& candidate_values,
                                   std::vector<Node>& lems) = 0;
 protected:
  /** reference to quantifier engine */
  QuantifiersEngine * d_qe;
  /** reference to the parent conjecture */
  CegConjecture * d_parent;
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_MODULE_H */
