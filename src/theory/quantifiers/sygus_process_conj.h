/*********************                                                        */
/*! \file sygus_process_conj.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Techniqures for static preprocessing and analysis of
 ** sygus conjectures.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_PPROCESS_CONJ_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_PROCESSS_CONJ_H

#include "expr/node.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** This structure stores information regarding conjecture-specific
* analysis of a function to synthesize.
*/
struct CegSynthFunProcessInfo
{
 public:
  CegSynthFunProcessInfo() {}
  ~CegSynthFunProcessInfo() {}
  /** the set of arguments that this synth-fun is independent of */
  std::map<unsigned, bool> d_arg_independent;
};

/** Ceg Conjecture Process
*
* This class implements static techniques for preprocessing and analysis of
* sygus conjectures.
*
* It is used as a back-end to CegConjecture, which calls it using the following
* interface:
* (1) When a sygus conjecture is asserted, we call
* CegConjectureProcess::simplify( q ),
*     where q is the sygus conjecture in original form.
*
* (2) After a sygus conjecture is simplified and converted to deep
* embedding form, we call CegConjectureProcess::initialize( n, candidates ).
*
* (3) During enumerative SyGuS search, calls may be made by
* the extension of the quantifier-free datatypes decision procedure for
* sygus to CegConjectureProcess::getSymmetryBreakingPredicate(...), which are
* used for pruning search space based on conjecture-specific analysis.
*/
class CegConjectureProcess
{
 public:
  CegConjectureProcess(QuantifiersEngine* qe);
  ~CegConjectureProcess();
  /** simplify the synthesis conjecture q
  * Returns a formula that is equivalent to q.
  */
  Node simplify(Node q);
  /** initialize
  *
  * n is the "base instantiation" of the deep-embedding version of
  *   the synthesis conjecture under "candidates".
  *   (see CegConjecture::d_base_inst)
  */
  void initialize(Node n, std::vector<Node>& candidates);
  /** get symmetry breaking predicate
  *
  * Returns a formula that restricts the enumerative search space (for a given
  * depth) for a term x of sygus type tn whose top symbol is the tindex^{th}
  * constructor, where x is a subterm of enumerator e.
  */
  Node getSymmetryBreakingPredicate(
      Node x, Node e, TypeNode tn, unsigned tindex, unsigned depth);
  /** print out debug information about this conjecture */
  void debugPrint(const char* c);

 private:
  /** process conjunct */
  void processConjunct(Node c);
  /** for each synth-fun, information that is specific to this conjecture */
  std::map<Node, CegSynthFunProcessInfo> d_sf_info;
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
};

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif
