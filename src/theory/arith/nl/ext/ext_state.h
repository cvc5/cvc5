/*********************                                                        */
/*! \file ext_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common data shared by multiple checks
 **/

#ifndef CVC4__THEORY__ARITH__NL__EXT__SHARED_CHECK_DATA_H
#define CVC4__THEORY__ARITH__NL__EXT__SHARED_CHECK_DATA_H

#include <vector>

#include "expr/node.h"
#include "expr/proof.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/ext/monomial.h"
#include "theory/arith/nl/nl_model.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

struct ExtState
{
  ExtState(InferenceManager& im, NlModel& model, context::Context* c);

  void init(const std::vector<Node>& xts);

  Node d_false;
  Node d_true;
  Node d_zero;
  Node d_one;
  Node d_neg_one;

  /** The inference manager that we push conflicts and lemmas to. */
  InferenceManager& d_im;
  /** Reference to the non-linear model object */
  NlModel& d_model;

  // information about monomials
  std::vector<Node> d_ms;
  std::vector<Node> d_ms_vars;
  std::vector<Node> d_mterms;

  /** Context-independent database of monomial information */
  MonomialDb d_mdb;

  // ( x*y, x*z, y ) for each pair of monomials ( x*y, x*z ) with common factors
  std::map<Node, std::map<Node, Node> > d_mono_diff;
  /** the set of monomials we should apply tangent planes to */
  std::unordered_set<Node, NodeHashFunction> d_tplane_refine;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
