/*********************                                                        */
/*! \file shared_check_data.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
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
  Node d_false = NodeManager::currentNM()->mkConst(false);
  Node d_true = NodeManager::currentNM()->mkConst(true);
  Node d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  Node d_one = NodeManager::currentNM()->mkConst(Rational(1));
  Node d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));

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

  std::unique_ptr<CDProof> d_proof;

  ExtState(InferenceManager& im,
           NlModel& model,
           ProofNodeManager* pnm,
           context::Context* c)
      : d_im(im), d_model(model)
  {
    if (pnm != nullptr)
    {
      d_proof.reset(new CDProof(pnm, c));
    }
  }

  void init(const std::vector<Node>& xts);

  bool proofsEnabled() const { return d_proof != nullptr; }
  bool addProof(Node expected,
                PfRule id,
                const std::vector<Node>& children,
                const std::vector<Node>& args)
  {
    if (!proofsEnabled()) return false;
    return d_proof->addStep(expected, id, children, args);
  }
  std::shared_ptr<ProofNode> getProof(Node expected)
  {
    if (!proofsEnabled()) return nullptr;
    return d_proof->getProofFor(expected);
  }
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif
