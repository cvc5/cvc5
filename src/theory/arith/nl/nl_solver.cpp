/*********************                                                        */
/*! \file nl_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Ahmed Irfan
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of non-linear solver
 **/

#include "theory/arith/nl/nl_solver.h"

#include "options/arith_options.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"
#include "theory/theory_model.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {


NlSolver::NlSolver(InferenceManager& im,
                   ArithState& astate,
                   NlModel& model,
                   SharedCheckData* data)
    : d_im(im), d_model(model), d_data(data)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  d_zero = nm->mkConst(Rational(0));
}

NlSolver::~NlSolver() {}

void NlSolver::initLastCall(const std::vector<Node>& assertions,
                            const std::vector<Node>& false_asserts,
                            const std::vector<Node>& xts)
{
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
