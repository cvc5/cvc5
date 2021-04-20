/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Michael Chang, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The base class for optimizers of individual cvc5 type.
 */

#include "omt/omt_optimizer.h"

#include "omt/bitvector_optimizer.h"
#include "omt/integer_optimizer.h"
#include "options/smt_options.h"
#include "smt/smt_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::theory;
using namespace cvc5::smt;
namespace cvc5::omt {

std::unique_ptr<OMTOptimizer> OMTOptimizer::getOptimizerForObjective(
    Objective objective)
{
  // the datatype of the target node
  TypeNode objectiveType = objective.d_node.getType(true);
  if (objectiveType.isInteger())
  {
    // integer type: use OMTOptimizerInteger
    return std::unique_ptr<OMTOptimizer>(new OMTOptimizerInteger());
  }
  else if (objectiveType.isBitVector())
  {
    // bitvector type: use OMTOptimizerBitVector
    return std::unique_ptr<OMTOptimizer>(
        new OMTOptimizerBitVector(objective.d_bvSigned));
  }
  else
  {
    CVC5_FATAL() << "Unsupported Type for optimization\n";
    return nullptr;
  }
}

std::pair<Kind, Kind> OMTOptimizer::getLTLEOperator(Objective objective)
{
  // the datatype of the target node
  TypeNode objectiveType = objective.d_node.getType();
  if (objectiveType.isInteger() || objectiveType.isReal())
  {
    // integer type
    return std::make_pair(kind::LT, kind::LEQ);
  }
  else if (objectiveType.isBitVector())
  {
    // bitvector type
    return (objective.d_bvSigned)
               ? (std::make_pair(kind::BITVECTOR_SLT, kind::BITVECTOR_SLE))
               : (std::make_pair(kind::BITVECTOR_ULT, kind::BITVECTOR_ULE));
  }
  else if (objectiveType.isFloatingPoint())
  {
    return std::make_pair(kind::FLOATINGPOINT_LT, kind::FLOATINGPOINT_LEQ);
  }
  else
  {
    CVC5_FATAL() << "Unsupported Type for optimization\n";
    return std::make_pair(kind::NULL_EXPR, kind::NULL_EXPR);
  }
}

}  // namespace cvc5::omt
