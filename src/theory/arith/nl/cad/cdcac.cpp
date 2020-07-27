/*********************                                                        */
/*! \file cdcac.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements the CDCAC approach.
 **
 ** Implements the CDCAC approach as described in
 ** https://arxiv.org/pdf/2003.05633.pdf.
 **/

#include "theory/arith/nl/cad/cdcac.h"

#include "theory/arith/nl/cad/projections.h"
#include "theory/arith/nl/cad/variable_ordering.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

CDCAC::CDCAC() {}

CDCAC::CDCAC(const std::vector<Variable>& ordering)
    : mVariableOrdering(ordering)
{
}

void CDCAC::reset()
{
  mConstraints.reset();
  mAssignment.clear();
}

void CDCAC::computeVariableOrdering() {}

Constraints& CDCAC::getConstraints() { return mConstraints; }
const Constraints& CDCAC::getConstraints() const { return mConstraints; }

const Assignment& CDCAC::getModel() const { return mAssignment; }

const std::vector<Variable>& CDCAC::getVariableOrdering() const
{
  return mVariableOrdering;
}

std::vector<CACInterval> CDCAC::getUnsatIntervals(
    std::size_t cur_variable) const
{
  return {};
}

std::vector<Polynomial> CDCAC::requiredCoefficients(const Polynomial& p) const
{
  return {};
}

std::vector<Polynomial> CDCAC::constructCharacterization(
    std::vector<CACInterval>& intervals)
{
  return {};
}

CACInterval CDCAC::intervalFromCharacterization(
    const std::vector<Polynomial>& characterization,
    std::size_t cur_variable,
    const Value& sample)
{
  return {};
}

std::vector<CACInterval> CDCAC::getUnsatCover(std::size_t cur_variable)
{
  return {};
}

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4
