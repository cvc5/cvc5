/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Statistics for the liastar extension.
 */

#ifdef CVC5_USE_NORMALIZ

#include "theory/arith/liastar/liastar_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

LiaStarStatistics::LiaStarStatistics(StatisticsRegistry& sr)
    : d_checkFullEffortTime(
          sr.registerTimer("theory::arith::liastar::checkFullEffortTime")),
      d_modelValueTime(
          sr.registerTimer("theory::arith::liastar::modelValueTime")),
      d_toDnfTime(sr.registerTimer("theory::arith::liastar::toDnfTime")),
      d_removeItesTime(
          sr.registerTimer("theory::arith::liastar::removeItesTime")),
      d_removeNotTime(
          sr.registerTimer("theory::arith::liastar::removeNotTime")),
      d_distributeTime(
          sr.registerTimer("theory::arith::liastar::distributeTime")),
      d_getMatricesTime(
          sr.registerTimer("theory::arith::liastar::getMatricesTime")),
      d_normalizInputTime(
          sr.registerTimer("theory::arith::liastar::normalizInputTime")),
      d_normalizComputeTime(
          sr.registerTimer("theory::arith::liastar::normalizComputeTime")),
      d_getConesTime(sr.registerTimer("theory::arith::liastar::getConesTime")),
      d_getLiaTime(sr.registerTimer("theory::arith::liastar::getLiaTime")),
      d_subSolverTime(
          sr.registerTimer("theory::arith::liastar::subSolverTime")),
      d_cvc5SubSolverTime(
          sr.registerTimer("theory::arith::liastar::cvc5SubSolverTime")),
      d_normalizSubSolverTime(
          sr.registerTimer("theory::arith::liastar::normalizSubSolverTime")),
      d_checkRuns(sr.registerInt("theory::arith::liastar::checkRuns")),
      d_starContainsLiterals(
          sr.registerInt("theory::arith::liastar::starContainsLiterals")),
      d_modelValueChecks(
          sr.registerInt("theory::arith::liastar::modelValueChecks")),
      d_modelValueSolved(
          sr.registerInt("theory::arith::liastar::modelValueSolved")),
      d_starTermsReduced(
          sr.registerInt("theory::arith::liastar::starTermsReduced")),
      d_itesRemoved(sr.registerInt("theory::arith::liastar::itesRemoved")),
      d_dnfCalls(sr.registerInt("theory::arith::liastar::dnfCalls")),
      d_dnfDisjuncts(sr.registerInt("theory::arith::liastar::dnfDisjuncts")),
      d_dnfDisjunctsMax(
          sr.registerInt("theory::arith::liastar::dnfDisjunctsMax")),
      d_disjunctsPrunedUnsat(
          sr.registerInt("theory::arith::liastar::disjunctsPrunedUnsat")),
      d_subSolverCalls(
          sr.registerInt("theory::arith::liastar::subSolverCalls")),
      d_subSolverSat(sr.registerInt("theory::arith::liastar::subSolverSat")),
      d_subSolverUnsat(
          sr.registerInt("theory::arith::liastar::subSolverUnsat")),
      d_subSolverUnknown(
          sr.registerInt("theory::arith::liastar::subSolverUnknown")),
      d_normalizCalls(sr.registerInt("theory::arith::liastar::normalizCalls")),
      d_conesEmpty(sr.registerInt("theory::arith::liastar::conesEmpty")),
      d_conesNonempty(sr.registerInt("theory::arith::liastar::conesNonempty")),
      d_hilbertBasisTotal(
          sr.registerInt("theory::arith::liastar::hilbertBasisTotal")),
      d_hilbertBasisMax(
          sr.registerInt("theory::arith::liastar::hilbertBasisMax")),
      d_moduleGeneratorsTotal(
          sr.registerInt("theory::arith::liastar::moduleGeneratorsTotal")),
      d_moduleGeneratorsMax(
          sr.registerInt("theory::arith::liastar::moduleGeneratorsMax")),
      d_dimensionMax(sr.registerInt("theory::arith::liastar::dimensionMax"))
{
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */
