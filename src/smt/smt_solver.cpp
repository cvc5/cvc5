/*********************                                                        */
/*! \file smt_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for SMT queries in an SmtEngine.
 **/

#include "smt/smt_solver.h"

namespace CVC4 {
namespace smt {

SmtSolver::SmtSolver(SmtEngine& smt) : d_smt(smt), d_theoryEngine(nullptr), d_propEngine(nullptr)
{
}

SmtSolver::~SmtSolver()
{
}

void SmtSolver::finishInit()
{
  // We have mutual dependency here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine.reset(new TheoryEngine(getContext(),
                                        getUserContext(),
                                        getResourceManager(),
                                        d_pp->getTermFormulaRemover(),
                                        const_cast<const LogicInfo&>(d_logic),
                                        pnm));

  // Add the theories
  for(TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
    TheoryConstructor::addTheory(getTheoryEngine(), id);
    //register with proof engine if applicable
#ifdef CVC4_PROOF
    ProofManager::currentPM()->getTheoryProofEngine()->registerTheory(d_theoryEngine->theoryOf(id));
#endif
  }

  Trace("smt-debug") << "Making decision engine..." << std::endl;

  Trace("smt-debug") << "Making prop engine..." << std::endl;
  /* force destruction of referenced PropEngine to enforce that statistics
   * are unregistered by the obsolete PropEngine object before registered
   * again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new PropEngine(d_theoryEngine.get(),
                                    getContext(),
                                    getUserContext(),
                                    d_smt.getResourceManager(),
                                    pnm));

  Trace("smt-debug") << "Setting up theory engine..." << std::endl;
  d_theoryEngine->setPropEngine(getPropEngine());
  Trace("smt-debug") << "Finishing init for theory engine..." << std::endl;
  d_theoryEngine->finishInit();
}

void SmtSolver::resetAssertions()
{
  
}

void SmtSolver::interrupt()
{
  
}

void SmtSolver::cleanup()
{
}

void SmtSolver::shutdown()
{
  if (d_propEngine != nullptr)
  {
    d_propEngine->shutdown();
  }
  if (d_theoryEngine != nullptr)
  {
    d_theoryEngine->shutdown();
  }
}

void SmtSolver::push()
{
}

void SmtSolver::pop()
{
  
}

Result SmtSolver::checkSatisfiability(Assertions& as,
                            const Node& assumption,
                            bool inUnsatCore,
                            bool isEntailmentCheck)
{
  
}

Result SmtSolver::checkSatisfiability(Assertions& as,
                            const std::vector<Node>& assumptions,
                            bool inUnsatCore,
                            bool isEntailmentCheck)
{
  
}

TheoryEngine* SmtSolver::getTheoryEngine() { return d_theoryEngine.get(); }
prop::PropEngine* SmtSolver::getPropEngine() { return d_propEngine.get(); }
}  // namespace smt
}  // namespace CVC4

