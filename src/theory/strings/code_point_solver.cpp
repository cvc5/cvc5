/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Subsolver for handling code points
 */

#include "theory/strings/code_point_solver.h"

#include "theory/strings/base_solver.h"
#include "theory/strings/core_solver.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"
#include "theory/strings/word.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

CodePointSolver::CodePointSolver(Env& env,
                                 SolverState& s,
                                 InferenceManager& im,
                                 TermRegistry& tr,
                                 BaseSolver& bs,
                                 CoreSolver& cs)
    : EnvObj(env),
      d_state(s),
      d_im(im),
      d_termReg(tr),
      d_bsolver(bs),
      d_csolver(cs)
{
  d_negOne = NodeManager::currentNM()->mkConstInt(Rational(-1));
}

void CodePointSolver::checkCodes()
{
  // ensure that lemmas regarding str.code been added for each constant string
  // of length one
  if (!d_termReg.hasStringCode())
  {
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  // We construct a mapping from string equivalent classes to code point
  // applications. This mapping contains entries:
  // (1) r -> (str.to_code t) where r is the representative of t and the
  // term (str.to_code t) occurs in the equality engine.
  // (2) c -> (str.to_code k) where c is a string constant of length one and
  // c occurs in the equality engine (as a representative).
  // This mapping omits str.to_code terms that are already equal to -1.
  std::map<Node, Node> codes;
  const std::vector<Node>& seqc = d_bsolver.getStringLikeEqc();
  for (const Node& eqc : seqc)
  {
    if (!eqc.getType().isString())
    {
      continue;
    }
    Node codeArg;
    if (eqc.isConst())
    {
      // only relevant for injectivity if length is 1 (e.g. it has a valid
      // code point)
      if (Word::getLength(eqc) != 1)
      {
        continue;
      }
      codeArg = d_termReg.ensureProxyVariableFor(eqc);
    }
    else
    {
      EqcInfo* ei = d_state.getOrMakeEqcInfo(eqc, false);
      if (ei == nullptr || ei->d_codeTerm.get().isNull())
      {
        continue;
      }
      codeArg = ei->d_codeTerm.get();
    }
    Node vc = nm->mkNode(kind::STRING_TO_CODE, codeArg);
    // only relevant for injectivity if not already equal to negative one
    if (d_state.areEqual(vc, d_negOne))
    {
      continue;
    }
    codes[eqc] = vc;
  }
  if (d_im.hasProcessed() || codes.size() <= 1)
  {
    return;
  }
  // Now, ensure that str.code is injective. We only apply injectivity for
  // pairs of terms that are disequal. We check pairs of disequal terms by
  // iterating over the disequalities in getRelevantDeq.
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  std::map<Node, Node>::iterator itc;
  const std::vector<Node>& rlvDeq = d_csolver.getRelevantDeq();
  for (const Node& eq : rlvDeq)
  {
    bool foundCodePair = true;
    Node r[2];
    Node c[2];
    for (size_t i = 0; i < 2; i++)
    {
      r[i] = ee->getRepresentative(eq[i]);
      itc = codes.find(r[i]);
      if (itc == codes.end())
      {
        foundCodePair = false;
        break;
      }
      c[i] = itc->second;
    }
    if (!foundCodePair)
    {
      continue;
    }
    Trace("strings-code-debug")
        << "Compare codes : " << c[0] << " " << c[1] << std::endl;
    if (d_state.areDisequal(c[0], c[1]))
    {
      // code already disequal
      continue;
    }
    Node eq_no = c[0].eqNode(d_negOne);
    Node deq = c[0].eqNode(c[1]).negate();
    Node eqn = c[0][0].eqNode(c[1][0]);
    // str.code(x)==-1 V str.code(x)!=str.code(y) V x==y
    Node inj_lem = nm->mkNode(kind::OR, eq_no, deq, eqn);
    deq = rewrite(deq);
    d_im.addPendingPhaseRequirement(deq, false);
    std::vector<Node> emptyVec;
    d_im.sendInference(emptyVec, inj_lem, InferenceId::STRINGS_CODE_INJ);
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
