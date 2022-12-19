/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Subsolver for handling code points
 */

#include "theory/strings/code_point_solver.h"

#include "theory/strings/base_solver.h"
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
                                 BaseSolver& bs)
    : EnvObj(env), d_state(s), d_im(im), d_termReg(tr), d_bsolver(bs)
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
  // str.code applied to the code term for each equivalence class that has a
  // code term but is not a constant
  std::vector<Node> nconst_codes;
  // str.code applied to the proxy variables for each equivalence classes that
  // are constants of size one
  std::vector<Node> const_codes;
  const std::vector<Node>& seqc = d_bsolver.getStringLikeEqc();
  for (const Node& eqc : seqc)
  {
    if (!eqc.getType().isString())
    {
      continue;
    }
    if (eqc.isConst())
    {
      Node c = eqc;
      Trace("strings-code-debug")
          << "Get proxy variable for " << c << std::endl;
      Node cc = nm->mkNode(kind::STRING_TO_CODE, c);
      cc = rewrite(cc);
      Assert(cc.isConst());
      Node cp = d_termReg.ensureProxyVariableFor(c);
      Node vc = nm->mkNode(STRING_TO_CODE, cp);
      if (!d_state.areEqual(cc, vc))
      {
        std::vector<Node> emptyVec;
        d_im.sendInference(
            emptyVec, cc.eqNode(vc), InferenceId::STRINGS_CODE_PROXY);
      }
      // only relevant for injectivity if length is 1 (e.g. it has a valid
      // code point)
      if (Word::getLength(c) == 1)
      {
        const_codes.push_back(vc);
      }
    }
    else
    {
      EqcInfo* ei = d_state.getOrMakeEqcInfo(eqc, false);
      if (ei && !ei->d_codeTerm.get().isNull())
      {
        Node vc = nm->mkNode(kind::STRING_TO_CODE, ei->d_codeTerm.get());
        // only relevant for injectivity if not already equal to negative one
        if (!d_state.areEqual(vc, d_negOne))
        {
          nconst_codes.push_back(vc);
        }
      }
    }
  }
  if (d_im.hasProcessed())
  {
    return;
  }
  // now, ensure that str.code is injective
  std::vector<Node> cmps;
  cmps.insert(cmps.end(), const_codes.rbegin(), const_codes.rend());
  cmps.insert(cmps.end(), nconst_codes.rbegin(), nconst_codes.rend());
  for (unsigned i = 0, num_ncc = nconst_codes.size(); i < num_ncc; i++)
  {
    Node c1 = nconst_codes[i];
    cmps.pop_back();
    for (const Node& c2 : cmps)
    {
      Trace("strings-code-debug")
          << "Compare codes : " << c1 << " " << c2 << std::endl;
      if (!d_state.areDisequal(c1, c2))
      {
        Node eq_no = c1.eqNode(d_negOne);
        Node deq = c1.eqNode(c2).negate();
        Node eqn = c1[0].eqNode(c2[0]);
        // str.code(x)==-1 V str.code(x)!=str.code(y) V x==y
        Node inj_lem = nm->mkNode(kind::OR, eq_no, deq, eqn);
        deq = rewrite(deq);
        d_im.addPendingPhaseRequirement(deq, false);
        std::vector<Node> emptyVec;
        d_im.sendInference(emptyVec, inj_lem, InferenceId::STRINGS_CODE_INJ);
      }
    }
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
