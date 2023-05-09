/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Datatypes inference.
 */

#include "theory/datatypes/inference.h"

#include "expr/dtype.h"
#include "options/datatypes_options.h"
#include "theory/datatypes/inference_manager.h"
#include "theory/theory.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace datatypes {

DatatypesInference::DatatypesInference(InferenceManager* im,
                                       Node conc,
                                       Node exp,
                                       InferenceId i)
    : SimpleTheoryInternalFact(i, conc, exp, nullptr), d_im(im)
{
  // false is not a valid explanation
  Assert(d_exp.isNull() || !d_exp.isConst() || d_exp.getConst<bool>());
}

bool DatatypesInference::mustCommunicateFact(Node n, Node exp)
{
  Trace("dt-lemma-debug") << "Compute for " << exp << " => " << n << std::endl;
  // Note that equalities due to instantiate are forced as lemmas if
  // necessary as they are created. This ensures that terms are shared with
  // external theories when necessary. We send the lemma here only if the
  // conclusion has kind LEQ (for datatypes size) or OR. Notice that
  // all equalities are kept internal, apart from those forced as lemmas
  // via instantiate.
  if (n.getKind() == LEQ || n.getKind() == OR)
  {
    Trace("dt-lemma-debug")
        << "Communicate " << n << " due to kind" << std::endl;
    return true;
  }
  Trace("dt-lemma-debug") << "Do not communicate " << n << std::endl;
  return false;
}

TrustNode DatatypesInference::processLemma(LemmaProperty& p)
{
  // we don't pass lemma property p currently, as it is always default
  return d_im->processDtLemma(d_conc, d_exp, getId());
}

Node DatatypesInference::processFact(std::vector<Node>& exp,
                                     ProofGenerator*& pg)
{
  // add to the explanation vector if applicable (when non-trivial)
  if (!d_exp.isNull() && !d_exp.isConst())
  {
    exp.push_back(d_exp);
  }
  return d_im->processDtFact(d_conc, d_exp, getId(), pg);
}

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
