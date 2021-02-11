/*********************                                                        */
/*! \file inference.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Datatypes inference
 **/

#include "theory/datatypes/inference.h"

#include "expr/dtype.h"
#include "options/datatypes_options.h"
#include "theory/datatypes/inference_manager.h"
#include "theory/theory.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace datatypes {

DatatypesInference::DatatypesInference(InferenceManager* im,
                                       Node conc,
                                       Node exp,
                                       InferenceId i)
    : SimpleTheoryInternalFact(conc, exp, nullptr), d_im(im), d_id(i)
{
  // false is not a valid explanation
  Assert(d_exp.isNull() || !d_exp.isConst() || d_exp.getConst<bool>());
}

bool DatatypesInference::mustCommunicateFact(Node n, Node exp)
{
  Trace("dt-lemma-debug") << "Compute for " << exp << " => " << n << std::endl;
  // Force lemmas if option is set
  if (options::dtInferAsLemmas())
  {
    Trace("dt-lemma-debug")
        << "Communicate " << n << " due to option" << std::endl;
    return true;
  }
  // Note that equalities due to instantiate are forced as lemmas if
  // necessary as they are created. This ensures that terms are shared with
  // external theories when necessary. We send the lemma here only if the
  // conclusion has kind LEQ (for datatypes size) or OR. Notice that
  // all equalities are kept internal, apart from those forced as lemmas
  // via instantiate.
  else if (n.getKind() == LEQ || n.getKind() == OR)
  {
    Trace("dt-lemma-debug")
        << "Communicate " << n << " due to kind" << std::endl;
    return true;
  }
  Trace("dt-lemma-debug") << "Do not communicate " << n << std::endl;
  return false;
}

bool DatatypesInference::process(TheoryInferenceManager* im, bool asLemma)
{
  // Check to see if we have to communicate it to the rest of the system.
  // The flag asLemma is true when the inference was marked that it must be
  // sent as a lemma in addPendingInference below.
  if (asLemma || mustCommunicateFact(d_conc, d_exp))
  {
    return d_im->processDtLemma(d_conc, d_exp, d_id);
  }
  return d_im->processDtFact(d_conc, d_exp, d_id);
}

InferenceId DatatypesInference::getInferId() const { return d_id; }

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
