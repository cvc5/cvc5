/*********************                                                        */
/*! \file infer_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference information utility.
 **/

#include "theory/strings/infer_info.h"

#include "theory/strings/inference_manager.h"
#include "theory/strings/theory_strings_utils.h"

namespace CVC4 {
namespace theory {
namespace strings {

InferInfo::InferInfo(InferenceId id): TheoryInference(id), d_sim(nullptr), d_idRev(false)
{
}

bool InferInfo::process(TheoryInferenceManager* im, bool asLemma)
{
  if (asLemma)
  {
    return d_sim->processLemma(*this);
  }
  return d_sim->processFact(*this);
}

TrustNode InferInfo::processLemma(LemmaProperty& p)
{
  return d_sim->processLemma(*this, p);
}

Node InferInfo::processInternalFact(std::vector<Node>& exp, ProofGenerator*& pg)
{
  return d_sim->processFact(*this, exp, pg);
}

bool InferInfo::isTrivial() const
{
  Assert(!d_conc.isNull());
  return d_conc.isConst() && d_conc.getConst<bool>();
}

bool InferInfo::isConflict() const
{
  Assert(!d_conc.isNull());
  return d_conc.isConst() && !d_conc.getConst<bool>() && d_noExplain.empty();
}

bool InferInfo::isFact() const
{
  Assert(!d_conc.isNull());
  TNode atom = d_conc.getKind() == kind::NOT ? d_conc[0] : d_conc;
  return !atom.isConst() && atom.getKind() != kind::OR && d_noExplain.empty();
}

Node InferInfo::getPremises() const
{
  // d_noExplain is a subset of d_ant
  return utils::mkAnd(d_premises);
}

std::ostream& operator<<(std::ostream& out, const InferInfo& ii)
{
  out << "(infer " << ii.getId() << " " << ii.d_conc;
  if (ii.d_idRev)
  {
    out << " :rev";
  }
  if (!ii.d_premises.empty())
  {
    out << " :ant (" << ii.d_premises << ")";
  }
  if (!ii.d_noExplain.empty())
  {
    out << " :no-explain (" << ii.d_noExplain << ")";
  }
  out << ")";
  return out;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
