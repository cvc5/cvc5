/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference information utility.
 */

#include "theory/strings/infer_info.h"

#include "theory/strings/inference_manager.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

InferInfo::InferInfo(InferenceId id): TheoryInference(id), d_sim(nullptr), d_idRev(false)
{
}

TrustNode InferInfo::processLemma(LemmaProperty& p)
{
  return d_sim->processLemma(*this, p);
}

Node InferInfo::processFact(std::vector<Node>& exp, ProofGenerator*& pg)
{
  for (const Node& ec : d_premises)
  {
    utils::flattenOp(kind::AND, ec, exp);
  }
  d_sim->processFact(*this, pg);
  return d_conc;
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
  // we could process inferences with conjunctive conclusions as facts, where
  // the explanation is copied. However, for simplicity, we always send these
  // as lemmas. This case happens very infrequently.
  return !atom.isConst() && Theory::theoryOf(atom) == THEORY_STRINGS
         && d_noExplain.empty();
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
}  // namespace cvc5::internal
