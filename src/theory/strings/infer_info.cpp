/*********************                                                        */
/*! \file infer_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference information utility.
 **/

#include "theory/strings/infer_info.h"

namespace CVC4 {
namespace theory {
namespace strings {

const char* toString(Inference i)
{
  switch (i)
  {
    case Inference::I_NORM_S: return "I_NORM_S";
    case Inference::I_CONST_MERGE: return "I_CONST_MERGE";
    case Inference::I_CONST_CONFLICT: return "I_CONST_CONFLICT";
    case Inference::I_NORM: return "I_NORM";
    case Inference::CARD_SP: return "CARD_SP";
    case Inference::CARDINALITY: return "CARDINALITY";
    case Inference::I_CYCLE_E: return "I_CYCLE_E";
    case Inference::I_CYCLE: return "I_CYCLE";
    case Inference::F_CONST: return "F_CONST";
    case Inference::F_UNIFY: return "F_UNIFY";
    case Inference::F_ENDPOINT_EMP: return "F_ENDPOINT_EMP";
    case Inference::F_ENDPOINT_EQ: return "F_ENDPOINT_EQ";
    case Inference::F_NCTN: return "F_NCTN";
    case Inference::N_EQ_CONF: return "N_EQ_CONF";
    case Inference::N_ENDPOINT_EMP: return "N_ENDPOINT_EMP";
    case Inference::N_UNIFY: return "N_UNIFY";
    case Inference::N_ENDPOINT_EQ: return "N_ENDPOINT_EQ";
    case Inference::N_CONST: return "N_CONST";
    case Inference::INFER_EMP: return "INFER_EMP";
    case Inference::SSPLIT_CST_PROP: return "SSPLIT_CST_PROP";
    case Inference::SSPLIT_VAR_PROP: return "SSPLIT_VAR_PROP";
    case Inference::LEN_SPLIT: return "LEN_SPLIT";
    case Inference::LEN_SPLIT_EMP: return "LEN_SPLIT_EMP";
    case Inference::SSPLIT_CST: return "SSPLIT_CST";
    case Inference::SSPLIT_VAR: return "SSPLIT_VAR";
    case Inference::FLOOP: return "FLOOP";
    case Inference::FLOOP_CONFLICT: return "FLOOP_CONFLICT";
    case Inference::NORMAL_FORM: return "NORMAL_FORM";
    case Inference::N_NCTN: return "N_NCTN";
    case Inference::LEN_NORM: return "LEN_NORM";
    case Inference::DEQ_DISL_EMP_SPLIT: return "DEQ_DISL_EMP_SPLIT";
    case Inference::DEQ_DISL_FIRST_CHAR_EQ_SPLIT:
      return "DEQ_DISL_FIRST_CHAR_EQ_SPLIT";
    case Inference::DEQ_DISL_FIRST_CHAR_STRING_SPLIT:
      return "DEQ_DISL_FIRST_CHAR_STRING_SPLIT";
    case Inference::DEQ_STRINGS_EQ: return "DEQ_STRINGS_EQ";
    case Inference::DEQ_DISL_STRINGS_SPLIT: return "DEQ_DISL_STRINGS_SPLIT";
    case Inference::DEQ_LENS_EQ: return "DEQ_LENS_EQ";
    case Inference::DEQ_NORM_EMP: return "DEQ_NORM_EMP";
    case Inference::DEQ_LENGTH_SP: return "DEQ_LENGTH_SP";
    case Inference::CODE_PROXY: return "CODE_PROXY";
    case Inference::CODE_INJ: return "CODE_INJ";
    case Inference::RE_NF_CONFLICT: return "RE_NF_CONFLICT";
    case Inference::RE_UNFOLD_POS: return "RE_UNFOLD_POS";
    case Inference::RE_UNFOLD_NEG: return "RE_UNFOLD_NEG";
    case Inference::RE_INTER_INCLUDE: return "RE_INTER_INCLUDE";
    case Inference::RE_INTER_CONF: return "RE_INTER_CONF";
    case Inference::RE_INTER_INFER: return "RE_INTER_INFER";
    case Inference::RE_DELTA: return "RE_DELTA";
    case Inference::RE_DELTA_CONF: return "RE_DELTA_CONF";
    case Inference::RE_DERIVE: return "RE_DERIVE";
    case Inference::EXTF: return "EXTF";
    case Inference::EXTF_N: return "EXTF_N";
    case Inference::EXTF_D: return "EXTF_D";
    case Inference::EXTF_D_N: return "EXTF_D_N";
    case Inference::EXTF_EQ_REW: return "EXTF_EQ_REW";
    case Inference::CTN_TRANS: return "CTN_TRANS";
    case Inference::CTN_DECOMPOSE: return "CTN_DECOMPOSE";
    case Inference::CTN_NEG_EQUAL: return "CTN_NEG_EQUAL";
    case Inference::CTN_POS: return "CTN_POS";
    case Inference::REDUCTION: return "REDUCTION";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Inference i)
{
  out << toString(i);
  return out;
}

InferInfo::InferInfo() : d_id(Inference::NONE) {}

bool InferInfo::isTrivial() const
{
  Assert(!d_conc.isNull());
  return d_conc.isConst() && d_conc.getConst<bool>();
}

bool InferInfo::isConflict() const
{
  Assert(!d_conc.isNull());
  return d_conc.isConst() && !d_conc.getConst<bool>() && d_antn.empty();
}

bool InferInfo::isFact() const
{
  Assert(!d_conc.isNull());
  TNode atom = d_conc.getKind() == kind::NOT ? d_conc[0] : d_conc;
  return !atom.isConst() && atom.getKind() != kind::OR && d_antn.empty();
}

std::ostream& operator<<(std::ostream& out, const InferInfo& ii)
{
  out << "(infer " << ii.d_id << " " << ii.d_conc;
  if (!ii.d_ant.empty())
  {
    out << " :ant (" << ii.d_ant << ")";
  }
  if (!ii.d_antn.empty())
  {
    out << " :antn (" << ii.d_antn << ")";
  }
  out << ")";
  return out;
}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
