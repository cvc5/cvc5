/*********************                                                        */
/*! \file infer_info.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
    case Inference::N_ENDPOINT_EMP: return "N_EndpointEmp";
    case Inference::N_UNIFY: return "N_Unify";
    case Inference::N_ENDPOINT_EQ: return "N_EndpointEq";
    case Inference::N_CONST: return "N_Const";
    case Inference::INFER_EMP: return "Infer-Emp";
    case Inference::SSPLIT_CST_PROP: return "S-Split(CST-P)-prop";
    case Inference::SSPLIT_VAR_PROP: return "S-Split(VAR)-prop";
    case Inference::LEN_SPLIT: return "Len-Split(Len)";
    case Inference::LEN_SPLIT_EMP: return "Len-Split(Emp)";
    case Inference::SSPLIT_CST: return "S-Split(CST-P)";
    case Inference::SSPLIT_VAR: return "S-Split(VAR)";
    case Inference::FLOOP: return "F-Loop";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Inference i)
{
  out << toString(i);
  return out;
}

InferInfo::InferInfo() : d_id(Inference::NONE), d_index(0), d_rev(false) {}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
