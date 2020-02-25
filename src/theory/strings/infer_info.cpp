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

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

std::ostream& operator<<(std::ostream& out, Inference i)
{
  switch (i)
  {
    case INFER_INFER_EMP: out << "Infer-Emp"; break;
    case INFER_SSPLIT_CST_PROP: out << "S-Split(CST-P)-prop"; break;
    case INFER_SSPLIT_VAR_PROP: out << "S-Split(VAR)-prop"; break;
    case INFER_LEN_SPLIT: out << "Len-Split(Len)"; break;
    case INFER_LEN_SPLIT_EMP: out << "Len-Split(Emp)"; break;
    case INFER_SSPLIT_CST: out << "S-Split(CST-P)"; break;
    case INFER_SSPLIT_VAR: out << "S-Split(VAR)"; break;
    case INFER_FLOOP: out << "F-Loop"; break;
    default: out << "?"; break;
  }
  return out;
}

InferInfo::InferInfo() : d_id(INFER_NONE), d_index(0), d_rev(false) {}

}  // namespace strings
}  // namespace theory
}  // namespace CVC4
