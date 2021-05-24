/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of method identifier
 */

#include "proof/method_id.h"

namespace cvc5 {

const char* toString(MethodId id)
{
  switch (id)
  {
    case MethodId::RW_REWRITE: return "RW_REWRITE";
    case MethodId::RW_EXT_REWRITE: return "RW_EXT_REWRITE";
    case MethodId::RW_REWRITE_EQ_EXT: return "RW_REWRITE_EQ_EXT";
    case MethodId::RW_EVALUATE: return "RW_EVALUATE";
    case MethodId::RW_IDENTITY: return "RW_IDENTITY";
    case MethodId::RW_REWRITE_THEORY_PRE: return "RW_REWRITE_THEORY_PRE";
    case MethodId::RW_REWRITE_THEORY_POST: return "RW_REWRITE_THEORY_POST";
    case MethodId::SB_DEFAULT: return "SB_DEFAULT";
    case MethodId::SB_LITERAL: return "SB_LITERAL";
    case MethodId::SB_FORMULA: return "SB_FORMULA";
    case MethodId::SBA_SEQUENTIAL: return "SBA_SEQUENTIAL";
    case MethodId::SBA_SIMUL: return "SBA_SIMUL";
    case MethodId::SBA_FIXPOINT: return "SBA_FIXPOINT";
    default: return "MethodId::Unknown";
  };
}

std::ostream& operator<<(std::ostream& out, MethodId id)
{
  out << toString(id);
  return out;
}

Node mkMethodId(MethodId id)
{
  return NodeManager::currentNM()->mkConst(Rational(static_cast<uint32_t>(id)));
}

}  // namespace cvc5
