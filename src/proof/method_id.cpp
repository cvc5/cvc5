/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of method identifier
 */

#include "proof/method_id.h"

#include "proof/proof_checker.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

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
  return NodeManager::currentNM()->mkConstInt(
      Rational(static_cast<uint32_t>(id)));
}

bool getMethodId(TNode n, MethodId& i)
{
  uint32_t index;
  if (!ProofRuleChecker::getUInt32(n, index))
  {
    return false;
  }
  i = static_cast<MethodId>(index);
  return true;
}

bool getMethodIds(const std::vector<Node>& args,
                  MethodId& ids,
                  MethodId& ida,
                  MethodId& idr,
                  size_t index)
{
  ids = MethodId::SB_DEFAULT;
  ida = MethodId::SBA_SEQUENTIAL;
  idr = MethodId::RW_REWRITE;
  for (size_t offset = 0; offset <= 2; offset++)
  {
    if (args.size() > index + offset)
    {
      MethodId& id = offset == 0 ? ids : (offset == 1 ? ida : idr);
      if (!getMethodId(args[index + offset], id))
      {
        Trace("builtin-pfcheck")
            << "Failed to get id from " << args[index + offset] << std::endl;
        return false;
      }
    }
    else
    {
      break;
    }
  }
  Trace("builtin-pfcheck") << "Got MethodIds ids/ida/idr: " << ids << " / "
                           << ida << " / " << idr << "\n";
  return true;
}

void addMethodIds(std::vector<Node>& args,
                  MethodId ids,
                  MethodId ida,
                  MethodId idr)
{
  bool ndefRewriter = (idr != MethodId::RW_REWRITE);
  bool ndefApply = (ida != MethodId::SBA_SEQUENTIAL);
  if (ids != MethodId::SB_DEFAULT || ndefRewriter || ndefApply)
  {
    args.push_back(mkMethodId(ids));
  }
  if (ndefApply || ndefRewriter)
  {
    args.push_back(mkMethodId(ida));
  }
  if (ndefRewriter)
  {
    args.push_back(mkMethodId(idr));
  }
}

}  // namespace cvc5::internal
