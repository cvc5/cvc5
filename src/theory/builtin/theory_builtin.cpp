/*********************                                                        */
/*! \file theory_builtin.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the builtin theory.
 **
 ** Implementation of the builtin theory.
 **/

#include "theory/builtin/theory_builtin.h"

#include "expr/kind.h"
#include "theory/builtin/theory_builtin_rewriter.h"
#include "theory/theory_model.h"
#include "theory/valuation.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace builtin {

TheoryBuiltin::TheoryBuiltin(context::Context* c,
                             context::UserContext* u,
                             OutputChannel& out,
                             Valuation valuation,
                             const LogicInfo& logicInfo)
    : Theory(THEORY_BUILTIN, c, u, out, valuation, logicInfo)
{
}

std::string TheoryBuiltin::identify() const
{
  return std::string("TheoryBuiltin");
}

void TheoryBuiltin::finishInit()
{
  // Notice that choice is an unevaluated kind belonging to this theory.
  // However, it should be set as an unevaluated kind where it is used, e.g.
  // in the quantifiers theory. This ensures that a logic like QF_LIA, which
  // includes the builtin theory, does not mark any kinds as unevaluated and
  // hence it is easy to check for illegal eliminations via TheoryModel
  // (see TheoryModel::isLegalElimination) since there are no unevaluated kinds
  // present.
}

}  // namespace builtin
}  // namespace theory
}  // namespace CVC4
