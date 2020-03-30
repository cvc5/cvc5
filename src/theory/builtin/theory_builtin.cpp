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
  // choice nodes are not evaluated in getModelValue
  TheoryModel* theoryModel = d_valuation.getModel();
  Assert(theoryModel != nullptr);
  theoryModel->setUnevaluatedKind(kind::CHOICE);
}

}  // namespace builtin
}  // namespace theory
}  // namespace CVC4
