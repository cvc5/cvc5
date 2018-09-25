/*********************                                                        */
/*! \file ite_to_bvite.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the CVC4 project.
** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file COPYING in the top-level source
** directory for licensing information.\endverbatim
**
** \brief The IteToBvite preprocessing pass. Converts ITEs to BITVECTOR_ITEs
**         when it's convenient to do so, as implemented by easyToLower
**
**/

#include "preprocessing/passes/ite_to_bvite.h"

#include <string>

#include "expr/node.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {
using namespace CVC4::theory;

IteToBvite::IteToBvite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ite-to-bvite"), d_statistics(){};

PreprocessingPassResult IteToBvite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager::currentResourceManager()->spendResource(
      options::preprocessStep());

  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, Rewriter::rewrite(lowerIte(assertionsToPreprocess->operator[](i))));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

Node IteToBvite::lowerIte(TNode term)
{
  Debug("ite-to-bvite") << "IteToBvite got " << term << std::endl;
  Kind kind = term.getKind();

  if (term.getNumChildren() == 0)
  {
    return term;
  }

  // potentially changes if lowering an ITE, bool arg becomes bitvec
  Node firstChild = term[0];
  Kind new_kind = kind;
  if ((kind == kind::ITE) && easyToLower(term[0]))
  {
    ++(d_statistics.d_numIteToBvite);
    firstChild = lowerBool(firstChild);
    new_kind = kind::BITVECTOR_ITE;
  }

  NodeBuilder<> builder(new_kind);
  if (term.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << term.getOperator();
  }

  builder << lowerIte(firstChild);
  for (unsigned i = 1; i < term.getNumChildren(); ++i)
  {
    builder << lowerIte(term[i]);
  }

  Debug("ite-to-bvite") << "Lowered to " << builder << std::endl;

  return builder;
}

Node IteToBvite::lowerBool(TNode boolTerm)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind kind = boolTerm.getKind();
  Kind new_kind = kind;
  switch (kind)
  {
    case kind::EQUAL:
      // guaranteed because only executed if easyToLower(boolTerm) is true
      Assert(boolTerm[0].getType().isBitVector());
      // don't need to handle other case because of rewrites
      if ((boolTerm[0].getType().getBitVectorSize() == 1)
          && boolTerm[1].isConst())
      {
        BitVector val = boolTerm[1].getConst<BitVector>();
        if (val == BitVector(1, (unsigned)1))
        {
          return boolTerm[0];
        }
        else
        {
          return nm->mkNode(kind::BITVECTOR_NOT, boolTerm[0]);
        }
      }
      else
      {
        new_kind = kind::BITVECTOR_COMP;
      }
      break;
    case kind::BITVECTOR_ULT: new_kind = kind::BITVECTOR_ULTBV; break;
    case kind::BITVECTOR_SLT: new_kind = kind::BITVECTOR_SLTBV; break;
    default:
      // only three cases above due to easyToLower and rewriting
      Unreachable();
      break;
  }

  Assert(new_kind != kind);
  return nm->mkNode(new_kind, boolTerm[0], boolTerm[1]);
}

bool IteToBvite::easyToLower(TNode boolTerm)
{
  Assert(boolTerm.getType().isBoolean());
  Kind kind = boolTerm.getKind();
  return ((kind == kind::BITVECTOR_ULT) || (kind == kind::BITVECTOR_SLT)
          || ((kind == kind::EQUAL) && boolTerm[0].getType().isBitVector()));
}

IteToBvite::Statistics::Statistics()
    : d_numIteToBvite("preprocessing::passes::IteToBvite::NumIteToBvite", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numIteToBvite);
}

IteToBvite::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_numIteToBvite);
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
