/*********************                                                        */
/*! \file bool_to_bv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar, Makai Mann
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BoolToBv preprocessing pass
 **
 **/

#include "preprocessing/passes/bool_to_bv.h"

#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {
using namespace CVC4::theory;

BoolToBV::BoolToBV(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bool-to-bv"),
      d_lowerCache(),
      d_one(bv::utils::mkOne(1)),
      d_zero(bv::utils::mkZero(1)),
      d_statistics(){};

PreprocessingPassResult BoolToBV::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager::currentResourceManager()->spendResource(
      options::preprocessStep());
  std::vector<Node> new_assertions;
  lowerBoolToBv(assertionsToPreprocess->ref(), new_assertions);
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(i, Rewriter::rewrite(new_assertions[i]));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

void BoolToBV::addToLowerCache(TNode term, Node new_term)
{
  Assert(new_term != Node());
  Assert(!hasLowerCache(term));
  d_lowerCache[term] = new_term;
}

Node BoolToBV::getLowerCache(TNode term) const
{
  Assert(hasLowerCache(term));
  return d_lowerCache.find(term)->second;
}

bool BoolToBV::hasLowerCache(TNode term) const
{
  return d_lowerCache.find(term) != d_lowerCache.end();
}

Node BoolToBV::lowerNode(TNode current, bool topLevel)
{
  Node result;
  NodeManager* nm = NodeManager::currentNM();
  if (hasLowerCache(current))
  {
    result = getLowerCache(current);
  }
  else
  {
    if (current.getNumChildren() == 0)
    {
      if (current.getKind() == kind::CONST_BOOLEAN)
      {
        result = (current == bv::utils::mkTrue()) ? d_one : d_zero;
      }
      else
      {
        result = current;
      }
    }
    else
    {
      Kind kind = current.getKind();
      Kind new_kind = kind;
      switch (kind)
      {
        case kind::EQUAL:
          if (current[0].getType().isBitVector()
              || current[0].getType().isBoolean())
          {
            new_kind = kind::BITVECTOR_COMP;
          }
          break;
        case kind::AND: new_kind = kind::BITVECTOR_AND; break;
        case kind::OR: new_kind = kind::BITVECTOR_OR; break;
        case kind::NOT: new_kind = kind::BITVECTOR_NOT; break;
        case kind::XOR: new_kind = kind::BITVECTOR_XOR; break;
        case kind::IMPLIES: new_kind = kind::BITVECTOR_OR; break;
        case kind::ITE:
          if (current.getType().isBitVector() || current.getType().isBoolean())
          {
            new_kind = kind::BITVECTOR_ITE;
          }
          break;
        case kind::BITVECTOR_ULT: new_kind = kind::BITVECTOR_ULTBV; break;
        case kind::BITVECTOR_SLT: new_kind = kind::BITVECTOR_SLTBV; break;
        case kind::BITVECTOR_ULE:
        case kind::BITVECTOR_UGT:
        case kind::BITVECTOR_UGE:
        case kind::BITVECTOR_SLE:
        case kind::BITVECTOR_SGT:
        case kind::BITVECTOR_SGE:
          // Should have been removed by rewriting.
          Unreachable();
        default: break;
      }
      NodeBuilder<> builder(new_kind);
      if (kind != new_kind)
      {
        ++(d_statistics.d_numTermsLowered);
      }
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        builder << current.getOperator();
      }
      Node converted;
      if (new_kind == kind::ITE)
      {
        // Special-case ITE because need condition to be Boolean.
        converted = lowerNode(current[0], true);
        builder << converted;
        converted = lowerNode(current[1]);
        builder << converted;
        converted = lowerNode(current[2]);
        builder << converted;
      }
      else if (kind == kind::IMPLIES) {
        // Special-case IMPLIES because needs to be rewritten.
        converted = lowerNode(current[0]);
        builder << nm->mkNode(kind::BITVECTOR_NOT, converted);
        converted = lowerNode(current[1]);
        builder << converted;
      }
      else
      {
        for (unsigned i = 0; i < current.getNumChildren(); ++i)
        {
          converted = lowerNode(current[i]);
          builder << converted;
        }
      }
      result = builder;
    }
    if (result.getType().isBoolean())
    {
      ++(d_statistics.d_numTermsForcedLowered);
      result = nm->mkNode(kind::ITE, result, d_one, d_zero);
    }
    addToLowerCache(current, result);
  }
  if (topLevel)
  {
    result = nm->mkNode(kind::EQUAL, result, d_one);
  }
  Assert(result != Node());
  Debug("bool-to-bv") << "BoolToBV::lowerNode " << current << " => \n"
                      << result << "\n";
  return result;
}

void BoolToBV::lowerBoolToBv(const std::vector<Node>& assertions,
                             std::vector<Node>& new_assertions)
{
  for (unsigned i = 0; i < assertions.size(); ++i)
  {
    Node new_assertion = lowerNode(assertions[i], true);
    new_assertions.push_back(new_assertion);
    Trace("bool-to-bv") << "  " << assertions[i] << " => " << new_assertions[i]
                        << "\n";
  }
}

BoolToBV::Statistics::Statistics()
    : d_numTermsLowered("preprocessing::passes::BoolToBV::NumTermsLowered", 0),
      d_numAtomsLowered("preprocessing::passes::BoolToBV::NumAtomsLowered", 0),
      d_numTermsForcedLowered(
          "preprocessing::passes::BoolToBV::NumTermsForcedLowered", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numTermsLowered);
  smtStatisticsRegistry()->registerStat(&d_numAtomsLowered);
  smtStatisticsRegistry()->registerStat(&d_numTermsForcedLowered);
}

BoolToBV::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_numTermsLowered);
  smtStatisticsRegistry()->unregisterStat(&d_numAtomsLowered);
  smtStatisticsRegistry()->unregisterStat(&d_numTermsForcedLowered);
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
