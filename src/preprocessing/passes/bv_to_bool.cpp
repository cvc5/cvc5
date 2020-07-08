/*********************                                                        */
/*! \file bv_to_bool.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar, Liana Hadarean, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass that lifts bit-vectors of size 1 to booleans.
 **
 ** Preprocessing pass that lifts bit-vectors of size 1 to booleans.
 ** Implemented recursively.
 **/

#include "preprocessing/passes/bv_to_bool.h"

#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_visitor.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace CVC4::theory;

BVToBool::BVToBool(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-to-bool"),
      d_liftCache(),
      d_boolCache(),
      d_one(bv::utils::mkOne(1)),
      d_zero(bv::utils::mkZero(1)),
      d_statistics(){};

PreprocessingPassResult BVToBool::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(ResourceManager::Resource::PreprocessStep);
  std::vector<Node> new_assertions;
  liftBvToBool(assertionsToPreprocess->ref(), new_assertions);
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(i, Rewriter::rewrite(new_assertions[i]));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

void BVToBool::addToLiftCache(TNode term, Node new_term)
{
  Assert(new_term != Node());
  Assert(!hasLiftCache(term));
  Assert(term.getType() == new_term.getType());
  d_liftCache[term] = new_term;
}

Node BVToBool::getLiftCache(TNode term) const
{
  Assert(hasLiftCache(term));
  return d_liftCache.find(term)->second;
}

bool BVToBool::hasLiftCache(TNode term) const
{
  return d_liftCache.find(term) != d_liftCache.end();
}

void BVToBool::addToBoolCache(TNode term, Node new_term)
{
  Assert(new_term != Node());
  Assert(!hasBoolCache(term));
  Assert(bv::utils::getSize(term) == 1);
  Assert(new_term.getType().isBoolean());
  d_boolCache[term] = new_term;
}

Node BVToBool::getBoolCache(TNode term) const
{
  Assert(hasBoolCache(term));
  return d_boolCache.find(term)->second;
}

bool BVToBool::hasBoolCache(TNode term) const
{
  return d_boolCache.find(term) != d_boolCache.end();
}
bool BVToBool::isConvertibleBvAtom(TNode node)
{
  Kind kind = node.getKind();
  return (kind == kind::EQUAL && node[0].getType().isBitVector()
          && node[0].getType().getBitVectorSize() == 1
          && node[1].getType().isBitVector()
          && node[1].getType().getBitVectorSize() == 1
          && node[0].getKind() != kind::BITVECTOR_EXTRACT
          && node[1].getKind() != kind::BITVECTOR_EXTRACT);
}

bool BVToBool::isConvertibleBvTerm(TNode node)
{
  if (!node.getType().isBitVector() || node.getType().getBitVectorSize() != 1)
    return false;

  Kind kind = node.getKind();

  if (kind == kind::CONST_BITVECTOR || kind == kind::ITE
      || kind == kind::BITVECTOR_AND
      || kind == kind::BITVECTOR_OR
      || kind == kind::BITVECTOR_NOT
      || kind == kind::BITVECTOR_XOR
      || kind == kind::BITVECTOR_COMP)
  {
    return true;
  }

  return false;
}

Node BVToBool::convertBvAtom(TNode node)
{
  Assert(node.getType().isBoolean() && node.getKind() == kind::EQUAL);
  Assert(bv::utils::getSize(node[0]) == 1);
  Assert(bv::utils::getSize(node[1]) == 1);
  Node a = convertBvTerm(node[0]);
  Node b = convertBvTerm(node[1]);
  Node result = NodeManager::currentNM()->mkNode(kind::EQUAL, a, b);
  Debug("bv-to-bool") << "BVToBool::convertBvAtom " << node << " => " << result
                      << "\n";

  ++(d_statistics.d_numAtomsLifted);
  return result;
}

Node BVToBool::convertBvTerm(TNode node)
{
  Assert(node.getType().isBitVector()
         && node.getType().getBitVectorSize() == 1);

  if (hasBoolCache(node)) return getBoolCache(node);

  NodeManager* nm = NodeManager::currentNM();

  if (!isConvertibleBvTerm(node))
  {
    ++(d_statistics.d_numTermsForcedLifted);
    Node result = nm->mkNode(kind::EQUAL, node, d_one);
    addToBoolCache(node, result);
    Debug("bv-to-bool") << "BVToBool::convertBvTerm " << node << " => "
                        << result << "\n";
    return result;
  }

  if (node.getNumChildren() == 0)
  {
    Assert(node.getKind() == kind::CONST_BITVECTOR);
    Node result = node == d_one ? bv::utils::mkTrue() : bv::utils::mkFalse();
    // addToCache(node, result);
    Debug("bv-to-bool") << "BVToBool::convertBvTerm " << node << " => "
                        << result << "\n";
    return result;
  }

  ++(d_statistics.d_numTermsLifted);

  Kind kind = node.getKind();
  if (kind == kind::ITE)
  {
    Node cond = liftNode(node[0]);
    Node true_branch = convertBvTerm(node[1]);
    Node false_branch = convertBvTerm(node[2]);
    Node result = nm->mkNode(kind::ITE, cond, true_branch, false_branch);
    addToBoolCache(node, result);
    Debug("bv-to-bool") << "BVToBool::convertBvTerm " << node << " => "
                        << result << "\n";
    return result;
  }

  Kind new_kind;
  // special case for XOR as it has to be binary
  // while BITVECTOR_XOR can be n-ary
  if (kind == kind::BITVECTOR_XOR)
  {
    new_kind = kind::XOR;
    Node result = convertBvTerm(node[0]);
    for (unsigned i = 1; i < node.getNumChildren(); ++i)
    {
      Node converted = convertBvTerm(node[i]);
      result = nm->mkNode(kind::XOR, result, converted);
    }
    Debug("bv-to-bool") << "BVToBool::convertBvTerm " << node << " => "
                        << result << "\n";
    return result;
  }

  if (kind == kind::BITVECTOR_COMP)
  {
    Node result = nm->mkNode(kind::EQUAL, node[0], node[1]);
    addToBoolCache(node, result);
    Debug("bv-to-bool") << "BVToBool::convertBvTerm " << node << " => "
                        << result << "\n";
    return result;
  }

  switch (kind)
  {
    case kind::BITVECTOR_OR: new_kind = kind::OR; break;
    case kind::BITVECTOR_AND: new_kind = kind::AND; break;
    case kind::BITVECTOR_NOT: new_kind = kind::NOT; break;
    default: Unhandled();
  }

  NodeBuilder<> builder(new_kind);
  for (unsigned i = 0; i < node.getNumChildren(); ++i)
  {
    builder << convertBvTerm(node[i]);
  }

  Node result = builder;
  addToBoolCache(node, result);
  Debug("bv-to-bool") << "BVToBool::convertBvTerm " << node << " => " << result
                      << "\n";
  return result;
}

Node BVToBool::liftNode(TNode current)
{
  Node result;

  if (hasLiftCache(current))
  {
    result = getLiftCache(current);
  }
  else if (isConvertibleBvAtom(current))
  {
    result = convertBvAtom(current);
    addToLiftCache(current, result);
  }
  else
  {
    if (current.getNumChildren() == 0)
    {
      result = current;
    }
    else
    {
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        builder << current.getOperator();
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        // Recursively lift children
        Node converted = liftNode(current[i]);
        Assert(converted.getType() == current[i].getType());
        builder << converted;
      }
      result = builder;
      addToLiftCache(current, result);
    }
  }
  Assert(result != Node());
  Assert(result.getType() == current.getType());
  Debug("bv-to-bool") << "BVToBool::liftNode " << current << " => \n"
                      << result << "\n";
  return result;
}

void BVToBool::liftBvToBool(const std::vector<Node>& assertions,
                            std::vector<Node>& new_assertions)
{
  for (unsigned i = 0; i < assertions.size(); ++i)
  {
    Node new_assertion = liftNode(assertions[i]);
    new_assertions.push_back(Rewriter::rewrite(new_assertion));
    Trace("bv-to-bool") << "  " << assertions[i] << " => " << new_assertions[i]
                        << "\n";
  }
}

BVToBool::Statistics::Statistics()
    : d_numTermsLifted("preprocessing::passes::BVToBool::NumTermsLifted", 0),
      d_numAtomsLifted("preprocessing::passes::BVToBool::NumAtomsLifted", 0),
      d_numTermsForcedLifted(
          "preprocessing::passes::BVToBool::NumTermsForcedLifted", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numTermsLifted);
  smtStatisticsRegistry()->registerStat(&d_numAtomsLifted);
  smtStatisticsRegistry()->registerStat(&d_numTermsForcedLifted);
}

BVToBool::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_numTermsLifted);
  smtStatisticsRegistry()->unregisterStat(&d_numAtomsLifted);
  smtStatisticsRegistry()->unregisterStat(&d_numTermsForcedLifted);
}


}  // passes
}  // Preprocessing
}  // CVC4
