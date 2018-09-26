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
        i, Rewriter::rewrite(newLowerIte(assertionsToPreprocess->operator[](i))));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

Node IteToBvite::newLowerIte(TNode a)
{
  // TODO: optimization if visited & ite_cond then all children are ite_cond
  //       where ite_cond keeps track of whether it's in an ite condition
  NodeManager* nm = NodeManager::currentNM();
  std::vector<TNode> terms;
  terms.push_back(a);
  std::unordered_set<TNode, TNodeHashFunction> visited;
  while(!terms.empty())
  {
    TNode n = terms.back();
    terms.pop_back();
    Kind k = n.getKind();
    Debug("ite-to-bvite") << "IteToBvite Post-traversal with " << n << " and visited = " << visited.count(n) << std::endl;

    // TODO: Optimization: if it's a leaf, then don't need to wait for visited=1 to do the work

    if (visited.count(n) == 0)
    {
      visited.insert(n);
      terms.push_back(n);
      for (const Node& nn : n)
      {
        terms.push_back(nn);
      }
    }

    else
    {
      TypeNode t = n.getType();
      if ((t.isBitVector() || t.isBoolean()) && (n.getNumChildren() == 0))
      {
        if (k == kind::CONST_BOOLEAN)
        {
          d_lowerCache[n] = nm->mkNode(kind::ITE, n, bv::utils::mkOne(1), bv::utils::mkZero(1));
          // TODO: This isn't quite right because might be thrown away in ite option
          ++(d_statistics.d_numTermsForcedLowered);
        }
        // if it's already a bit-vector with no children, we don't need to do anything
      }
      else
      {
        Assert(n.getNumChildren() > 0);

        bool all_bv = true;
        // check if it converted all children to bitvectors
        for (const Node& nn : n)
        {
          all_bv = all_bv && fromCache(nn).getType().isBitVector();
        }

        Debug("ite-to-bvite") << "IteToBvite: Checking " << n << " with all_bv = " << all_bv << std::endl;

        if (all_bv)
        {
          Kind new_kind = k;
          switch(k)
          {
          case kind::EQUAL: new_kind = kind::BITVECTOR_COMP; break;
          case kind::AND: new_kind = kind::BITVECTOR_AND; break;
          case kind::OR: new_kind = kind::BITVECTOR_OR; break;
          case kind::NOT: new_kind = kind::BITVECTOR_NOT; break;
          case kind::XOR: new_kind = kind::BITVECTOR_XOR; break;
          case kind::IMPLIES: new_kind = kind::BITVECTOR_OR; break;
          case kind::ITE: new_kind = kind::BITVECTOR_ITE; break;
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

          Debug("ite-to-bvite") << "IteToBvite: Processing " << n << " with new_kind = " << new_kind << std::endl;

          // TODO: Investigate this optimization
          // might not always hold...could already be a bit-vector op, but nested structure needs to be updated
          // if (new_kind == k)
          // {
          //   // don't need to rebuild
          //   continue;
          // }

          NodeBuilder<> builder(new_kind);
          if (new_kind != k)
          {
            // FIXME: This isn't quite right for the ite optimization because it might be thrown away
            ++(d_statistics.d_numTermsLowered);
          }

          // TODO: Figure out if this is necessary
          if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
          {
            builder << n.getOperator();
          }

          // special case IMPLIES because needs to be rewritten
          if (k == kind::IMPLIES)
          {
            builder << nm->mkNode(kind::BITVECTOR_NOT, fromCache(n[0]));
            builder << fromCache(n[1]);
          }
          else
          {
            for (const Node &nn : n)
            {
              builder << fromCache(nn);
            }
          }

          d_lowerCache[n] = builder;
        }
      }
    }
  }

  return nm->mkNode(kind::EQUAL, fromCache(a), bv::utils::mkOne(1));
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

Node IteToBvite::fromCache(TNode n)
{
  if (d_lowerCache.find(n) != d_lowerCache.end())
  {
    return d_lowerCache.find(n)->second;
  }
  return n;
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
