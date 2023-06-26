/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of skolem manager class.
 */

#include "expr/skolem_manager.h"

#include <sstream>

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager_attributes.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

struct OriginalFormAttributeId
{
};
typedef expr::Attribute<OriginalFormAttributeId, Node> OriginalFormAttribute;

struct UnpurifiedFormAttributeId
{
};
typedef expr::Attribute<UnpurifiedFormAttributeId, Node> UnpurifiedFormAttribute;

const char* toString(SkolemFunId id)
{
  switch (id)
  {
    case SkolemFunId::PURIFY: return "PURIFY";
    case SkolemFunId::ARRAY_DEQ_DIFF: return "ARRAY_DEQ_DIFF";
    case SkolemFunId::DIV_BY_ZERO: return "DIV_BY_ZERO";
    case SkolemFunId::INT_DIV_BY_ZERO: return "INT_DIV_BY_ZERO";
    case SkolemFunId::MOD_BY_ZERO: return "MOD_BY_ZERO";
    case SkolemFunId::SQRT: return "SQRT";
    case SkolemFunId::TRANSCENDENTAL_PURIFY_ARG:
      return "TRANSCENDENTAL_PURIFY_ARG";
    case SkolemFunId::SHARED_SELECTOR: return "SHARED_SELECTOR";
    case SkolemFunId::QUANTIFIERS_SKOLEMIZE: return "QUANTIFIERS_SKOLEMIZE";
    case SkolemFunId::QUANTIFIERS_SYNTH_FUN_EMBED:
      return "QUANTIFIERS_SYNTH_FUN_EMBED";
    case SkolemFunId::STRINGS_NUM_OCCUR: return "STRINGS_NUM_OCCUR";
    case SkolemFunId::STRINGS_OCCUR_INDEX: return "STRINGS_OCCUR_INDEX";
    case SkolemFunId::STRINGS_OCCUR_LEN: return "STRINGS_OCCUR_LEN";
    case SkolemFunId::STRINGS_DEQ_DIFF: return "STRINGS_DEQ_DIFF";
    case SkolemFunId::STRINGS_REPLACE_ALL_RESULT:
      return "STRINGS_REPLACE_ALL_RESULT";
    case SkolemFunId::STRINGS_ITOS_RESULT: return "STRINGS_ITOS_RESULT";
    case SkolemFunId::STRINGS_STOI_RESULT: return "STRINGS_STOI_RESULT";
    case SkolemFunId::STRINGS_STOI_NON_DIGIT: return "STRINGS_STOI_NON_DIGIT";
    case SkolemFunId::SK_FIRST_MATCH_PRE: return "SK_FIRST_MATCH_PRE";
    case SkolemFunId::SK_FIRST_MATCH: return "SK_FIRST_MATCH";
    case SkolemFunId::SK_FIRST_MATCH_POST: return "SK_FIRST_MATCH_POST";
    case SkolemFunId::RE_UNFOLD_POS_COMPONENT: return "RE_UNFOLD_POS_COMPONENT";
    case SkolemFunId::SEQ_MODEL_BASE_ELEMENT: return "SEQ_MODEL_BASE_ELEMENT";
    case SkolemFunId::BAGS_CARD_CARDINALITY: return "BAGS_CARD_CARDINALITY";
    case SkolemFunId::BAGS_CARD_ELEMENTS: return "BAGS_CARD_ELEMENTS";
    case SkolemFunId::BAGS_CARD_N: return "BAGS_CARD_N";
    case SkolemFunId::BAGS_CARD_UNION_DISJOINT:
      return "BAGS_CARD_UNION_DISJOINT";
    case SkolemFunId::BAGS_CHOOSE: return "BAGS_CHOOSE";
    case SkolemFunId::BAGS_FOLD_CARD: return "BAGS_FOLD_CARD";
    case SkolemFunId::BAGS_FOLD_COMBINE: return "BAGS_FOLD_COMBINE";
    case SkolemFunId::BAGS_FOLD_ELEMENTS: return "BAGS_FOLD_ELEMENTS";
    case SkolemFunId::BAGS_FOLD_UNION_DISJOINT: return "BAGS_FOLD_UNION_DISJOINT";
    case SkolemFunId::BAGS_MAP_PREIMAGE: return "BAGS_MAP_PREIMAGE";
    case SkolemFunId::BAGS_MAP_PREIMAGE_SIZE: return "BAGS_MAP_PREIMAGE_SIZE";
    case SkolemFunId::BAGS_MAP_PREIMAGE_INDEX: return "BAGS_MAP_PREIMAGE_INDEX";
    case SkolemFunId::BAGS_MAP_SUM: return "BAGS_MAP_SUM";
    case SkolemFunId::BAGS_DEQ_DIFF: return "BAGS_DEQ_DIFF";
    case SkolemFunId::TABLES_GROUP_PART: return "TABLES_GROUP_PART";
    case SkolemFunId::TABLES_GROUP_PART_ELEMENT:
      return "TABLES_GROUP_PART_ELEMENT";
    case SkolemFunId::RELATIONS_GROUP_PART: return "RELATIONS_GROUP_PART";
    case SkolemFunId::RELATIONS_GROUP_PART_ELEMENT:
      return "RELATIONS_GROUP_PART_ELEMENT";
    case SkolemFunId::SETS_CHOOSE: return "SETS_CHOOSE";
    case SkolemFunId::SETS_DEQ_DIFF: return "SETS_DEQ_DIFF";
    case SkolemFunId::SETS_FOLD_CARD: return "SETS_FOLD_CARD";
    case SkolemFunId::SETS_FOLD_COMBINE: return "SETS_FOLD_COMBINE";
    case SkolemFunId::SETS_FOLD_ELEMENTS: return "SETS_FOLD_ELEMENTS";
    case SkolemFunId::SETS_FOLD_UNION: return "SETS_FOLD_UNION";
    case SkolemFunId::SETS_MAP_DOWN_ELEMENT: return "SETS_MAP_DOWN_ELEMENT";
    case SkolemFunId::HO_TYPE_MATCH_PRED: return "HO_TYPE_MATCH_PRED";
    case SkolemFunId::IEVAL_NONE: return "IEVAL_NONE";
    case SkolemFunId::IEVAL_SOME: return "IEVAL_SOME";
    case SkolemFunId::ABSTRACT_VALUE: return "ABSTRACT_VALUE";
    case SkolemFunId::SYGUS_ANY_CONSTANT: return "SYGUS_ANY_CONSTANT";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, SkolemFunId id)
{
  out << toString(id);
  return out;
}

SkolemManager::SkolemManager() : d_skolemCounter(0) {}

Node SkolemManager::mkPurifySkolem(Node t,
                                   ProofGenerator* pg)
{
  // We do not recursively compute the original form of t here
  Node k;
  if (t.getKind() == WITNESS)
  {
    // The purification skolem for (witness ((x T)) P) is the same as
    // the skolem function (QUANTIFIERS_SKOLEMIZE (exists ((x T)) P) 0).
    NodeManager* nm = NodeManager::currentNM();
    Node exists = nm->mkNode(EXISTS, std::vector<Node>(t.begin(), t.end()));
    k = mkSkolemFunction(SkolemFunId::QUANTIFIERS_SKOLEMIZE,
                         t.getType(),
                         {exists, nm->mkConstInt(Rational(0))});
    // store the proof generator if it exists
    if (pg != nullptr)
    {
      d_gens[exists] = pg;
    }
  }
  else
  {
    k = mkSkolemFunction(SkolemFunId::PURIFY, t.getType(), {t});
    // shouldn't provide proof generators for other terms
    Assert(pg == nullptr);
  }
  // set unpurified form attribute for k
  UnpurifiedFormAttribute ufa;
  k.setAttribute(ufa, t);
  // the original form of k can be computed by calling getOriginalForm, but
  // it is not computed here

  Trace("sk-manager-skolem")
      << "skolem: " << k << " purify " << t << std::endl;
  return k;
}

Node SkolemManager::mkSkolemFunction(SkolemFunId id, TypeNode tn, Node cacheVal)
{
  std::tuple<SkolemFunId, TypeNode, Node> key(id, tn, cacheVal);
  std::map<std::tuple<SkolemFunId, TypeNode, Node>, Node>::iterator it =
      d_skolemFuns.find(key);
  if (it == d_skolemFuns.end())
  {
    // we use @ as a prefix, which follows the SMT-LIB standard indicating
    // internal symbols starting with @ or . are reserved for internal use.
    std::stringstream ss;
    ss << "@" << id;
    Node k = mkSkolemNode(
        ss.str(), tn, "an internal skolem function", SKOLEM_DEFAULT);
    d_skolemFuns[key] = k;
    d_skolemFunMap[k] = key;
    Trace("sk-manager-skolem") << "mkSkolemFunction(" << id << ", " << cacheVal
                               << ") returns " << k << std::endl;
    return k;
  }
  return it->second;
}

Node SkolemManager::mkSkolemFunction(SkolemFunId id,
                                     TypeNode tn,
                                     const std::vector<Node>& cacheVals)
{
  Node cacheVal;
  // use null node if cacheVals is empty
  if (!cacheVals.empty())
  {
    cacheVal = cacheVals.size() == 1
                   ? cacheVals[0]
                   : NodeManager::currentNM()->mkNode(SEXPR, cacheVals);
  }
  return mkSkolemFunction(id, tn, cacheVal);
}

bool SkolemManager::isSkolemFunction(TNode k,
                                     SkolemFunId& id,
                                     Node& cacheVal) const
{
  std::map<Node, std::tuple<SkolemFunId, TypeNode, Node>>::const_iterator it =
      d_skolemFunMap.find(k);
  if (it == d_skolemFunMap.end())
  {
    return false;
  }
  id = std::get<0>(it->second);
  cacheVal = std::get<2>(it->second);
  return true;
}

SkolemFunId SkolemManager::getId(TNode k) const
{
  SkolemFunId id;
  Node cacheVal;
  if (isSkolemFunction(k, id, cacheVal))
  {
    return id;
  }
  return SkolemFunId::NONE;
}

Node SkolemManager::mkDummySkolem(const std::string& prefix,
                                  const TypeNode& type,
                                  const std::string& comment,
                                  int flags)
{
  return mkSkolemNode(prefix, type, comment, flags);
}

ProofGenerator* SkolemManager::getProofGenerator(Node t) const
{
  std::map<Node, ProofGenerator*>::const_iterator it = d_gens.find(t);
  if (it != d_gens.end())
  {
    return it->second;
  }
  return nullptr;
}

bool SkolemManager::isAbstractValue(TNode n) const
{
  SkolemFunId id;
  Node cacheVal;
  if (isSkolemFunction(n, id, cacheVal))
  {
    return id == SkolemFunId::ABSTRACT_VALUE;
  }
  return false;
}

Node SkolemManager::getOriginalForm(Node n)
{
  if (n.isNull())
  {
    return n;
  }
  Trace("sk-manager-debug")
      << "SkolemManager::getOriginalForm " << n << std::endl;
  OriginalFormAttribute ofa;
  UnpurifiedFormAttribute ufa;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      if (cur.hasAttribute(ofa))
      {
        visited[cur] = cur.getAttribute(ofa);
      }
      else if (cur.hasAttribute(ufa))
      {
        // if it has an unpurified form, compute the original form of it
        Node ucur = cur.getAttribute(ufa);
        if (ucur.hasAttribute(ofa))
        {
          // Already computed, set. This always happens after cur is visited
          // again after computing the original form of its unpurified form.
          Node ucuro = ucur.getAttribute(ofa);
          cur.setAttribute(ofa, ucuro);
          visited[cur] = ucuro;
        }
        else
        {
          // visit ucur then visit cur again
          visit.push_back(cur);
          visit.push_back(ucur);
        }
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        if (cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          visit.push_back(cur.getOperator());
        }
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        it = visited.find(cur.getOperator());
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur.getOperator() != it->second;
        children.push_back(it->second);
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      cur.setAttribute(ofa, ret);
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  Trace("sk-manager-debug") << "..return " << visited[n] << std::endl;
  return visited[n];
}

Node SkolemManager::getUnpurifiedForm(Node k)
{
  UnpurifiedFormAttribute ufa;
  if (k.hasAttribute(ufa))
  {
    return k.getAttribute(ufa);
  }
  return k;
}

Node SkolemManager::mkSkolemNode(const std::string& prefix,
                                 const TypeNode& type,
                                 const std::string& comment,
                                 int flags)
{
  NodeManager* nm = NodeManager::currentNM();
  Node n = NodeBuilder(nm, SKOLEM);
  if ((flags & SKOLEM_EXACT_NAME) == 0)
  {
    std::stringstream name;
    name << prefix << '_' << ++d_skolemCounter;
    n.setAttribute(expr::VarNameAttr(), name.str());
  }
  else
  {
    n.setAttribute(expr::VarNameAttr(), prefix);
  }
  n.setAttribute(expr::TypeAttr(), type);
  n.setAttribute(expr::TypeCheckedAttr(), true);
  return n;
}

}  // namespace cvc5::internal
