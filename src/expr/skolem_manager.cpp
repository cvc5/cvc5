/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
#include "expr/sort_to_term.h"
#include "util/rational.h"
#include "util/string.h"

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
    case SkolemFunId::INPUT_VARIABLE: return "INPUT_VARIABLE";
    case SkolemFunId::PURIFY: return "PURIFY";
    case SkolemFunId::ABSTRACT_VALUE: return "ABSTRACT_VALUE";
    case SkolemFunId::ARRAY_DEQ_DIFF: return "ARRAY_DEQ_DIFF";
    case SkolemFunId::DIV_BY_ZERO: return "DIV_BY_ZERO";
    case SkolemFunId::INT_DIV_BY_ZERO: return "INT_DIV_BY_ZERO";
    case SkolemFunId::MOD_BY_ZERO: return "MOD_BY_ZERO";
    case SkolemFunId::SQRT: return "SQRT";
    case SkolemFunId::TRANSCENDENTAL_PURIFY_ARG:
      return "TRANSCENDENTAL_PURIFY_ARG";
    case SkolemFunId::QUANTIFIERS_SKOLEMIZE: return "QUANTIFIERS_SKOLEMIZE";
    case SkolemFunId::STRINGS_NUM_OCCUR: return "STRINGS_NUM_OCCUR";
    case SkolemFunId::STRINGS_NUM_OCCUR_RE: return "STRINGS_NUM_OCCUR_RE";
    case SkolemFunId::STRINGS_OCCUR_INDEX: return "STRINGS_OCCUR_INDEX";
    case SkolemFunId::STRINGS_OCCUR_INDEX_RE: return "STRINGS_OCCUR_INDEX_RE";
    case SkolemFunId::STRINGS_OCCUR_LEN: return "STRINGS_OCCUR_LEN";
    case SkolemFunId::STRINGS_OCCUR_LEN_RE: return "STRINGS_OCCUR_LEN_RE";
    case SkolemFunId::STRINGS_DEQ_DIFF: return "STRINGS_DEQ_DIFF";
    case SkolemFunId::STRINGS_REPLACE_ALL_RESULT:
      return "STRINGS_REPLACE_ALL_RESULT";
    case SkolemFunId::STRINGS_ITOS_RESULT: return "STRINGS_ITOS_RESULT";
    case SkolemFunId::STRINGS_STOI_RESULT: return "STRINGS_STOI_RESULT";
    case SkolemFunId::STRINGS_STOI_NON_DIGIT: return "STRINGS_STOI_NON_DIGIT";
    case SkolemFunId::RE_FIRST_MATCH_PRE: return "RE_FIRST_MATCH_PRE";
    case SkolemFunId::RE_FIRST_MATCH: return "RE_FIRST_MATCH";
    case SkolemFunId::RE_FIRST_MATCH_POST: return "RE_FIRST_MATCH_POST";
    case SkolemFunId::RE_UNFOLD_POS_COMPONENT: return "RE_UNFOLD_POS_COMPONENT";
    case SkolemFunId::BAGS_CARD_COMBINE: return "BAGS_CARD_COMBINE";
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
    case SkolemFunId::BAGS_MAP_PREIMAGE_INJECTIVE:
      return "BAGS_MAP_PREIMAGE_INJECTIVE";
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
    case SkolemFunId::SHARED_SELECTOR: return "SHARED_SELECTOR";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, SkolemFunId id)
{
  out << toString(id);
  return out;
}

const char* toString(InternalSkolemFunId id)
{
  switch (id)
  {
    case InternalSkolemFunId::SEQ_MODEL_BASE_ELEMENT:
      return "SEQ_MODEL_BASE_ELEMENT";
    case InternalSkolemFunId::IEVAL_NONE: return "IEVAL_NONE";
    case InternalSkolemFunId::IEVAL_SOME: return "IEVAL_SOME";
    case InternalSkolemFunId::SYGUS_ANY_CONSTANT: return "SYGUS_ANY_CONSTANT";
    case InternalSkolemFunId::QUANTIFIERS_SYNTH_FUN_EMBED:
      return "QUANTIFIERS_SYNTH_FUN_EMBED";
    case InternalSkolemFunId::HO_TYPE_MATCH_PRED: return "HO_TYPE_MATCH_PRED";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, InternalSkolemFunId id)
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
  if (t.getKind() == Kind::WITNESS)
  {
    // The purification skolem for (witness ((x T)) P) is the same as
    // the skolem function (QUANTIFIERS_SKOLEMIZE (exists ((x T)) P) 0).
    NodeManager* nm = NodeManager::currentNM();
    Node exists =
        nm->mkNode(Kind::EXISTS, std::vector<Node>(t.begin(), t.end()));
    k = mkSkolemFunction(SkolemFunId::QUANTIFIERS_SKOLEMIZE,
                         {exists, nm->mkConstInt(Rational(0))});
    // store the proof generator if it exists
    if (pg != nullptr)
    {
      d_gens[exists] = pg;
    }
    UnpurifiedFormAttribute ufa;
    k.setAttribute(ufa, t);
  }
  else
  {
    k = mkSkolemFunction(SkolemFunId::PURIFY, {t});
    // shouldn't provide proof generators for other terms
    Assert(pg == nullptr);
  }
  Trace("sk-manager-skolem") << "skolem: " << k << " purify " << t << std::endl;
  return k;
}

Node SkolemManager::mkSkolemFunction(SkolemFunId id, Node cacheVal)
{
  std::vector<Node> cvals;
  if (!cacheVal.isNull())
  {
    if (cacheVal.getKind() == Kind::SEXPR)
    {
      cvals.insert(cvals.end(), cacheVal.begin(), cacheVal.end());
    }
    else
    {
      cvals.push_back(cacheVal);
    }
  }
  TypeNode ctn = getTypeFor(id, cvals);
  Assert(!ctn.isNull());
  return mkSkolemFunctionTyped(id, ctn, cacheVal);
}

Node SkolemManager::mkSkolemFunction(SkolemFunId id,
                                     const std::vector<Node>& cacheVals)
{
  TypeNode ctn = getTypeFor(id, cacheVals);
  Assert(!ctn.isNull());
  return mkSkolemFunctionTyped(id, ctn, cacheVals);
}

Node SkolemManager::mkInternalSkolemFunction(InternalSkolemFunId id,
                                             TypeNode tn,
                                             const std::vector<Node>& cacheVals)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> cvals;
  cvals.push_back(nm->mkConstInt(Rational(static_cast<uint32_t>(id))));
  cvals.insert(cvals.end(), cacheVals.begin(), cacheVals.end());
  return mkSkolemFunctionTyped(SkolemFunId::INTERNAL, tn, cvals);
}

Node SkolemManager::mkSkolemFunctionTyped(SkolemFunId id,
                                          TypeNode tn,
                                          Node cacheVal)
{
  std::tuple<SkolemFunId, TypeNode, Node> key(id, tn, cacheVal);
  std::map<std::tuple<SkolemFunId, TypeNode, Node>, Node>::iterator it =
      d_skolemFuns.find(key);
  if (it == d_skolemFuns.end())
  {
    Node k;
    // For now, INPUT_VARIABLE is a special case that constructs a variable
    // of the original name.
    if (id == SkolemFunId::INPUT_VARIABLE)
    {
      k = mkSkolemNode(Kind::VARIABLE,
                       cacheVal[0].getConst<String>().toString(),
                       tn,
                       SKOLEM_EXACT_NAME);
    }
    else
    {
      // we use @ as a prefix, which follows the SMT-LIB standard indicating
      // internal symbols starting with @ or . are reserved for internal use.
      std::stringstream ss;
      ss << "@" << id;
      k = mkSkolemNode(Kind::SKOLEM, ss.str(), tn);
    }
    if (id == SkolemFunId::PURIFY)
    {
      Assert(cacheVal.getType() == tn);
      // set unpurified form attribute for k
      UnpurifiedFormAttribute ufa;
      k.setAttribute(ufa, cacheVal);
      // the original form of k can be computed by calling getOriginalForm, but
      // it is not computed here
    }
    d_skolemFuns[key] = k;
    d_skolemFunMap[k] = key;
    Trace("sk-manager-skolem") << "mkSkolemFunction(" << id << ", " << cacheVal
                               << ") returns " << k << std::endl;
    return k;
  }
  return it->second;
}

Node SkolemManager::mkSkolemFunctionTyped(SkolemFunId id,
                                          TypeNode tn,
                                          const std::vector<Node>& cacheVals)
{
  Node cacheVal;
  // use null node if cacheVals is empty
  if (!cacheVals.empty())
  {
    cacheVal = cacheVals.size() == 1
                   ? cacheVals[0]
                   : NodeManager::currentNM()->mkNode(Kind::SEXPR, cacheVals);
  }
  return mkSkolemFunctionTyped(id, tn, cacheVal);
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

InternalSkolemFunId SkolemManager::getInternalId(TNode k) const
{
  SkolemFunId id;
  Node cacheVal;
  // if its an internal skolem
  if (isSkolemFunction(k, id, cacheVal) && id == SkolemFunId::INTERNAL)
  {
    Assert(!cacheVal.isNull());
    Node cval = cacheVal.getKind() == Kind::SEXPR ? cacheVal[0] : cacheVal;
    Assert(cval.getKind() == Kind::CONST_INTEGER);
    Rational r = cval.getConst<Rational>();
    Assert(r.sgn() >= 0 && r.getNumerator().fitsUnsignedInt());
    return static_cast<InternalSkolemFunId>(r.getNumerator().toUnsignedInt());
  }
  return InternalSkolemFunId::NONE;
}

Node SkolemManager::mkDummySkolem(const std::string& prefix,
                                  const TypeNode& type,
                                  const std::string& comment,
                                  int flags)
{
  return mkSkolemNode(Kind::SKOLEM, prefix, type, flags);
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

Node SkolemManager::mkSkolemNode(Kind k,
                                 const std::string& prefix,
                                 const TypeNode& type,
                                 int flags)
{
  NodeManager* nm = NodeManager::currentNM();
  Node n = NodeBuilder(nm, k);
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

TypeNode SkolemManager::getTypeFor(SkolemFunId id,
                                   const std::vector<Node>& cacheVals)
{
  NodeManager* nm = NodeManager::currentNM();
  switch (id)
  {
    // Type(cacheVals[0]), i.e skolems that return same type as first argument
    case SkolemFunId::PURIFY:
    case SkolemFunId::ABSTRACT_VALUE:
      Assert(cacheVals.size() > 0);
      return cacheVals[0].getType();
      break;
    // Type(cacheVals[1])
    case SkolemFunId::INPUT_VARIABLE:
      Assert(cacheVals.size() == 2
             && cacheVals[1].getKind() == Kind::SORT_TO_TERM);
      return cacheVals[1].getConst<SortToTerm>().getType();
      break;
    // real -> real function
    case SkolemFunId::DIV_BY_ZERO:
    case SkolemFunId::SQRT:
    {
      TypeNode rtype = nm->realType();
      return nm->mkFunctionType(rtype, rtype);
    }
    // real skolems
    case SkolemFunId::TRANSCENDENTAL_PURIFY_ARG: return nm->realType();
    // int -> int function
    case SkolemFunId::INT_DIV_BY_ZERO:
    case SkolemFunId::MOD_BY_ZERO:
    case SkolemFunId::STRINGS_OCCUR_INDEX:
    case SkolemFunId::STRINGS_OCCUR_INDEX_RE:
    case SkolemFunId::STRINGS_OCCUR_LEN:
    case SkolemFunId::STRINGS_OCCUR_LEN_RE:
    case SkolemFunId::STRINGS_STOI_RESULT:
    case SkolemFunId::STRINGS_ITOS_RESULT:
    case SkolemFunId::BAGS_MAP_SUM:
    case SkolemFunId::BAGS_CARD_COMBINE:
    {
      TypeNode itype = nm->integerType();
      return nm->mkFunctionType(itype, itype);
    }
    // int -> Type(args[0])
    case SkolemFunId::STRINGS_REPLACE_ALL_RESULT:
    {
      Assert(cacheVals.size() > 0);
      TypeNode itype = nm->integerType();
      return nm->mkFunctionType(itype, cacheVals[0].getType());
    }
    // integer skolems
    case SkolemFunId::STRINGS_NUM_OCCUR:
    case SkolemFunId::STRINGS_NUM_OCCUR_RE:
    case SkolemFunId::STRINGS_DEQ_DIFF:
    case SkolemFunId::STRINGS_STOI_NON_DIGIT:
    case SkolemFunId::BAGS_FOLD_CARD:
    case SkolemFunId::SETS_FOLD_CARD:
    case SkolemFunId::BAGS_MAP_PREIMAGE_SIZE:
    case SkolemFunId::BAGS_MAP_PREIMAGE_INDEX:
    case SkolemFunId::BAGS_CARD_N: return nm->integerType();
    // string skolems
    case SkolemFunId::RE_FIRST_MATCH_PRE:
    case SkolemFunId::RE_FIRST_MATCH:
    case SkolemFunId::RE_FIRST_MATCH_POST:
    case SkolemFunId::RE_UNFOLD_POS_COMPONENT: return nm->stringType();
    case SkolemFunId::ARRAY_DEQ_DIFF:
    {
      Assert(cacheVals.size() == 2);
      TypeNode atype = cacheVals[0].getType();
      Assert(atype.isArray());
      return atype.getArrayIndexType();
    }
    case SkolemFunId::QUANTIFIERS_SKOLEMIZE:
    {
      Assert(cacheVals.size() == 2);
      Node vi = cacheVals[1];
      if (vi.getKind() == Kind::CONST_INTEGER
          && vi.getConst<Rational>().sgn() >= 0
          && vi.getConst<Rational>().getNumerator().fitsUnsignedInt())
      {
        uint32_t i = vi.getConst<Rational>().getNumerator().toUnsignedInt();
        Assert(cacheVals[0].getKind() == Kind::EXISTS
               && i < cacheVals[0][0].getNumChildren());
        return cacheVals[0][0][i].getType();
      }
    }
    break;
    // skolems that return the set element type
    case SkolemFunId::BAGS_DEQ_DIFF:
    case SkolemFunId::SETS_DEQ_DIFF:
    {
      Assert(cacheVals.size() > 0);
      TypeNode stype = cacheVals[0].getType();
      Assert(stype.getNumChildren() == 1);
      return stype[0];
    }
    // skolems that return the set to set element type
    case SkolemFunId::BAGS_CHOOSE:
    case SkolemFunId::SETS_CHOOSE:
    {
      Assert(cacheVals.size() > 0);
      TypeNode stype = cacheVals[0].getType();
      Assert(stype.getNumChildren() == 1);
      return nm->mkFunctionType(stype, stype[0]);
    }
    case SkolemFunId::TABLES_GROUP_PART:
    case SkolemFunId::RELATIONS_GROUP_PART:
    {
      Assert(cacheVals.size() > 0);
      TypeNode stype = cacheVals[0].getType();
      Assert(stype.getNumChildren() == 1);
      stype = stype[0];
      Assert(stype.getNumChildren() == 1);
      return nm->mkFunctionType(stype[0], stype);
    }
    // skolems that return the set element of set element type
    case SkolemFunId::TABLES_GROUP_PART_ELEMENT:
    case SkolemFunId::RELATIONS_GROUP_PART_ELEMENT:
    {
      Assert(cacheVals.size() > 0);
      TypeNode stype = cacheVals[0].getType();
      Assert(stype.getNumChildren() == 1);
      stype = stype[0];
      Assert(stype.getNumChildren() == 1);
      return stype[0];
    }
    case SkolemFunId::SETS_MAP_DOWN_ELEMENT:
    {
      Assert(cacheVals.size() == 2 && cacheVals[0].getKind() == Kind::SET_MAP);
      TypeNode stype = cacheVals[0][1].getType();
      Assert(stype.isSet());
      return stype.getSetElementType();
    }
    case SkolemFunId::BAGS_FOLD_UNION_DISJOINT:
    case SkolemFunId::SETS_FOLD_UNION:
    case SkolemFunId::BAGS_CARD_UNION_DISJOINT:
    {
      Assert(cacheVals.size() > 0);
      TypeNode itype = nm->integerType();
      return nm->mkFunctionType(itype, cacheVals[0].getType());
    }
    case SkolemFunId::BAGS_FOLD_ELEMENTS:
    case SkolemFunId::SETS_FOLD_ELEMENTS:
    case SkolemFunId::BAGS_CARD_ELEMENTS:
    {
      Assert(cacheVals.size() > 0);
      TypeNode itype = nm->integerType();
      TypeNode stype = cacheVals[0].getType();
      Assert(stype.getNumChildren() == 1);
      return nm->mkFunctionType(itype, stype[0]);
    }
    case SkolemFunId::BAGS_FOLD_COMBINE:
    case SkolemFunId::SETS_FOLD_COMBINE:
    {
      Assert(cacheVals.size() == 3);
      TypeNode itype = nm->integerType();
      return nm->mkFunctionType(itype, cacheVals[1].getType());
    }
    case SkolemFunId::BAGS_MAP_PREIMAGE:
    {
      TypeNode itype = nm->integerType();
      Assert (cacheVals[0].getType().isFunction());
      TypeNode retType = cacheVals[0].getType().getArgTypes()[0];
      return nm->mkFunctionType(itype, retType);
    }
    case SkolemFunId::BAGS_MAP_PREIMAGE_INJECTIVE:
    {
      Assert (cacheVals[0].getType().isFunction());
      return cacheVals[0].getType().getArgTypes()[0];
    }
    case SkolemFunId::SHARED_SELECTOR:
    {
      Assert(cacheVals.size() == 3);
      Assert(cacheVals[0].getKind() == Kind::SORT_TO_TERM);
      Assert(cacheVals[1].getKind() == Kind::SORT_TO_TERM);
      TypeNode dtt = cacheVals[0].getConst<SortToTerm>().getType();
      TypeNode t = cacheVals[1].getConst<SortToTerm>().getType();
      return nm->mkSelectorType(dtt, t);
    }
    default: break;
  }
  TypeNode ret;
  return ret;
}

}  // namespace cvc5::internal
