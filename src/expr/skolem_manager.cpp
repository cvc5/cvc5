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

const char* toString(InternalSkolemId id)
{
  switch (id)
  {
    case InternalSkolemId::SEQ_MODEL_BASE_ELEMENT:
      return "SEQ_MODEL_BASE_ELEMENT";
    case InternalSkolemId::IEVAL_NONE: return "IEVAL_NONE";
    case InternalSkolemId::IEVAL_SOME: return "IEVAL_SOME";
    case InternalSkolemId::SYGUS_ANY_CONSTANT: return "SYGUS_ANY_CONSTANT";
    case InternalSkolemId::QUANTIFIERS_SYNTH_FUN_EMBED:
      return "QUANTIFIERS_SYNTH_FUN_EMBED";
    case InternalSkolemId::HO_TYPE_MATCH_PRED: return "HO_TYPE_MATCH_PRED";
    case InternalSkolemId::MBQI_INPUT: return "MBQI_INPUT";
    case InternalSkolemId::ABSTRACT_VALUE: return "ABSTRACT_VALUE";
    case InternalSkolemId::QE_CLOSED_INPUT: return "QE_CLOSED_INPUT";
    case InternalSkolemId::QUANTIFIERS_ATTRIBUTE_INTERNAL:
      return "QUANTIFIERS_ATTRIBUTE_INTERNAL";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, InternalSkolemId id)
{
  out << toString(id);
  return out;
}

SkolemManager::SkolemManager() : d_skolemCounter(0) {}

Node SkolemManager::mkPurifySkolem(Node t)
{
  // We do not recursively compute the original form of t here
  Node k = mkSkolemFunction(SkolemId::PURIFY, {t});
  Trace("sk-manager-skolem") << "skolem: " << k << " purify " << t << std::endl;
  return k;
}

Node SkolemManager::mkSkolemFunction(SkolemId id, Node cacheVal)
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
  return mkSkolemFunction(id, cvals);
}

Node SkolemManager::mkSkolemFunction(SkolemId id,
                                     const std::vector<Node>& cacheVals)
{
  TypeNode ctn = getTypeFor(id, cacheVals);
  Assert(!ctn.isNull());
  return mkSkolemFunctionTyped(id, ctn, cacheVals);
}

Node SkolemManager::mkInternalSkolemFunction(InternalSkolemId id,
                                             TypeNode tn,
                                             const std::vector<Node>& cacheVals)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> cvals;
  cvals.push_back(nm->mkConstInt(Rational(static_cast<uint32_t>(id))));
  cvals.insert(cvals.end(), cacheVals.begin(), cacheVals.end());
  return mkSkolemFunctionTyped(SkolemId::INTERNAL, tn, cvals);
}

bool SkolemManager::isCommutativeSkolemId(SkolemId id)
{
  switch (id)
  {
    case cvc5::SkolemId::ARRAY_DEQ_DIFF:
    case cvc5::SkolemId::BAGS_DEQ_DIFF:
    case cvc5::SkolemId::SETS_DEQ_DIFF:
    case cvc5::SkolemId::STRINGS_DEQ_DIFF: return true;
    default: break;
  }
  return false;
}

Node SkolemManager::mkSkolemFunctionTyped(SkolemId id,
                                          TypeNode tn,
                                          Node cacheVal)
{
  std::tuple<SkolemId, TypeNode, Node> key(id, tn, cacheVal);
  std::map<std::tuple<SkolemId, TypeNode, Node>, Node>::iterator it =
      d_skolemFuns.find(key);
  if (it == d_skolemFuns.end())
  {
    // We use @ as a prefix, which follows the SMT-LIB standard indicating
    // internal symbols starting with @ or . are reserved for internal use.
    //
    std::stringstream ss;
    // Print internal skolems by the internal identifier, otherwise all would
    // be @INTERNAL_*.
    if (id == SkolemId::INTERNAL)
    {
      Node cval = cacheVal.getKind() == Kind::SEXPR ? cacheVal[0] : cacheVal;
      Assert(cval.getKind() == Kind::CONST_INTEGER);
      Rational r = cval.getConst<Rational>();
      Assert(r.sgn() >= 0 && r.getNumerator().fitsUnsignedInt());
      ss << "@"
         << static_cast<InternalSkolemId>(r.getNumerator().toUnsignedInt());
    }
    else
    {
      ss << "@" << id;
    }
    Node k = mkSkolemNode(Kind::SKOLEM, ss.str(), tn);
    if (id == SkolemId::PURIFY)
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

Node SkolemManager::mkSkolemFunctionTyped(SkolemId id,
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

bool SkolemManager::isSkolemFunction(TNode k) const
{
  return k.getKind() == Kind::SKOLEM;
}

bool SkolemManager::isSkolemFunction(TNode k,
                                     SkolemId& id,
                                     Node& cacheVal) const
{
  if (k.getKind() != Kind::SKOLEM)
  {
    return false;
  }
  std::map<Node, std::tuple<SkolemId, TypeNode, Node>>::const_iterator it =
      d_skolemFunMap.find(k);
  Assert(it != d_skolemFunMap.end());
  id = std::get<0>(it->second);
  cacheVal = std::get<2>(it->second);
  return true;
}

SkolemId SkolemManager::getId(TNode k) const
{
  SkolemId id;
  Node cacheVal;
  if (isSkolemFunction(k, id, cacheVal))
  {
    return id;
  }
  return SkolemId::NONE;
}

InternalSkolemId SkolemManager::getInternalId(TNode k) const
{
  SkolemId id;
  Node cacheVal;
  // if its an internal skolem
  if (isSkolemFunction(k, id, cacheVal) && id == SkolemId::INTERNAL)
  {
    Assert(!cacheVal.isNull());
    Node cval = cacheVal.getKind() == Kind::SEXPR ? cacheVal[0] : cacheVal;
    Assert(cval.getKind() == Kind::CONST_INTEGER);
    Rational r = cval.getConst<Rational>();
    Assert(r.sgn() >= 0 && r.getNumerator().fitsUnsignedInt());
    return static_cast<InternalSkolemId>(r.getNumerator().toUnsignedInt());
  }
  return InternalSkolemId::NONE;
}

Node SkolemManager::mkDummySkolem(const std::string& prefix,
                                  const TypeNode& type,
                                  const std::string& comment,
                                  int flags)
{
  return mkSkolemNode(Kind::DUMMY_SKOLEM, prefix, type, flags);
}

bool SkolemManager::isAbstractValue(TNode n) const
{
  return (getInternalId(n) == InternalSkolemId::ABSTRACT_VALUE);
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
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    if (cur.hasAttribute(ofa))
    {
      visit.pop_back();
      continue;
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
        visit.pop_back();
      }
      else
      {
        // visit ucur then visit cur again
        visit.push_back(ucur);
      }
      continue;
    }
    else if (cur.getNumChildren() == 0)
    {
      cur.setAttribute(ofa, cur);
      visit.pop_back();
      continue;
    }
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    visit.pop_back();
    Node ret = cur;
    bool childChanged = false;
    std::vector<Node> children;
    if (cur.getMetaKind() == metakind::PARAMETERIZED)
    {
      const Node& oon = cur.getOperator().getAttribute(ofa);
      Assert(!oon.isNull());
      childChanged = childChanged || cur.getOperator() != oon;
      children.push_back(oon);
    }
    for (const Node& cn : cur)
    {
      const Node& ocn = cn.getAttribute(ofa);
      Assert(!ocn.isNull());
      childChanged = childChanged || cn != ocn;
      children.push_back(ocn);
    }
    if (childChanged)
    {
      ret = nm->mkNode(cur.getKind(), children);
    }
    cur.setAttribute(ofa, ret);

  } while (!visit.empty());
  const Node& on = n.getAttribute(ofa);
  Trace("sk-manager-debug") << "..return " << on << std::endl;
  return on;
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

TypeNode SkolemManager::getTypeFor(SkolemId id,
                                   const std::vector<Node>& cacheVals)
{
  NodeManager* nm = NodeManager::currentNM();
  switch (id)
  {
    // Type(cacheVals[0]), i.e skolems that return same type as first argument
    case SkolemId::PURIFY:
    case SkolemId::TRANSCENDENTAL_PURIFY:
      Assert(cacheVals.size() > 0);
      return cacheVals[0].getType();
      break;
    case SkolemId::GROUND_TERM:
    case SkolemId::ARITH_VTS_INFINITY:
    case SkolemId::ARITH_VTS_INFINITY_FREE:
    {
      Assert(cacheVals[0].getKind() == Kind::SORT_TO_TERM);
      return cacheVals[0].getConst<SortToTerm>().getType();
    }
    // real -> real function
    case SkolemId::DIV_BY_ZERO:
    {
      TypeNode rtype = nm->realType();
      return nm->mkFunctionType(rtype, rtype);
    }
    // real skolems
    case SkolemId::TRANSCENDENTAL_PURIFY_ARG:
    case SkolemId::TRANSCENDENTAL_SINE_PHASE_SHIFT:
    case SkolemId::ARITH_VTS_DELTA:
    case SkolemId::ARITH_VTS_DELTA_FREE: return nm->realType();
    // int -> int function
    case SkolemId::INT_DIV_BY_ZERO:
    case SkolemId::MOD_BY_ZERO:
    case SkolemId::STRINGS_OCCUR_INDEX:
    case SkolemId::STRINGS_OCCUR_INDEX_RE:
    case SkolemId::STRINGS_OCCUR_LEN_RE:
    case SkolemId::STRINGS_STOI_RESULT:
    case SkolemId::STRINGS_ITOS_RESULT:
    case SkolemId::BAGS_MAP_SUM:
    case SkolemId::BAGS_CARD_COMBINE:
    {
      TypeNode itype = nm->integerType();
      return nm->mkFunctionType(itype, itype);
    }
    case SkolemId::BV_EMPTY:
    {
      return nm->mkBitVectorType(0);
    }
    // int -> Type(args[0])
    case SkolemId::STRINGS_REPLACE_ALL_RESULT:
    {
      Assert(cacheVals.size() > 0);
      TypeNode itype = nm->integerType();
      return nm->mkFunctionType(itype, cacheVals[0].getType());
    }
    // integer skolems
    case SkolemId::STRINGS_NUM_OCCUR:
    case SkolemId::STRINGS_NUM_OCCUR_RE:
    case SkolemId::STRINGS_DEQ_DIFF:
    case SkolemId::STRINGS_STOI_NON_DIGIT:
    case SkolemId::BAGS_FOLD_CARD:
    case SkolemId::SETS_FOLD_CARD:
    case SkolemId::BAGS_DISTINCT_ELEMENTS_SIZE:
    case SkolemId::BAGS_MAP_INDEX: return nm->integerType();
    // string skolems
    case SkolemId::RE_FIRST_MATCH_PRE:
    case SkolemId::RE_FIRST_MATCH:
    case SkolemId::RE_FIRST_MATCH_POST:
    case SkolemId::RE_UNFOLD_POS_COMPONENT: return nm->stringType();
    case SkolemId::ARRAY_DEQ_DIFF:
    {
      Assert(cacheVals.size() == 2);
      TypeNode atype = cacheVals[0].getType();
      Assert(atype.isArray());
      return atype.getArrayIndexType();
    }
    case SkolemId::QUANTIFIERS_SKOLEMIZE:
    {
      Assert(cacheVals.size() == 2);
      Assert(cacheVals[0].getKind() == Kind::FORALL);
      Assert(cacheVals[1].getKind() == Kind::CONST_INTEGER);
      const Rational& r = cacheVals[1].getConst<Rational>();
      Assert(r.getNumerator().fitsUnsignedInt());
      size_t i = r.getNumerator().toUnsignedInt();
      Assert(i < cacheVals[0][0].getNumChildren());
      return cacheVals[0][0][i].getType();
    }
    break;
    // skolems that return the set element type
    case SkolemId::BAGS_DEQ_DIFF:
    case SkolemId::SETS_DEQ_DIFF:
    {
      Assert(cacheVals.size() > 0);
      TypeNode stype = cacheVals[0].getType();
      Assert(stype.getNumChildren() == 1);
      return stype[0];
    }
    // skolems that return the set to set element type
    case SkolemId::BAGS_CHOOSE:
    case SkolemId::SETS_CHOOSE:
    {
      Assert(cacheVals.size() > 0);
      TypeNode stype = cacheVals[0].getType();
      Assert(stype.getNumChildren() == 1);
      return nm->mkFunctionType(stype, stype[0]);
    }
    case SkolemId::TABLES_GROUP_PART:
    case SkolemId::RELATIONS_GROUP_PART:
    {
      Assert(cacheVals.size() > 0);
      TypeNode stype = cacheVals[0].getType();
      Assert(stype.getNumChildren() == 1);
      stype = stype[0];
      Assert(stype.getNumChildren() == 1);
      return nm->mkFunctionType(stype[0], stype);
    }
    // skolems that return the set element of set element type
    case SkolemId::TABLES_GROUP_PART_ELEMENT:
    case SkolemId::RELATIONS_GROUP_PART_ELEMENT:
    {
      Assert(cacheVals.size() > 0);
      TypeNode stype = cacheVals[0].getType();
      Assert(stype.getNumChildren() == 1);
      stype = stype[0];
      Assert(stype.getNumChildren() == 1);
      return stype[0];
    }
    case SkolemId::SETS_MAP_DOWN_ELEMENT:
    {
      Assert(cacheVals.size() == 2 && cacheVals[0].getKind() == Kind::SET_MAP);
      TypeNode stype = cacheVals[0][1].getType();
      Assert(stype.isSet());
      return stype.getSetElementType();
    }
    case SkolemId::BAGS_FOLD_UNION_DISJOINT:
    case SkolemId::SETS_FOLD_UNION:
    case SkolemId::BAGS_DISTINCT_ELEMENTS_UNION_DISJOINT:
    {
      Assert(cacheVals.size() > 0);
      TypeNode itype = nm->integerType();
      return nm->mkFunctionType(itype, cacheVals[0].getType());
    }
    case SkolemId::BAGS_DISTINCT_ELEMENTS:
    case SkolemId::BAGS_FOLD_ELEMENTS:
    case SkolemId::SETS_FOLD_ELEMENTS:
    {
      Assert(cacheVals.size() > 0);
      TypeNode itype = nm->integerType();
      TypeNode collectionType = cacheVals[0].getType();
      Assert(collectionType.getNumChildren() == 1);
      TypeNode elementType = collectionType[0];
      return nm->mkFunctionType(itype, elementType);
    }
    case SkolemId::BAGS_FOLD_COMBINE:
    case SkolemId::SETS_FOLD_COMBINE:
    {
      Assert(cacheVals.size() == 3);
      TypeNode itype = nm->integerType();
      return nm->mkFunctionType(itype, cacheVals[1].getType());
    }
    case SkolemId::BAGS_MAP_PREIMAGE_INJECTIVE:
    {
      Assert (cacheVals[0].getType().isFunction());
      return cacheVals[0].getType().getArgTypes()[0];
    }
    case SkolemId::SHARED_SELECTOR:
    {
      Assert(cacheVals.size() == 3);
      Assert(cacheVals[0].getKind() == Kind::SORT_TO_TERM);
      Assert(cacheVals[1].getKind() == Kind::SORT_TO_TERM);
      TypeNode dtt = cacheVals[0].getConst<SortToTerm>().getType();
      TypeNode t = cacheVals[1].getConst<SortToTerm>().getType();
      return nm->mkSelectorType(dtt, t);
    }
    case SkolemId::HO_DEQ_DIFF:
    {
      const Rational& r = cacheVals[2].getConst<Rational>();
      Assert(r.getNumerator().fitsUnsignedInt());
      size_t i = r.getNumerator().toUnsignedInt();
      Assert(cacheVals[0].getType().isFunction());
      std::vector<TypeNode> argTypes = cacheVals[0].getType().getArgTypes();
      Assert(i < argTypes.size());
      return argTypes[i];
    }
    // fp skolems
    case SkolemId::FP_MIN_ZERO:
    case SkolemId::FP_MAX_ZERO:
    {
      Assert(cacheVals.size() == 1);
      Assert(cacheVals[0].getKind() == Kind::SORT_TO_TERM);
      TypeNode type = cacheVals[0].getConst<SortToTerm>().getType();
      Assert(type.isFloatingPoint());
      return nm->mkFunctionType({type, type}, nm->mkBitVectorType(1));
    }
    case SkolemId::FP_TO_SBV:
    case SkolemId::FP_TO_UBV:
    {
      Assert(cacheVals.size() == 2);
      Assert(cacheVals[0].getKind() == Kind::SORT_TO_TERM);
      TypeNode fptype = cacheVals[0].getConst<SortToTerm>().getType();
      Assert(fptype.isFloatingPoint());
      Assert(cacheVals[1].getKind() == Kind::SORT_TO_TERM);
      TypeNode bvtype = cacheVals[1].getConst<SortToTerm>().getType();
      Assert(bvtype.isBitVector());
      return nm->mkFunctionType({nm->roundingModeType(), fptype}, bvtype);
    }
    case SkolemId::FP_TO_REAL:
    {
      Assert(cacheVals.size() == 1);
      Assert(cacheVals[0].getKind() == Kind::SORT_TO_TERM);
      TypeNode type = cacheVals[0].getConst<SortToTerm>().getType();
      Assert(type.isFloatingPoint());
      return nm->mkFunctionType({type}, nm->realType());
    }
    case SkolemId::BV_TO_INT_UF:
    {
      Assert(cacheVals.size() == 1);
      // fetch the original function
      Node bvUF = cacheVals[0];
      Assert(cacheVals[0].getType().isFunction());
      // old and new types of domain and result
      TypeNode tn = bvUF.getType();
      TypeNode bvRange = tn.getRangeType();
      std::vector<TypeNode> bvDomain = tn.getArgTypes();
      std::vector<TypeNode> intDomain;

      // if the original range is a bit-vector sort,
      // the new range should be an integer sort.
      // Otherwise, we keep the original range.
      // Similarly for the domain sorts.
      TypeNode intRange = bvRange.isBitVector() ? nm->integerType() : bvRange;
      for (const TypeNode& d : bvDomain)
      {
        intDomain.push_back(d.isBitVector() ? nm->integerType() : d);
      }
      return nm->mkFunctionType(intDomain, intRange);
    }
    //
    default: break;
  }
  return TypeNode();
}

size_t SkolemManager::getNumIndicesForSkolemId(SkolemId id) const
{
  switch (id)
  {
    // Number of skolem indices: 0
    case SkolemId::BV_EMPTY:
    case SkolemId::DIV_BY_ZERO:
    case SkolemId::INT_DIV_BY_ZERO:
    case SkolemId::MOD_BY_ZERO: return 0;

    // Number of skolem indices: 1
    case SkolemId::PURIFY:
    case SkolemId::GROUND_TERM:
    case SkolemId::TRANSCENDENTAL_PURIFY:
    case SkolemId::TRANSCENDENTAL_PURIFY_ARG:
    case SkolemId::TRANSCENDENTAL_SINE_PHASE_SHIFT:
    case SkolemId::STRINGS_REPLACE_ALL_RESULT:
    case SkolemId::STRINGS_ITOS_RESULT:
    case SkolemId::STRINGS_STOI_RESULT:
    case SkolemId::STRINGS_STOI_NON_DIGIT:
    case SkolemId::BAGS_CARD_COMBINE:
    case SkolemId::BAGS_DISTINCT_ELEMENTS_UNION_DISJOINT:
    case SkolemId::BAGS_FOLD_CARD:
    case SkolemId::BAGS_FOLD_ELEMENTS:
    case SkolemId::BAGS_FOLD_UNION_DISJOINT:
    case SkolemId::BAGS_CHOOSE:
    case SkolemId::BAGS_DISTINCT_ELEMENTS:
    case SkolemId::BAGS_DISTINCT_ELEMENTS_SIZE:
    case SkolemId::TABLES_GROUP_PART:
    case SkolemId::RELATIONS_GROUP_PART:
    case SkolemId::SETS_CHOOSE:
    case SkolemId::SETS_FOLD_CARD:
    case SkolemId::SETS_FOLD_ELEMENTS:
    case SkolemId::SETS_FOLD_UNION:
    case SkolemId::FP_MIN_ZERO:
    case SkolemId::FP_MAX_ZERO:
    case SkolemId::BV_TO_INT_UF:
    case SkolemId::FP_TO_REAL: return 1;

    // Number of skolem indices: 2
    case SkolemId::ARRAY_DEQ_DIFF:
    case SkolemId::QUANTIFIERS_SKOLEMIZE:
    case SkolemId::STRINGS_NUM_OCCUR:
    case SkolemId::STRINGS_OCCUR_INDEX:
    case SkolemId::STRINGS_NUM_OCCUR_RE:
    case SkolemId::STRINGS_OCCUR_INDEX_RE:
    case SkolemId::STRINGS_OCCUR_LEN_RE:
    case SkolemId::STRINGS_DEQ_DIFF:
    case SkolemId::RE_FIRST_MATCH_PRE:
    case SkolemId::RE_FIRST_MATCH:
    case SkolemId::RE_FIRST_MATCH_POST:
    case SkolemId::BAGS_DEQ_DIFF:
    case SkolemId::TABLES_GROUP_PART_ELEMENT:
    case SkolemId::RELATIONS_GROUP_PART_ELEMENT:
    case SkolemId::SETS_DEQ_DIFF:
    case SkolemId::SETS_MAP_DOWN_ELEMENT:
    case SkolemId::FP_TO_SBV:
    case SkolemId::FP_TO_UBV: return 2;

    // Number of skolem indices: 3
    case SkolemId::SHARED_SELECTOR:
    case SkolemId::RE_UNFOLD_POS_COMPONENT:
    case SkolemId::BAGS_FOLD_COMBINE:
    case SkolemId::BAGS_MAP_PREIMAGE_INJECTIVE:
    case SkolemId::BAGS_MAP_SUM:
    case SkolemId::SETS_FOLD_COMBINE: return 3;

    // Number of skolem indices: 5
    case SkolemId::BAGS_MAP_INDEX: return 5;

    default: Unimplemented() << "Unknown skolem kind " << id; break;
  }
}

}  // namespace cvc5::internal
