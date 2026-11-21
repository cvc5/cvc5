/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The SetsToBags preprocessing pass.
 *
 * Converts set terms into bag terms.
 */

#include "preprocessing/passes/sets_to_bags.h"

#include <sstream>
#include <unordered_set>

#include "expr/beta_reduce_converter.h"
#include "expr/dtype.h"
#include "expr/emptybag.h"
#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/logic_exception.h"
#include "theory/trust_substitutions.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

namespace {

/** Returns true if tn has a set type as a component or as a datatype field */
bool hasSetComponent(TypeNode tn)
{
  std::unordered_set<TypeNode> visited;
  std::vector<TypeNode> visit{tn};
  do
  {
    TypeNode cur = visit.back();
    visit.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    if (cur.isSet())
    {
      return true;
    }
    if (cur.isDatatype())
    {
      for (const TypeNode& stn : cur.getDType().getSubfieldTypes())
      {
        visit.push_back(stn);
      }
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
  } while (!visit.empty());
  return false;
}

}  // namespace

SetsToBagsConverter::SetsToBagsConverter(Env& env, options::SetsToBagsMode mode)
    : EnvObj(env), NodeConverter(nodeManager()), d_mode(mode)
{
}

const std::map<TypeNode, Node>& SetsToBagsConverter::getUniverses() const
{
  return d_universes;
}

TypeNode SetsToBagsConverter::preConvertType(TypeNode tn)
{
  if (tn.isDatatype() && hasSetComponent(tn))
  {
    std::stringstream ss;
    ss << "Cannot convert the datatype " << tn
       << " to bags since it has fields of set type. Remove option --"
       << options::sets::longName::setsToBags << ".";
    throw LogicException(ss.str());
  }
  return tn;
}

TypeNode SetsToBagsConverter::postConvertType(TypeNode tn)
{
  if (tn.isSet())
  {
    return nodeManager()->mkBagType(tn.getSetElementType());
  }
  return tn;
}

Node SetsToBagsConverter::postConvertUntyped(Node orig,
                                             const std::vector<Node>& terms,
                                             bool termsChanged)
{
  NodeManager* nm = nodeManager();
  TypeNode tn = orig.getType();
  TypeNode ctn = convertType(tn);
  Kind k = orig.getKind();
  Node ret;
  if (theory::kindToTheoryId(k) == theory::THEORY_SETS)
  {
    ret = convertSetOperator(orig, terms);
  }
  else if (orig.isVar())
  {
    if (ctn == tn)
    {
      return orig;
    }
    // the converted variable has the same name as the original one
    if (k == Kind::BOUND_VARIABLE)
    {
      ret = orig.hasName() ? NodeManager::mkBoundVar(orig.getName(), ctn)
                           : NodeManager::mkBoundVar(ctn);
    }
    else
    {
      SkolemManager* sm = nm->getSkolemManager();
      ret = orig.hasName()
                ? sm->mkDummySkolem(
                      orig.getName(), ctn, SkolemFlags::SKOLEM_EXACT_NAME)
                : sm->mkDummySkolem("sets_to_bags", ctn);
    }
  }
  else if (k == Kind::BOUND_VAR_LIST)
  {
    // the variables of a binder are not wrapped in bag.setof
    std::vector<Node> vars;
    for (const Node& v : terms)
    {
      vars.push_back(v.getKind() == Kind::BAG_SETOF ? v[0] : v);
    }
    ret = nm->mkNode(k, vars);
  }
  else if (termsChanged)
  {
    ret = nm->mkNode(k, terms);
  }
  else
  {
    ret = orig;
  }
  if (tn.isSet())
  {
    ret = mkSetof(ret);
  }
  if (ret.getType() != ctn)
  {
    std::stringstream ss;
    ss << "Cannot convert " << orig << " to bags. Remove option --"
       << options::sets::longName::setsToBags << ".";
    throw LogicException(ss.str());
  }
  return ret;
}

Node SetsToBagsConverter::convertSetOperator(Node orig,
                                             const std::vector<Node>& terms)
{
  NodeManager* nm = nodeManager();
  Kind k = orig.getKind();
  switch (k)
  {
    case Kind::SET_EMPTY:
      return nm->mkConst(EmptyBag(convertType(orig.getType())));
    case Kind::SET_UNIVERSE:
      checkSetsExp();
      return getUniverse(convertType(orig.getType()));
    case Kind::SET_SINGLETON:
      return nm->mkNode(Kind::BAG_MAKE, terms[0], nm->mkConstInt(Rational(1)));
    case Kind::SET_INSERT:
    {
      // (set.insert x_1 ... x_n A) is the union of A and {x_1}, ..., {x_n}
      Node one = nm->mkConstInt(Rational(1));
      Node ret = terms.back();
      for (size_t i = terms.size() - 1; i > 0; i--)
      {
        ret = mkUnion(nm->mkNode(Kind::BAG_MAKE, terms[i - 1], one), ret);
      }
      return ret;
    }
    case Kind::SET_UNION: return mkUnion(terms[0], terms[1]);
    case Kind::SET_INTER: return nm->mkNode(Kind::BAG_INTER_MIN, terms);
    case Kind::SET_MINUS:
      return nm->mkNode(Kind::BAG_DIFFERENCE_SUBTRACT, terms);
    case Kind::SET_SUBSET: return nm->mkNode(Kind::BAG_SUBBAG, terms);
    case Kind::SET_MEMBER: return nm->mkNode(Kind::BAG_MEMBER, terms);
    case Kind::SET_CARD: return nm->mkNode(Kind::BAG_CARD, terms);
    case Kind::SET_COMPLEMENT:
    {
      checkSetsExp();
      Node universe = mkSetof(getUniverse(terms[0].getType()));
      return nm->mkNode(Kind::BAG_DIFFERENCE_SUBTRACT, universe, terms[0]);
    }
    case Kind::SET_IS_EMPTY:
      return terms[0].eqNode(nm->mkConst(EmptyBag(terms[0].getType())));
    case Kind::SET_IS_SINGLETON:
    {
      Node choose = nm->mkNode(Kind::BAG_CHOOSE, terms[0]);
      Node one = nm->mkConstInt(Rational(1));
      return terms[0].eqNode(nm->mkNode(Kind::BAG_MAKE, choose, one));
    }
    case Kind::SET_CHOOSE: return nm->mkNode(Kind::BAG_CHOOSE, terms);
    case Kind::SET_MAP: return nm->mkNode(Kind::BAG_MAP, terms);
    case Kind::SET_FILTER: return nm->mkNode(Kind::BAG_FILTER, terms);
    case Kind::SET_ALL: return nm->mkNode(Kind::BAG_ALL, terms);
    case Kind::SET_SOME: return nm->mkNode(Kind::BAG_SOME, terms);
    case Kind::SET_FOLD: return nm->mkNode(Kind::BAG_FOLD, terms);
    default: break;
  }
  std::stringstream ss;
  ss << "Cannot convert the set operator " << k
     << " to a bag operator. Remove option --"
     << options::sets::longName::setsToBags << ".";
  throw LogicException(ss.str());
}

Node SetsToBagsConverter::getUniverse(TypeNode bagType)
{
  std::map<TypeNode, Node>::iterator it = d_universes.find(bagType);
  if (it != d_universes.end())
  {
    return it->second;
  }
  Node universe = nodeManager()->getSkolemManager()->mkDummySkolem(
      "bag.universe", bagType, SkolemFlags::SKOLEM_EXACT_NAME);
  d_universes[bagType] = universe;
  return universe;
}

Node SetsToBagsConverter::mkSetof(Node b)
{
  if (d_mode != options::SetsToBagsMode::SETOF)
  {
    return b;
  }
  Kind k = b.getKind();
  if (k == Kind::BAG_SETOF || k == Kind::BAG_EMPTY
      || (k == Kind::BAG_MAKE && b[1].isConst()
          && b[1].getConst<Rational>().isOne()))
  {
    return b;
  }
  return nodeManager()->mkNode(Kind::BAG_SETOF, b);
}

Node SetsToBagsConverter::mkUnion(Node a, Node b)
{
  NodeManager* nm = nodeManager();
  return nm->mkNode(Kind::BAG_SETOF, nm->mkNode(Kind::BAG_UNION_MAX, a, b));
}

void SetsToBagsConverter::checkSetsExp() const
{
  if (!options().sets.setsExp)
  {
    std::stringstream ss;
    ss << "Extended set operators are not supported in default mode, try "
          "--sets-exp.";
    throw LogicException(ss.str());
  }
}

SetsToBags::SetsToBags(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sets-to-bags"),
      d_converter(preprocContext->getEnv(), options().sets.setsToBags),
      d_modelUnsound(false)
{
}

PreprocessingPassResult SetsToBags::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // This pass runs before the input is rewritten, since the rewriter
  // eliminates set operators. Hence, we apply the top-level substitutions,
  // which include the definitions of defined functions, without rewriting.
  theory::SubstitutionMap& sm =
      d_preprocContext->getTopLevelSubstitutions().get();
  BetaReduceNodeConverter brc(nodeManager());
  // convert all assertions first, since they determine the universe bags
  std::vector<Node> converted;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node a = brc.convert(sm.apply((*assertionsToPreprocess)[i]));
    converted.push_back(d_converter.convert(a, false));
  }
  if (options().sets.setsToBags == options::SetsToBagsMode::SETOF
      && !d_converter.getUniverses().empty())
  {
    // The universe set contains all elements, whereas the universe bag is only
    // required to contain the other bags.
    d_modelUnsound = true;
  }
  NodeManager* nm = nodeManager();
  for (size_t i = 0, size = converted.size(); i < size; ++i)
  {
    Node a = (*assertionsToPreprocess)[i];
    std::vector<Node> conj{converted[i]};
    addUniverseConstraints(converted[i], conj);
    Node ac = nm->mkAnd(conj);
    if (ac == a)
    {
      continue;
    }
    Trace("sets-to-bags") << "Converted " << a << " to " << ac << std::endl;
    assertionsToPreprocess->replace(
        i, ac, nullptr, TrustId::PREPROCESS_SETS_TO_BAGS);
  }
  if (d_modelUnsound)
  {
    assertionsToPreprocess->markModelUnsound();
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

void SetsToBags::addUniverseConstraints(Node n, std::vector<Node>& conj) const
{
  const std::map<TypeNode, Node>& universes = d_converter.getUniverses();
  if (universes.empty())
  {
    return;
  }
  NodeManager* nm = nodeManager();
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit{n};
  do
  {
    TNode cur = visit.back();
    visit.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    // we do not traverse below binders, so that all terms we visit are ground
    if (!cur.isClosure())
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    std::map<TypeNode, Node>::const_iterator it = universes.find(cur.getType());
    if (it == universes.end())
    {
      continue;
    }
    Node universe = it->second;
    Kind k = cur.getKind();
    if (cur == universe || k == Kind::BAG_EMPTY
        || (k == Kind::BAG_SETOF && cur[0] == universe))
    {
      continue;
    }
    conj.push_back(nm->mkNode(Kind::BAG_SUBBAG, cur, universe));
  } while (!visit.empty());
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
