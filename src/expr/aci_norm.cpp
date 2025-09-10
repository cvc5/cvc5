/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definition of ProofRule::ACI_NORM and ProofRule::ABSORB.
 */

#include "expr/aci_norm.h"

#include "expr/attribute.h"
#include "expr/skolem_manager.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/strings/word.h"
#include "util/bitvector.h"
#include "util/finite_field_value.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

Node getNullTerminator(NodeManager* nm, Kind k, TypeNode tn)
{
  Node nullTerm;
  switch (k)
  {
    case Kind::OR: nullTerm = nm->mkConst(false); break;
    case Kind::AND:
    case Kind::SEP_STAR: nullTerm = nm->mkConst(true); break;
    case Kind::ADD:
      // Note that we ignore the type. This is safe since ADD is permissive
      // for subtypes.
      nullTerm = nm->mkConstInt(Rational(0));
      break;
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
      // Note that we ignore the type. This is safe since multiplication is
      // permissive for subtypes.
      nullTerm = nm->mkConstInt(Rational(1));
      break;
    case Kind::STRING_CONCAT:
      // handles strings and sequences
      if (tn.isStringLike())
      {
        nullTerm = theory::strings::Word::mkEmptyWord(tn);
      }
      break;
    case Kind::REGEXP_CONCAT:
      // the language containing only the empty string
      nullTerm = nm->mkNode(Kind::STRING_TO_REGEXP, nm->mkConst(String("")));
      break;
    case Kind::REGEXP_UNION:
      // empty language
      nullTerm = nm->mkNode(Kind::REGEXP_NONE);
      break;
    case Kind::REGEXP_INTER:
      // universal language
      nullTerm = nm->mkNode(Kind::REGEXP_ALL);
      break;
    case Kind::BITVECTOR_AND:
      // it may be the case that we are an abstract type, which we guard here
      // and return the null node.
      if (tn.isBitVector())
      {
        nullTerm = theory::bv::utils::mkOnes(nm, tn.getBitVectorSize());
      }
      break;
    case Kind::BITVECTOR_OR:
    case Kind::BITVECTOR_ADD:
    case Kind::BITVECTOR_XOR:
      if (tn.isBitVector())
      {
        nullTerm = theory::bv::utils::mkZero(nm, tn.getBitVectorSize());
      }
      break;
    case Kind::BITVECTOR_MULT:
      if (tn.isBitVector())
      {
        nullTerm = theory::bv::utils::mkOne(nm, tn.getBitVectorSize());
      }
      break;
    case Kind::BITVECTOR_CONCAT:
    {
      nullTerm = nm->getSkolemManager()->mkSkolemFunction(SkolemId::BV_EMPTY);
    }
    break;
    case Kind::FINITE_FIELD_ADD:
      if (tn.isFiniteField())
      {
        nullTerm = nm->mkConst(FiniteFieldValue(Integer(0), tn.getFfSize()));
      }
      break;
    case Kind::FINITE_FIELD_MULT:
      if (tn.isFiniteField())
      {
        nullTerm = nm->mkConst(FiniteFieldValue(Integer(1), tn.getFfSize()));
      }
      break;
    default:
      // not handled as null-terminated
      break;
  }
  return nullTerm;
}

bool isAssocCommIdem(Kind k)
{
  switch (k)
  {
    case Kind::OR:
    case Kind::AND:
    case Kind::SEP_STAR:
    case Kind::REGEXP_UNION:
    case Kind::REGEXP_INTER:
    case Kind::BITVECTOR_AND:
    case Kind::BITVECTOR_OR:
    case Kind::FINITE_FIELD_ADD:
    case Kind::FINITE_FIELD_MULT: return true;
    default: break;
  }
  return false;
}

bool isAssocComm(Kind k)
{
  return (k==Kind::BITVECTOR_XOR);
}

bool isAssoc(Kind k)
{
  switch (k)
  {
    case Kind::BITVECTOR_CONCAT:
    case Kind::STRING_CONCAT:
    case Kind::REGEXP_CONCAT: return true;
    default: break;
  }
  // also return true for the operators listed above
  return isAssocCommIdem(k);
}

struct NormalFormTag
{
};
using NormalFormAttr = expr::Attribute<NormalFormTag, Node>;

Node getACINormalForm(Node a)
{
  NormalFormAttr nfa;
  Node an = a.getAttribute(nfa);
  if (!an.isNull())
  {
    // already computed
    return an;
  }
  Kind k = a.getKind();
  bool aci = isAssocCommIdem(k);
  bool ac = isAssocComm(k) || aci;
  if (!ac && !isAssoc(k))
  {
    // not associative, return self
    a.setAttribute(nfa, a);
    return a;
  }
  TypeNode atn = a.getType();
  Node nt = getNullTerminator(a.getNodeManager(), k, atn);
  if (nt.isNull())
  {
    // no null terminator, likely abstract type, return self
    a.setAttribute(nfa, a);
    return a;
  }
  std::vector<Node> toProcess;
  toProcess.insert(toProcess.end(), a.rbegin(), a.rend());
  std::vector<Node> children;
  Node cur;
  do
  {
    cur = toProcess.back();
    toProcess.pop_back();
    if (cur == nt)
    {
      // ignore null terminator (which is the neutral element)
      continue;
    }
    else if (cur.getKind() == k)
    {
      // flatten
      toProcess.insert(toProcess.end(), cur.rbegin(), cur.rend());
    }
    else if (!aci
             || std::find(children.begin(), children.end(), cur)
                    == children.end())
    {
      // add to final children if not idempotent or if not a duplicate
      children.push_back(cur);
    }
  } while (!toProcess.empty());
  if (ac)
  {
    // sort if commutative
    std::sort(children.begin(), children.end());
  }
  an = children.empty()
           ? nt
           : (children.size() == 1 ? children[0]
                                   : a.getNodeManager()->mkNode(k, children));
  a.setAttribute(nfa, an);
  return an;
}

bool isACINorm(Node a, Node b)
{
  Node an = getACINormalForm(a);
  Node bn = getACINormalForm(b);
  if (a.getKind() == b.getKind())
  {
    // if the kinds are equal, we compare their normal forms only, as the checks
    // below are spurious.
    return (an == bn);
  }
  // note we compare three possibilities, to handle cases like
  //   (or (and A B) false) == (and A B).
  //
  // Note that we do *not* succeed if an==bn here, since this depends on the
  // chosen ordering. For example, if (or (and A B) false) == (and B A),
  // we get a normal form of (and A B) for the LHS. The normal form of the
  // RHS is either (and A B) or (and B A). If we succeeded when an==bn,
  // then this would only be the case if the former was chosen as a normal
  // form. Instead, both fail.
  return (a == bn) || (an == b);
}

Node getZeroElement(NodeManager* nm, Kind k, TypeNode tn)
{
  Node zeroTerm;
  switch (k)
  {
    case Kind::OR: zeroTerm = nm->mkConst(true); break;
    case Kind::AND:
    case Kind::SEP_STAR: zeroTerm = nm->mkConst(false); break;
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
      // Note that we ignore the type. This is safe since multiplication is
      // permissive for subtypes.
      zeroTerm = nm->mkConstInt(Rational(0));
      break;
    case Kind::REGEXP_UNION:
      // universal language
      zeroTerm = nm->mkNode(Kind::REGEXP_ALL);
      break;
    case Kind::REGEXP_INTER:
    case Kind::REGEXP_CONCAT:
      // empty language
      zeroTerm = nm->mkNode(Kind::REGEXP_NONE);
      break;
    case Kind::BITVECTOR_OR:
      if (tn.isBitVector())
      {
        zeroTerm = theory::bv::utils::mkOnes(nm, tn.getBitVectorSize());
      }
      break;
    case Kind::BITVECTOR_AND:
    case Kind::BITVECTOR_MULT:
      // it may be the case that we are an abstract type, which we guard here
      // and return the null node.
      if (tn.isBitVector())
      {
        zeroTerm = theory::bv::utils::mkZero(nm, tn.getBitVectorSize());
      }
      break;
    default:
      // no zero
      break;
  }
  return zeroTerm;
}

struct AbsorbTag
{
};
struct AbsorbComputedTag
{
};
/**
 * Attribute true for terms that can be absorbd. Note the same attribute
 * is stored for all kinds.
 */
typedef expr::Attribute<AbsorbTag, bool> AbsorbAttr;
typedef expr::Attribute<AbsorbComputedTag, bool> AbsorbComputedAttr;

bool isAbsorb(Kind k)
{
  switch (k)
  {
    case Kind::OR:
    case Kind::AND:
    case Kind::REGEXP_UNION:
    case Kind::REGEXP_INTER:
    case Kind::REGEXP_CONCAT:
    case Kind::BITVECTOR_AND:
    case Kind::BITVECTOR_OR: return true;
    default: break;
  }
  return false;
}

bool isAbsorb(Node a, const Node& zero)
{
  Kind k = a.getKind();
  if (!isAbsorb(k))
  {
    return false;
  }
  AbsorbAttr aa;
  AbsorbComputedAttr aca;
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(a);
  do
  {
    cur = visit.back();
    Assert(cur.getKind() == k);
    if (cur.getAttribute(aca))
    {
      visit.pop_back();
      continue;
    }
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited.insert(cur);
      for (const Node& cc : cur)
      {
        if (cc.getKind() == k)
        {
          visit.push_back(cc);
        }
      }
      continue;
    }
    visit.pop_back();
    bool isAnnil = false;
    for (const Node& cc : cur)
    {
      // only absorbs if the child is zero or has the same kind and
      // absorbs
      if (cc == zero || (cc.getKind() == k && cc.getAttribute(aa)))
      {
        isAnnil = true;
        break;
      }
    }
    cur.setAttribute(aa, isAnnil);
    cur.setAttribute(aca, true);
  } while (!visit.empty());
  return a.getAttribute(aa);
}

}  // namespace expr
}  // namespace cvc5::internal
