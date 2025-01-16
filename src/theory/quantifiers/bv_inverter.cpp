/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inverse rules for bit-vector operators.
 */

#include "theory/quantifiers/bv_inverter.h"

#include <algorithm>

#include "expr/bound_var_manager.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "proof/proof_rule_checker.h"
#include "proof/valid_witness_proof_generator.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/quantifiers/bv_inverter_utils.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

BvInverter::BvInverter(const Options& opts, NodeManager* nm, Rewriter* r)
    : d_opts(opts), d_nm(nm), d_rewriter(r)
{
}

/*---------------------------------------------------------------------------*/

Node BvInverter::getSolveVariable(TypeNode tn)
{
  std::map<TypeNode, Node>::iterator its = d_solve_var.find(tn);
  if (its == d_solve_var.end())
  {
    Node k = NodeManager::mkDummySkolem("slv", tn);
    d_solve_var[tn] = k;
    return k;
  }
  return its->second;
}

/*---------------------------------------------------------------------------*/

Node BvInverter::mkWitness(const Node& annot) const
{
  // use the valid witness proof generator utility to construct the proper
  // witness term based on the annotation
  Node w = ValidWitnessProofGenerator::mkWitness(
      d_nm, ProofRule::MACRO_EXISTS_INV_CONDITION, {annot});
  Trace("bv-invert-witness")
      << "...returned " << w << " for " << annot << std::endl;
  if (!w.isNull())
  {
    if (d_rewriter != nullptr)
    {
      Node neww = d_rewriter->rewrite(w);
      if (neww != w)
      {
        Trace("bv-invert-witness")
            << "Witness " << w << " was rewritten to " << neww << std::endl;
      }
      w = neww;
    }
  }
  return w;
}

/*---------------------------------------------------------------------------*/

static bool isInvertible(Kind k, unsigned index)
{
  return k == Kind::NOT || k == Kind::EQUAL || k == Kind::BITVECTOR_ULT
         || k == Kind::BITVECTOR_SLT || k == Kind::BITVECTOR_COMP
         || k == Kind::BITVECTOR_NOT || k == Kind::BITVECTOR_NEG
         || k == Kind::BITVECTOR_CONCAT || k == Kind::BITVECTOR_SIGN_EXTEND
         || k == Kind::BITVECTOR_ADD || k == Kind::BITVECTOR_MULT
         || k == Kind::BITVECTOR_UREM || k == Kind::BITVECTOR_UDIV
         || k == Kind::BITVECTOR_AND || k == Kind::BITVECTOR_OR
         || k == Kind::BITVECTOR_XOR || k == Kind::BITVECTOR_LSHR
         || k == Kind::BITVECTOR_ASHR || k == Kind::BITVECTOR_SHL;
}

Node BvInverter::getPathToPv(Node lit,
                             Node pv,
                             Node sv,
                             std::vector<unsigned>& path,
                             std::unordered_set<TNode>& visited)
{
  if (visited.find(lit) == visited.end())
  {
    visited.insert(lit);
    if (lit == pv)
    {
      return sv;
    }
    else
    {
      unsigned rmod = 0;  // TODO : randomize?
      for (size_t i = 0, num = lit.getNumChildren(); i < num; i++)
      {
        size_t ii = (i + rmod) % lit.getNumChildren();
        // only recurse if the kind is invertible
        // this allows us to avoid paths that go through skolem functions
        if (!isInvertible(lit.getKind(), ii))
        {
          continue;
        }
        Node litc = getPathToPv(lit[ii], pv, sv, path, visited);
        if (!litc.isNull())
        {
          // path is outermost term index last
          path.push_back(ii);
          std::vector<Node> children;
          if (lit.getMetaKind() == kind::metakind::PARAMETERIZED)
          {
            children.push_back(lit.getOperator());
          }
          for (size_t j = 0, num2 = lit.getNumChildren(); j < num2; j++)
          {
            children.push_back(j == ii ? litc : lit[j]);
          }
          return NodeManager::currentNM()->mkNode(lit.getKind(), children);
        }
      }
    }
  }
  return Node::null();
}

Node BvInverter::getPathToPv(Node lit,
                             Node pv,
                             Node sv,
                             Node pvs,
                             std::vector<unsigned>& path,
                             bool projectNl)
{
  std::unordered_set<TNode> visited;
  Node slit = getPathToPv(lit, pv, sv, path, visited);
  // if we are able to find a (invertible) path to pv
  if (!slit.isNull() && !pvs.isNull())
  {
    // substitute pvs for the other occurrences of pv
    TNode tpv = pv;
    TNode tpvs = pvs;
    Node prev_lit = slit;
    slit = slit.substitute(tpv, tpvs);
    if (!projectNl && slit != prev_lit)
    {
      // found another occurrence of pv that was not on the solve path,
      // hence lit is non-linear wrt pv and we return null.
      return Node::null();
    }
  }
  return slit;
}

/*---------------------------------------------------------------------------*/

/* Drop child at given index from expression.
 * E.g., dropChild((x + y + z), 1) -> (x + z)  */
static Node dropChild(Node n, unsigned index)
{
  unsigned nchildren = n.getNumChildren();
  Assert(nchildren > 0);
  Assert(index < nchildren);

  if (nchildren < 2) return Node::null();

  Kind k = n.getKind();
  NodeBuilder nb(n.getNodeManager(), k);
  for (unsigned i = 0; i < nchildren; ++i)
  {
    if (i == index) continue;
    nb << n[i];
  }
  Assert(nb.getNumChildren() > 0);
  return nb.getNumChildren() == 1 ? nb[0] : nb.constructNode();
}

Node BvInverter::solveBvLit(Node sv,
                            Node lit,
                            std::vector<unsigned>& path,
                            BvInverterQuery* m)
{
  Assert(!path.empty());

  bool pol = true;
  unsigned index;
  Kind k, litk;

  Assert(!path.empty());
  index = path.back();
  Assert(index < lit.getNumChildren());
  path.pop_back();
  litk = k = lit.getKind();

  /* Note: option --bool-to-bv is currently disabled when CBQI BV
   *       is enabled and the logic is quantified.
   *       We currently do not support Boolean operators
   *       that are interpreted as bit-vector operators of width 1.  */

  /* Boolean layer ----------------------------------------------- */

  if (k == Kind::NOT)
  {
    pol = !pol;
    lit = lit[index];
    Assert(!path.empty());
    index = path.back();
    Assert(index < lit.getNumChildren());
    path.pop_back();
    litk = k = lit.getKind();
  }

  Assert(k == Kind::EQUAL || k == Kind::BITVECTOR_ULT
         || k == Kind::BITVECTOR_SLT);

  Node sv_t = lit[index];
  Node t = lit[1 - index];
  if (litk == Kind::BITVECTOR_ULT && index == 1)
  {
    litk = Kind::BITVECTOR_UGT;
  }
  else if (litk == Kind::BITVECTOR_SLT && index == 1)
  {
    litk = Kind::BITVECTOR_SGT;
  }

  /* Bit-vector layer -------------------------------------------- */

  while (!path.empty())
  {
    unsigned nchildren = sv_t.getNumChildren();
    Assert(nchildren > 0);
    index = path.back();
    Assert(index < nchildren);
    path.pop_back();
    k = sv_t.getKind();

    /* Note: All n-ary kinds except for CONCAT (i.e., BITVECTOR_AND,
     *       BITVECTOR_OR, MULT, ADD) are commutative (no case split
     *       based on index). */
    Node s = dropChild(sv_t, index);
    // Try to directly solve for sv_t[index] in (sv_t = t). If so,
    // set tnext such that this equality is equivalent to
    // (sv_t[index] = tnext).
    Node tnext;
    if (litk == Kind::EQUAL
        && (k == Kind::BITVECTOR_NOT || k == Kind::BITVECTOR_NEG))
    {
      tnext = NodeManager::mkNode(k, t);
    }
    else if (litk == Kind::EQUAL && k == Kind::BITVECTOR_ADD)
    {
      tnext = NodeManager::mkNode(Kind::BITVECTOR_SUB, t, s);
    }
    else if (litk == Kind::EQUAL && k == Kind::BITVECTOR_XOR)
    {
      tnext = NodeManager::mkNode(Kind::BITVECTOR_XOR, t, s);
    }
    else if (litk == Kind::EQUAL && k == Kind::BITVECTOR_MULT && s.isConst()
             && bv::utils::getBit(s, 0))
    {
      unsigned w = bv::utils::getSize(s);
      Integer s_val = s.getConst<BitVector>().toInteger();
      Integer mod_val = Integer(1).multiplyByPow2(w);
      Trace("bv-invert-debug")
          << "Compute inverse : " << s_val << " " << mod_val << std::endl;
      Integer inv_val = s_val.modInverse(mod_val);
      Trace("bv-invert-debug") << "Inverse : " << inv_val << std::endl;
      Node inv = bv::utils::mkConst(w, inv_val);
      tnext = NodeManager::mkNode(Kind::BITVECTOR_MULT, inv, t);
    }
    else if (k == Kind::BITVECTOR_CONCAT)
    {
      if (litk == Kind::EQUAL && d_opts.quantifiers.cegqiBvConcInv)
      {
        /* Compute inverse for s1 o x, x o s2, s1 o x o s2
         * (while disregarding that invertibility depends on si)
         * rather than an invertibility condition (the proper handling).
         * This improves performance on a considerable number of benchmarks.
         *
         * x = t[upper:lower]
         * where
         * upper = getSize(t) - 1 - sum(getSize(sv_t[i])) for i < index
         * lower = getSize(sv_t[i]) for i > index  */
        unsigned upper, lower;
        upper = bv::utils::getSize(t) - 1;
        lower = 0;
        NodeBuilder nb(NodeManager::currentNM(), Kind::BITVECTOR_CONCAT);
        for (unsigned i = 0; i < nchildren; i++)
        {
          if (i < index)
          {
            upper -= bv::utils::getSize(sv_t[i]);
          }
          else if (i > index)
          {
            lower += bv::utils::getSize(sv_t[i]);
          }
        }
        tnext = bv::utils::mkExtract(t, upper, lower);
      }
    }
    // If we didn't solve for t directly, we use a witness term.
    if (tnext.isNull())
    {
      /* t = fresh skolem constant */
      Node annot = mkAnnotation(d_nm, litk, pol, t, sv_t, index);
      tnext = mkWitness(annot);
      /* We generate a witness term (witness x0. ic => x0 <k> s <litk> t) for
       * x <k> s <litk> t. When traversing down, this witness term determines
       * the value for x <k> s = (witness x0. ic => x0 <k> s <litk> t), i.e.,
       * from here on, the propagated literal is a positive equality. */
      litk = Kind::EQUAL;
      pol = true;
      if (tnext.isNull())
      {
        return tnext;
      }
    }
    t = tnext;

    sv_t = sv_t[index];
  }

  /* Base case  */
  Assert(sv_t == sv);
  if (litk == Kind::BITVECTOR_ULT || litk == Kind::BITVECTOR_UGT
      || litk == Kind::BITVECTOR_SLT || litk == Kind::BITVECTOR_SGT
      || pol == false)
  {
    Node annot = mkAnnotationBase(d_nm, litk, pol, t);
    return mkWitness(annot);
  }
  return t;
}

Node BvInverter::mkInvertibilityCondition(const Node& x, const Node& exists)
{
  Trace("mk-inv-cond") << "Make invertibility condition for " << x << " "
                       << exists << std::endl;
  Assert(exists.getKind() == Kind::EXISTS);
  Assert(exists[0].getNumChildren() == 1);
  Node v = exists[0][0];
  Assert(x.getType() == v.getType());
  Node body = exists[1];
  bool pol = body.getKind() != Kind::NOT;
  body = pol ? body : body[0];
  Assert(body.getNumChildren() == 2);
  Kind litk = body.getKind();
  Node t = body[1];
  bool isBase = (body[0] == v);
  Node ic;
  if (isBase)
  {
    if (litk == Kind::BITVECTOR_ULT || litk == Kind::BITVECTOR_UGT)
    {
      ic = utils::getICBvUltUgt(pol, litk, x, t);
    }
    else if (litk == Kind::BITVECTOR_SLT || litk == Kind::BITVECTOR_SGT)
    {
      ic = utils::getICBvSltSgt(pol, litk, x, t);
    }
    else if (pol == false)
    {
      Assert(litk == Kind::EQUAL);
      ic = NodeManager::mkNode(Kind::DISTINCT, x, t);
    }
  }
  else
  {
    Kind k = body[0].getKind();
    Node sv_t = body[0];
    unsigned index = 0;
    bool success = false;
    for (size_t i = 0, nchild = body[0].getNumChildren(); i < nchild; i++)
    {
      if (body[0][i] == v)
      {
        index = i;
        success = true;
        break;
      }
    }
    if (!success)
    {
      Trace("mk-inv-cond") << "...failed to find child" << std::endl;
      return Node::null();
    }
    /* Note: All n-ary kinds except for CONCAT (i.e., BITVECTOR_AND,
     *       BITVECTOR_OR, MULT, ADD) are commutative (no case split
     *       based on index). */
    Node s = dropChild(sv_t, index);
    if (k == Kind::BITVECTOR_MULT)
    {
      ic = utils::getICBvMult(pol, litk, k, index, x, s, t);
    }
    else if (k == Kind::BITVECTOR_SHL)
    {
      ic = utils::getICBvShl(pol, litk, k, index, x, s, t);
    }
    else if (k == Kind::BITVECTOR_UREM)
    {
      ic = utils::getICBvUrem(pol, litk, k, index, x, s, t);
    }
    else if (k == Kind::BITVECTOR_UDIV)
    {
      ic = utils::getICBvUdiv(pol, litk, k, index, x, s, t);
    }
    else if (k == Kind::BITVECTOR_AND || k == Kind::BITVECTOR_OR)
    {
      ic = utils::getICBvAndOr(pol, litk, k, index, x, s, t);
    }
    else if (k == Kind::BITVECTOR_LSHR)
    {
      ic = utils::getICBvLshr(pol, litk, k, index, x, s, t);
    }
    else if (k == Kind::BITVECTOR_ASHR)
    {
      ic = utils::getICBvAshr(pol, litk, k, index, x, s, t);
    }
    else if (k == Kind::BITVECTOR_CONCAT)
    {
      ic = utils::getICBvConcat(pol, litk, index, x, sv_t, t);
    }
    else if (k == Kind::BITVECTOR_SIGN_EXTEND)
    {
      ic = utils::getICBvSext(pol, litk, index, x, sv_t, t);
    }
    else if (litk == Kind::BITVECTOR_ULT || litk == Kind::BITVECTOR_UGT)
    {
      ic = utils::getICBvUltUgt(pol, litk, x, t);
    }
    else if (litk == Kind::BITVECTOR_SLT || litk == Kind::BITVECTOR_SGT)
    {
      ic = utils::getICBvSltSgt(pol, litk, x, t);
    }
    else if (pol == false)
    {
      Assert(litk == Kind::EQUAL);
      ic = NodeManager::mkNode(Kind::DISTINCT, x, t);
    }
  }
  Trace("mk-inv-cond") << "...returns " << ic << std::endl;
  return ic;
}

Node BvInverter::mkAnnotationBase(NodeManager* nm, Kind litk, bool pol, Node t)
{
  Node svt;
  return mkAnnotation(nm, litk, pol, t, svt, 0);
}

Node mkDummyOperator(const Node& op)
{
  return SkolemManager::mkPurifySkolem(op);
}

Node getDummyOperator(const Node& op)
{
  Assert(op.getSkolemId() == SkolemId::PURIFY);
  std::vector<Node> indices = op.getSkolemIndices();
  Assert(indices.size() == 1);
  return indices[0];
}

Node BvInverter::mkAnnotation(
    NodeManager* nm, Kind litk, bool pol, Node t, Node svt, unsigned index)
{
  std::vector<Node> sargs;
  sargs.push_back(ProofRuleChecker::mkKindNode(nm, litk));
  sargs.push_back(nm->mkConst(pol));
  sargs.push_back(t);
  if (!svt.isNull())
  {
    std::vector<Node> ss;
    // Must store a dummy operator for the operator, since otherwise the
    // SEXPR would become an application of that operator.
    ss.push_back(mkDummyOperator(svt.getOperator()));
    ss.insert(ss.end(), svt.begin(), svt.end());
    Node s = nm->mkNode(Kind::SEXPR, ss);
    Assert(s.getKind() == Kind::SEXPR);
    sargs.push_back(s);
    sargs.push_back(nm->mkConstInt(Rational(index)));
  }
  Node annot = nm->mkNode(Kind::SEXPR, sargs);
  Trace("bv-invert") << "Annotation: " << annot << std::endl;
  return annot;
}

/**
 * Mapping to the variable used for binding the existential below.
 */
struct BviAnnotToVarAttributeId
{
};
using BviAnnotToVarAttribute = expr::Attribute<BviAnnotToVarAttributeId, Node>;

Node BvInverter::mkExistsForAnnotation(NodeManager* nm, const Node& n)
{
  // this method unpacks the information constructed by mkAnnotation or
  // mkAnnotationBase and returns an existential of the form expected for
  // mkInvertibilityCondition
  if (n.getKind() != Kind::SEXPR || n.getNumChildren() < 3)
  {
    return Node::null();
  }
  Kind litk;
  if (!ProofRuleChecker::getKind(n[0], litk))
  {
    return Node::null();
  }
  if (n[1].getKind() != Kind::CONST_BOOLEAN)
  {
    return Node::null();
  }
  bool pol = n[1].getConst<bool>();
  Node t = n[2];
  Node s;
  Node v;
  BoundVarManager* bvm = nm->getBoundVarManager();
  if (n.getNumChildren() == 3)
  {
    v = bvm->mkBoundVar<BviAnnotToVarAttribute>(
        n, "@var.inv_cond", t.getType());
    s = v;
  }
  else if (n.getNumChildren() == 5)
  {
    uint32_t index;
    if (!ProofRuleChecker::getUInt32(n[4], index))
    {
      return Node::null();
    }
    std::vector<Node> sargs;
    Node op;
    if (n[3].getKind() == Kind::SEXPR && n[3].getNumChildren() >= 1)
    {
      sargs.insert(sargs.end(), n[3].begin() + 1, n[3].end());
      op = getDummyOperator(n[3][0]);
    }
    if (index >= sargs.size())
    {
      return Node::null();
    }
    v = bvm->mkBoundVar<BviAnnotToVarAttribute>(
        n, "@var.inv_cond", sargs[index].getType());
    sargs[index] = v;
    s = nm->mkNode(op, sargs);
  }
  if (s.isNull())
  {
    return Node::null();
  }
  Node body = nm->mkNode(litk, s, t);
  if (!pol)
  {
    body = body.notNode();
  }
  return nm->mkNode(Kind::EXISTS, nm->mkNode(Kind::BOUND_VAR_LIST, v), body);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
