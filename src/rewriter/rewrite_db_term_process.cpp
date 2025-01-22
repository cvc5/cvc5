/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database term processor
 */

#include "rewriter/rewrite_db_term_process.h"

#include "expr/aci_norm.h"
#include "expr/attribute.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "proof/conv_proof_generator.h"
#include "theory/builtin/generic_op.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/uf/function_const.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "util/bitvector.h"
#include "util/rational.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

RewriteDbNodeConverter::RewriteDbNodeConverter(NodeManager* nm,
                                               TConvProofGenerator* tpg,
                                               CDProof* p)
    : NodeConverter(nm), d_tpg(tpg), d_proof(p)
{
}

Node RewriteDbNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  if (k == Kind::CONST_STRING)
  {
    // "ABC" is (str.++ "A" "B" "C")
    const std::vector<unsigned>& vec = n.getConst<String>().getVec();
    if (vec.size() <= 1)
    {
      return n;
    }
    std::vector<Node> children;
    for (unsigned c : vec)
    {
      std::vector<unsigned> tmp;
      tmp.push_back(c);
      children.push_back(d_nm->mkConst(String(tmp)));
    }
    Node ret = d_nm->mkNode(Kind::STRING_CONCAT, children);
    recordProofStep(n, ret, ProofRule::EVALUATE);
    return ret;
  }
  else if (k == Kind::CONST_SEQUENCE)
  {
    Node ret = theory::strings::utils::mkConcatForConstSequence(n);
    recordProofStep(n, ret, ProofRule::ENCODE_EQ_INTRO);
    return ret;
  }
  else if (k == Kind::CONST_BITVECTOR)
  {
    // (_ bv N M) is (bv N M)
    std::vector<Node> children;
    children.push_back(
        d_nm->mkConstInt(Rational(n.getConst<BitVector>().toInteger())));
    children.push_back(
        d_nm->mkConstInt(Rational(theory::bv::utils::getSize(n))));
    Node ret = d_nm->mkNode(Kind::CONST_BITVECTOR_SYMBOLIC, children);
    recordProofStep(n, ret, ProofRule::EVALUATE);
    return ret;
  }
  else if (k == Kind::FUNCTION_ARRAY_CONST)
  {
    Node ret = theory::uf::FunctionConst::toLambda(n);
    recordProofStep(n, ret, ProofRule::ENCODE_EQ_INTRO);
    return ret;
  }
  else if (k == Kind::FORALL)
  {
    // ignore annotation
    if (n.getNumChildren() == 3)
    {
      Node ret = d_nm->mkNode(Kind::FORALL, n[0], n[1]);
      recordProofStep(n, ret, ProofRule::ENCODE_EQ_INTRO);
      return ret;
    }
  }
  else if (k == Kind::APPLY_UF)
  {
    Node ret = theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(n);
    recordProofStep(n, ret, ProofRule::ENCODE_EQ_INTRO);
    return ret;
  }
  else if (k == Kind::APPLY_CONSTRUCTOR)
  {
    // We apply annotations to parametric datatype constructors, which is
    // a no-op based on our proof signature.
    TypeNode tn = n.getType();
    if (tn.isParametricDatatype())
    {
      if (n.getOperator().getKind() != Kind::APPLY_TYPE_ASCRIPTION)
      {
        Node op = n.getOperator();
        size_t index = theory::datatypes::utils::indexOf(op);
        // get the constructor object
        const DTypeConstructor& dtc =
            theory::datatypes::utils::datatypeOf(op)[index];
        // create ascribed constructor type
        Node op_new = dtc.getInstantiatedConstructor(tn);
        // make new node
        std::vector<Node> children;
        children.push_back(op_new);
        children.insert(children.end(), n.begin(), n.end());
        Node inr = d_nm->mkNode(Kind::APPLY_CONSTRUCTOR, children);
        recordProofStep(n, inr, ProofRule::ENCODE_EQ_INTRO);
        return inr;
      }
    }
  }
  // convert indexed operators to symbolic
  if (GenericOp::isNumeralIndexedOperatorKind(k))
  {
    std::vector<Node> indices =
        GenericOp::getIndicesForOperator(k, n.getOperator());
    indices.insert(indices.begin(), d_nm->mkConst(GenericOp(k)));
    indices.insert(indices.end(), n.begin(), n.end());
    Node ret = d_nm->mkNode(Kind::APPLY_INDEXED_SYMBOLIC, indices);
    recordProofStep(n, ret, ProofRule::ENCODE_EQ_INTRO);
    return ret;
  }
  // since string constants are converted to concatenation terms, we ensure
  // these are flattened using ACI_NORM. This ensures (str.++ "AB" x) is
  // handled as (str.++ "A" "B" x), not (str.++ (str.++ "A" "B") x).
  if (k==Kind::STRING_CONCAT)
  {
    Node nacc = expr::getACINormalForm(n);
    recordProofStep(n, nacc, ProofRule::ACI_NORM);
    return nacc;
  }
  return n;
}

bool RewriteDbNodeConverter::shouldTraverse(Node n)
{
  return n.getKind() != Kind::INST_PATTERN_LIST;
}

void RewriteDbNodeConverter::recordProofStep(const Node& n,
                                             const Node& ret,
                                             ProofRule r)
{
  if (d_tpg == nullptr || n == ret)
  {
    return;
  }
  Assert(d_proof != nullptr);
  switch (r)
  {
    case ProofRule::ACI_NORM:
      d_tpg->addRewriteStep(n, ret, r, {}, {n.eqNode(ret)});
      break;
    case ProofRule::EVALUATE:
    {
      // Evaluate step in reverse, using d_proof as an intermediate step.
      // For instance, we require proving "ABC" = (str.++ "A" "B" "C").
      // We prove this by
      // ---------------------------- EVALUATE
      // (str.++ "A" "B" "C") = "ABC"
      // ----------------------------- SYMM
      // "ABC" = (str.++ "A" "B" "C")
      Node eq = ret.eqNode(n);
      d_proof->addStep(eq, ProofRule::EVALUATE, {}, {ret});
      d_tpg->addRewriteStep(n, ret, d_proof);
    }
    break;
    case ProofRule::ENCODE_EQ_INTRO:
      d_tpg->addRewriteStep(n, ret, r, {}, {n});
      break;
    default: break;
  }
}

ProofRewriteDbNodeConverter::ProofRewriteDbNodeConverter(Env& env)
    : EnvObj(env),
      d_wktc(Kind::INST_PATTERN_LIST),
      // must rewrite within operators
      d_tpg(env,
            nullptr,
            TConvPolicy::FIXPOINT,
            TConvCachePolicy::NEVER,
            "ProofRewriteDb",
            &d_wktc,
            true),
      d_proof(env)
{
}

std::shared_ptr<ProofNode> ProofRewriteDbNodeConverter::convert(const Node& n)
{
  RewriteDbNodeConverter rdnc(nodeManager(), &d_tpg, &d_proof);
  Node nr = rdnc.convert(n);
  Node equiv = n.eqNode(nr);
  return d_tpg.getProofFor(equiv);
}

}  // namespace rewriter
}  // namespace cvc5::internal
