/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Valid witness proof generator utility.
 */

#include "proof/valid_witness_proof_generator.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/skolem_manager.h"
#include "expr/sort_to_term.h"
#include "proof/proof.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_rule_checker.h"
#include "theory/quantifiers/bv_inverter.h"
#include "util/string.h"

namespace cvc5::internal {

/**
 * Mapping from predicates to the arguments used in mkAxiom
 */
struct ValidWitnessAxiomAttributeId
{
};
using ValidWitnessAxiomAttribute =
    expr::Attribute<ValidWitnessAxiomAttributeId, Node>;
/**
 * Mapping to the variable used for binding the witness term.
 */
struct ValidWitnessVarAttributeId
{
};
using ValidWitnessVarAttribute =
    expr::Attribute<ValidWitnessVarAttributeId, Node>;

/**
 * Makes an instantiation attribute whose value is an s-expression
 * corresponding to the application of a proof rule.
 */
Node mkProofSpec(NodeManager* nm, ProofRule r, const std::vector<Node>& args)
{
  std::vector<Node> pfspec;
  pfspec.push_back(nm->mkConst(String("witness")));
  std::vector<Node> sargs;
  // store as uint32_t
  sargs.push_back(nm->mkConstInt(Rational(static_cast<uint32_t>(r))));
  sargs.insert(sargs.end(), args.begin(), args.end());
  pfspec.push_back(nm->mkNode(Kind::SEXPR, sargs));
  return nm->mkNode(Kind::INST_ATTRIBUTE, pfspec);
}

/**
 * The inverse operation for mkProofSpec, if possible extracts the proof
 * rule and args from a given instantiation attribute attr.
 */
bool ValidWitnessProofGenerator::getProofSpec(NodeManager* nm,
                                              const Node& attr,
                                              ProofRule& r,
                                              std::vector<Node>& args)
{
  if (attr.getKind() == Kind::INST_ATTRIBUTE && attr.getNumChildren() == 2)
  {
    if (attr[0].getKind() == Kind::CONST_STRING
        && attr[1].getKind() == Kind::SEXPR && attr[1].getNumChildren() > 0)
    {
      std::string str = attr[0].getConst<String>().toString();
      if (str == "witness")
      {
        Node rn = attr[1][0];
        uint32_t rval;
        if (ProofRuleChecker::getUInt32(rn, rval))
        {
          r = static_cast<ProofRule>(rval);
          args.insert(args.end(), attr[1].begin() + 1, attr[1].end());
          return true;
        }
      }
    }
  }
  return false;
}

ValidWitnessProofGenerator::ValidWitnessProofGenerator(Env& env) : EnvObj(env) {}

ValidWitnessProofGenerator::~ValidWitnessProofGenerator() {}

std::shared_ptr<ProofNode> ValidWitnessProofGenerator::getProofFor(Node fact) 
{
  Trace("valid-witness") << "ValidWitness: Prove " << fact << std::endl;
  bool success = false;
  CDProof cdp(d_env);
  // if it was constructed via mkAxiom, we should have marked it with the
  // given attribute.
  ValidWitnessAxiomAttribute vwa;
  if (fact.hasAttribute(vwa))
  {
    Node spec = fact.getAttribute(vwa);
    ProofRule r;
    std::vector<Node> args;
    if (!spec.isNull() && getProofSpec(nodeManager(), spec, r, args))
    {
      success = true;
      cdp.addStep(fact, r, {}, args);
    }
  }
  if (!success)
  {
    // proof failed
    cdp.addTrustedStep(fact, TrustId::VALID_WITNESS, {}, {});
  }
  return cdp.getProofFor(fact);
}

std::string ValidWitnessProofGenerator::identify() const { return "ValidWitnessProofGenerator"; }

Node ValidWitnessProofGenerator::mkWitness(NodeManager* nm,
                                           ProofRule r,
                                           const std::vector<Node>& args)
{
  // must make the skolem to know what type the rule expects
  Node k = mkSkolem(nm, r, args);
  if (k.isNull())
  {
    return k;
  }
  // construct the bound variable based on the type of the skolem
  BoundVarManager* bvm = nm->getBoundVarManager();
  Node v = bvm->mkBoundVar(
      BoundVarId::VALID_WITNESS_VAR, k, "@var.witness", k.getType());
  // make the axiom
  Node ax = mkAxiom(nm, k, r, args);
  if (ax.isNull())
  {
    return ax;
  }
  TNode tk = k;
  TNode tv = v;
  ax = ax.substitute(tk, tv);
  std::vector<Node> children;
  children.push_back(nm->mkNode(Kind::BOUND_VAR_LIST, v));
  children.push_back(ax);
  // Store a marking to remember the origin of the witness. This ensures we
  // have a way to recognize
  children.push_back(
      nm->mkNode(Kind::INST_PATTERN_LIST, mkProofSpec(nm, r, args)));
  return nm->mkNode(Kind::WITNESS, children);
}

Node ValidWitnessProofGenerator::mkAxiom(NodeManager* nm,
                                         const Node& v,
                                         ProofRule r,
                                         const std::vector<Node>& args)
{
  Assert(!v.isNull());
  // then construct the predicate
  Node pred;
  Node spec = mkProofSpec(nm, r, args);
  switch (r)
  {
    case ProofRule::EXISTS_STRING_LENGTH:
      Assert(args.size() == 3);
      // only applicable for non-negative constants (for now)
      if (args[1].getKind() == Kind::CONST_INTEGER
          && args[1].getConst<Rational>().getNumerator().sgn() >= 0)
      {
        pred = nm->mkNode(Kind::STRING_LENGTH, v).eqNode(args[1]);
      }
      break;
    default: break;
  }
  // mark the attribute, to remember proof reconstruction
  if (!pred.isNull())
  {
    ValidWitnessAxiomAttribute vwa;
    pred.setAttribute(vwa, spec);
  }
  return pred;
}

Node ValidWitnessProofGenerator::mkSkolem(NodeManager* nm,
                                          ProofRule r,
                                          const std::vector<Node>& args)
{
  SkolemId id = SkolemId::NONE;
  switch (r)
  {
    case ProofRule::EXISTS_STRING_LENGTH:
      id = SkolemId::WITNESS_STRING_LENGTH;
      break;
    default: break;
  }
  if (id == SkolemId::NONE)
  {
    return Node::null();
  }
  return nm->getSkolemManager()->mkSkolemFunction(id, args);
}

}  // namespace cvc5::internal

