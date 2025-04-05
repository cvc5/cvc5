/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of QuantifiersRewriter class.
 */

#include "theory/quantifiers/quantifiers_rewriter.h"

#include "expr/ascription_type.h"
#include "expr/bound_var_manager.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/elim_shadow_converter.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_poly_norm.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/extended_rewrite.h"
#include "theory/quantifiers/quant_split.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

std::ostream& operator<<(std::ostream& out, RewriteStep s)
{
  switch (s)
  {
    case COMPUTE_ELIM_SYMBOLS: out << "COMPUTE_ELIM_SYMBOLS"; break;
    case COMPUTE_MINISCOPING: out << "COMPUTE_MINISCOPING"; break;
    case COMPUTE_AGGRESSIVE_MINISCOPING:
      out << "COMPUTE_AGGRESSIVE_MINISCOPING";
      break;
    case COMPUTE_PROCESS_TERMS: out << "COMPUTE_PROCESS_TERMS"; break;
    case COMPUTE_PRENEX: out << "COMPUTE_PRENEX"; break;
    case COMPUTE_VAR_ELIMINATION: out << "COMPUTE_VAR_ELIMINATION"; break;
    case COMPUTE_DT_VAR_EXPAND: out << "COMPUTE_DT_VAR_EXPAND"; break;
    case COMPUTE_COND_SPLIT: out << "COMPUTE_COND_SPLIT"; break;
    case COMPUTE_EXT_REWRITE: out << "COMPUTE_EXT_REWRITE"; break;
    default: out << "UnknownRewriteStep"; break;
  }
  return out;
}

QuantifiersRewriter::QuantifiersRewriter(NodeManager* nm,
                                         Rewriter* r,
                                         const Options& opts)
    : TheoryRewriter(nm), d_rewriter(r), d_opts(opts)
{
  registerProofRewriteRule(ProofRewriteRule::EXISTS_ELIM,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::QUANT_UNUSED_VARS,
                           TheoryRewriteCtx::PRE_DSL);
  // QUANT_MERGE_PRENEX is part of the reconstruction for
  // MACRO_QUANT_MERGE_PRENEX
  registerProofRewriteRule(ProofRewriteRule::MACRO_QUANT_MERGE_PRENEX,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_QUANT_PRENEX,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_QUANT_MINISCOPE,
                           TheoryRewriteCtx::PRE_DSL);
  // QUANT_MINISCOPE_OR is part of the reconstruction for MACRO_QUANT_MINISCOPE
  registerProofRewriteRule(ProofRewriteRule::MACRO_QUANT_PARTITION_CONNECTED_FV,
                           TheoryRewriteCtx::PRE_DSL);
  // note ProofRewriteRule::QUANT_DT_SPLIT is done by a module dynamically with
  // manual proof generation thus not registered here.
  registerProofRewriteRule(ProofRewriteRule::MACRO_QUANT_VAR_ELIM_EQ,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_QUANT_VAR_ELIM_INEQ,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_QUANT_DT_VAR_EXPAND,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_QUANT_REWRITE_BODY,
                           TheoryRewriteCtx::PRE_DSL);
}

Node QuantifiersRewriter::rewriteViaRule(ProofRewriteRule id, const Node& n)
{
  switch (id)
  {
    case ProofRewriteRule::EXISTS_ELIM:
    {
      if (n.getKind() != Kind::EXISTS)
      {
        return Node::null();
      }
      std::vector<Node> fchildren;
      fchildren.push_back(n[0]);
      fchildren.push_back(n[1].notNode());
      if (n.getNumChildren() == 3)
      {
        fchildren.push_back(n[2]);
      }
      return d_nm->mkNode(Kind::NOT, d_nm->mkNode(Kind::FORALL, fchildren));
    }
    case ProofRewriteRule::QUANT_UNUSED_VARS:
    {
      if (!n.isClosure())
      {
        return Node::null();
      }
      std::vector<Node> vars(n[0].begin(), n[0].end());
      std::vector<Node> activeVars;
      computeArgVec(vars, activeVars, n[1]);
      if (activeVars.size() < vars.size())
      {
        if (activeVars.empty())
        {
          return n[1];
        }
        return d_nm->mkNode(
            n.getKind(), d_nm->mkNode(Kind::BOUND_VAR_LIST, activeVars), n[1]);
      }
    }
    break;
    case ProofRewriteRule::MACRO_QUANT_MERGE_PRENEX:
    case ProofRewriteRule::QUANT_MERGE_PRENEX:
    {
      if (!n.isClosure())
      {
        return Node::null();
      }
      // Don't check standard here, which can't be replicated in a proof checker
      // without modelling the patterns.
      // We remove duplicates if the macro version.
      Node q = mergePrenex(
          n, false, id == ProofRewriteRule::MACRO_QUANT_MERGE_PRENEX);
      if (q != n)
      {
        return q;
      }
    }
    break;
    case ProofRewriteRule::MACRO_QUANT_PRENEX:
    {
      if (n.getKind() == Kind::FORALL)
      {
        std::vector<Node> args, nargs;
        Node nn = computePrenex(n, n[1], args, nargs, true, false);
        Assert(nargs.empty());
        if (!args.empty())
        {
          std::vector<Node> qargs(n[0].begin(), n[0].end());
          qargs.insert(qargs.end(), args.begin(), args.end());
          Node bvl = d_nm->mkNode(Kind::BOUND_VAR_LIST, qargs);
          return d_nm->mkNode(Kind::FORALL, bvl, nn);
        }
      }
    }
    break;
    case ProofRewriteRule::MACRO_QUANT_MINISCOPE:
    {
      if (n.getKind() != Kind::FORALL)
      {
        return Node::null();
      }
      Kind k = n[1].getKind();
      if (k != Kind::AND && k != Kind::ITE)
      {
        return Node::null();
      }
      // note that qa is not needed; moreover external proofs should be agnostic
      // to it
      QAttributes qa;
      QuantAttributes::computeQuantAttributes(n, qa);
      Node nret = computeMiniscoping(n, qa, true, false);
      if (nret != n)
      {
        return nret;
      }
    }
    break;
    case ProofRewriteRule::QUANT_MINISCOPE_AND:
    {
      if (n.getKind() != Kind::FORALL || n[1].getKind() != Kind::AND)
      {
        return Node::null();
      }
      std::vector<Node> conj;
      for (const Node& nc : n[1])
      {
        conj.push_back(d_nm->mkNode(Kind::FORALL, n[0], nc));
      }
      return d_nm->mkAnd(conj);
    }
    break;
    case ProofRewriteRule::MACRO_QUANT_PARTITION_CONNECTED_FV:
    {
      if (n.getKind() != Kind::FORALL || n[1].getKind() != Kind::OR)
      {
        return Node::null();
      }
      // note that qa is not needed; moreover external proofs should be agnostic
      // to it
      QAttributes qa;
      QuantAttributes::computeQuantAttributes(n, qa);
      std::vector<Node> vars(n[0].begin(), n[0].end());
      Node body = n[1];
      Node nret = computeSplit(vars, body, qa);
      if (!nret.isNull())
      {
        // only do this rule if it is a proper split; otherwise it will be
        // subsumed by QUANT_UNUSED_VARS.
        if (nret.getKind() == Kind::OR)
        {
          return nret;
        }
      }
    }
    break;
    case ProofRewriteRule::QUANT_MINISCOPE_OR:
    {
      if (n.getKind() != Kind::FORALL || n[1].getKind() != Kind::OR)
      {
        return Node::null();
      }
      size_t nvars = n[0].getNumChildren();
      std::vector<Node> disj;
      std::unordered_set<Node> varsUsed;
      size_t varIndex = 0;
      for (const Node& d : n[1])
      {
        // Note that we may apply to a nested quantified formula, in which
        // case some variables in fvs may not be bound by this quantified
        // formula.
        std::unordered_set<Node> fvs;
        expr::getFreeVariables(d, fvs);
        size_t prevVarIndex = varIndex;
        while (varIndex < nvars && fvs.find(n[0][varIndex]) != fvs.end())
        {
          // cannot have shadowing
          if (varsUsed.find(n[0][varIndex]) != varsUsed.end())
          {
            return Node::null();
          }
          varsUsed.insert(n[0][varIndex]);
          varIndex++;
        }
        std::vector<Node> dvs(n[0].begin() + prevVarIndex,
                              n[0].begin() + varIndex);
        if (dvs.empty())
        {
          disj.emplace_back(d);
        }
        else
        {
          Node bvl = d_nm->mkNode(Kind::BOUND_VAR_LIST, dvs);
          disj.emplace_back(d_nm->mkNode(Kind::FORALL, bvl, d));
        }
      }
      // must consume all variables
      if (varIndex != nvars)
      {
        return Node::null();
      }
      Node ret = d_nm->mkOr(disj);
      // go back and ensure all variables are bound
      std::unordered_set<Node> fvs;
      expr::getFreeVariables(ret, fvs);
      for (const Node& v : n[0])
      {
        if (fvs.find(v) != fvs.end())
        {
          return Node::null();
        }
      }
      return ret;
    }
    break;
    case ProofRewriteRule::QUANT_MINISCOPE_ITE:
    {
      if (n.getKind() != Kind::FORALL || n[1].getKind() != Kind::ITE)
      {
        return Node::null();
      }
      std::vector<Node> args(n[0].begin(), n[0].end());
      Node body = n[1];
      if (!expr::hasSubterm(body[0], args))
      {
        return d_nm->mkNode(Kind::ITE,
                            body[0],
                            d_nm->mkNode(Kind::FORALL, n[0], body[1]),
                            d_nm->mkNode(Kind::FORALL, n[0], body[2]));
      }
    }
    break;
    case ProofRewriteRule::QUANT_DT_SPLIT:
    {
      // always runs split utility on the first variable
      if (n.getKind() != Kind::FORALL || !n[0][0].getType().isDatatype())
      {
        return Node::null();
      }
      return QuantDSplit::split(nodeManager(), n, 0);
    }
    break;
    case ProofRewriteRule::MACRO_QUANT_DT_VAR_EXPAND:
    {
      if (n.getKind() != Kind::FORALL)
      {
        return Node::null();
      }
      size_t index;
      Node nn = computeDtVarExpand(nodeManager(), n, index);
      if (nn != n)
      {
        return nn;
      }
      return Node::null();
    }
    break;
    case ProofRewriteRule::MACRO_QUANT_VAR_ELIM_EQ:
    case ProofRewriteRule::QUANT_VAR_ELIM_EQ:
    case ProofRewriteRule::MACRO_QUANT_VAR_ELIM_INEQ:
    {
      if (n.getKind() != Kind::FORALL || n.getNumChildren() != 2)
      {
        return Node::null();
      }
      std::vector<Node> args(n[0].begin(), n[0].end());
      std::vector<Node> vars;
      std::vector<Node> subs;
      Node body = n[1];
      if (id == ProofRewriteRule::MACRO_QUANT_VAR_ELIM_EQ)
      {
        std::vector<Node> lits;
        getVarElim(body, args, vars, subs, lits);
      }
      else if (id == ProofRewriteRule::QUANT_VAR_ELIM_EQ)
      {
        if (args.size() != 1)
        {
          return Node::null();
        }
        std::vector<Node> lits;
        if (body.getKind() == Kind::OR)
        {
          lits.insert(lits.end(), body.begin(), body.end());
        }
        else
        {
          lits.push_back(body);
        }
        if (lits[0].getKind() != Kind::NOT
            || lits[0][0].getKind() != Kind::EQUAL)
        {
          return Node::null();
        }
        Node eq = lits[0][0];
        if (eq[0] != args[0] || expr::hasSubterm(eq[1], eq[0]))
        {
          return Node::null();
        }
        vars.push_back(eq[0]);
        subs.push_back(eq[1]);
        args.clear();
        std::vector<Node> remLits(lits.begin() + 1, lits.end());
        body = d_nm->mkOr(remLits);
      }
      else
      {
        Assert(id == ProofRewriteRule::MACRO_QUANT_VAR_ELIM_INEQ);
        // assume empty attribute
        QAttributes qa;
        Node ret = getVarElimIneq(n[1], args, qa);
        if (!ret.isNull() && !args.empty())
        {
          Node vlist = d_nm->mkNode(Kind::BOUND_VAR_LIST, args);
          ret = d_nm->mkNode(Kind::FORALL, vlist, ret);
        }
        return ret;
      }
      // if we eliminated a variable, update body and reprocess
      if (!vars.empty())
      {
        Assert(vars.size() == subs.size());
        std::vector<Node> qc(n.begin(), n.end());
        qc[1] =
            body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
        if (args.empty())
        {
          return qc[1];
        }
        qc[0] = d_nm->mkNode(Kind::BOUND_VAR_LIST, args);
        return d_nm->mkNode(Kind::FORALL, qc);
      }
    }
    break;
    case ProofRewriteRule::MACRO_QUANT_REWRITE_BODY:
    {
      if (n.getKind() != Kind::FORALL)
      {
        return Node::null();
      }
      Node nr = computeRewriteBody(n);
      if (nr != n)
      {
        return nr;
      }
    }
    break;
    default: break;
  }
  return Node::null();
}

bool QuantifiersRewriter::isLiteral( Node n ){
  switch( n.getKind() ){
    case Kind::NOT:
      return n[0].getKind() != Kind::NOT && isLiteral(n[0]);
      break;
    case Kind::OR:
    case Kind::AND:
    case Kind::IMPLIES:
    case Kind::XOR:
    case Kind::ITE: return false; break;
    case Kind::EQUAL:
      // for boolean terms
      return !n[0].getType().isBoolean();
      break;
    default: break;
  }
  return true;
}

void QuantifiersRewriter::computeArgs(const std::vector<Node>& args,
                                      std::map<Node, bool>& activeMap,
                                      Node n,
                                      std::map<Node, bool>& visited)
{
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if (n.getKind() == Kind::BOUND_VARIABLE)
    {
      if( std::find( args.begin(), args.end(), n )!=args.end() ){
        activeMap[ n ] = true;
      }
    }
    else
    {
      if (n.hasOperator())
      {
        computeArgs(args, activeMap, n.getOperator(), visited);
      }
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        computeArgs( args, activeMap, n[i], visited );
      }
    }
  }
}

void QuantifiersRewriter::computeArgVec(const std::vector<Node>& args,
                                        std::vector<Node>& activeArgs,
                                        Node n)
{
  Assert(activeArgs.empty());
  std::map< Node, bool > activeMap;
  std::map< Node, bool > visited;
  computeArgs( args, activeMap, n, visited );
  if( !activeMap.empty() ){
    std::map<Node, bool>::iterator it;
    for (const Node& v : args)
    {
      it = activeMap.find(v);
      if (it != activeMap.end())
      {
        activeArgs.emplace_back(v);
        // no longer active, which accounts for deleting duplicates
        activeMap.erase(it);
      }
    }
  }
}

void QuantifiersRewriter::computeArgVec2(const std::vector<Node>& args,
                                         std::vector<Node>& activeArgs,
                                         Node n,
                                         Node ipl)
{
  Assert(activeArgs.empty());
  std::map< Node, bool > activeMap;
  std::map< Node, bool > visited;
  computeArgs( args, activeMap, n, visited );
  // Collect variables in inst pattern list only if we cannot eliminate
  // quantifier, or if we have an add-to-pool annotation.
  bool varComputePatList = !activeMap.empty();
  for (const Node& ip : ipl)
  {
    Kind k = ip.getKind();
    if (k == Kind::INST_ADD_TO_POOL || k == Kind::SKOLEM_ADD_TO_POOL)
    {
      varComputePatList = true;
      break;
    }
  }
  if (varComputePatList)
  {
    computeArgs( args, activeMap, ipl, visited );
  }
  if (!activeMap.empty())
  {
    for (const Node& a : args)
    {
      if (activeMap.find(a) != activeMap.end())
      {
        activeArgs.push_back(a);
      }
    }
  }
}

RewriteResponse QuantifiersRewriter::preRewrite(TNode q)
{
  Kind k = q.getKind();
  if (k == Kind::FORALL || k == Kind::EXISTS)
  {
    // Do prenex merging now, since this may impact trigger selection.
    // In particular consider:
    //   (forall ((x Int)) (forall ((y Int)) (! (P x) :pattern ((f x)))))
    // If we wait until post-rewrite, we would rewrite the inner quantified
    // formula, dropping the pattern, so the entire formula becomes:
    //   (forall ((x Int)) (P x))
    // Instead, we merge to:
    //   (forall ((x Int) (y Int)) (! (P x) :pattern ((f x))))
    // eagerly here, where after we would drop y to obtain:
    //   (forall ((x Int)) (! (P x) :pattern ((f x))))
    // See issue #10303.
    Node qm = mergePrenex(q, true, true);
    if (q != qm)
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, qm);
    }
  }
  return RewriteResponse(REWRITE_DONE, q);
}

RewriteResponse QuantifiersRewriter::postRewrite(TNode in)
{
  Trace("quantifiers-rewrite-debug") << "post-rewriting " << in << std::endl;
  RewriteStatus status = REWRITE_DONE;
  Node ret = in;
  RewriteStep rew_op = COMPUTE_LAST;
  // get the body
  if (in.getKind() == Kind::EXISTS)
  {
    std::vector<Node> children;
    children.push_back(in[0]);
    children.push_back(in[1].notNode());
    if (in.getNumChildren() == 3)
    {
      children.push_back(in[2]);
    }
    ret = nodeManager()->mkNode(Kind::FORALL, children);
    ret = ret.negate();
    status = REWRITE_AGAIN_FULL;
  }
  else if (in.getKind() == Kind::FORALL)
  {
    // do prenex merging
    ret = mergePrenex(in, true, true);
    if (ret != in)
    {
      status = REWRITE_AGAIN_FULL;
    }
    else if (in[1].isConst() && in.getNumChildren() == 2)
    {
      return RewriteResponse( status, in[1] );
    }
    else
    {
      //compute attributes
      QAttributes qa;
      QuantAttributes::computeQuantAttributes( in, qa );
      for (unsigned i = 0; i < COMPUTE_LAST; ++i)
      {
        RewriteStep op = static_cast<RewriteStep>(i);
        if( doOperation( in, op, qa ) ){
          ret = computeOperation( in, op, qa );
          if( ret!=in ){
            rew_op = op;
            status = REWRITE_AGAIN_FULL;
            break;
          }
        }
      }
    }
  }
  //print if changed
  if( in!=ret ){
    Trace("quantifiers-rewrite") << "*** rewrite (op=" << rew_op << ") " << in << std::endl;
    Trace("quantifiers-rewrite") << " to " << std::endl;
    Trace("quantifiers-rewrite") << ret << std::endl;
  }
  return RewriteResponse( status, ret );
}

Node QuantifiersRewriter::mergePrenex(const Node& q, bool checkStd, bool rmDup)
{
  Assert(q.getKind() == Kind::FORALL || q.getKind() == Kind::EXISTS);
  Kind k = q.getKind();
  std::vector<Node> boundVars;
  Node body = q;
  bool combineQuantifiers = false;
  bool continueCombine = false;
  do
  {
    if (rmDup)
    {
      for (const Node& v : body[0])
      {
        if (std::find(boundVars.begin(), boundVars.end(), v) == boundVars.end())
        {
          boundVars.push_back(v);
        }
        else
        {
          // if duplicate variable due to shadowing, we must rewrite
          combineQuantifiers = true;
        }
      }
    }
    else
    {
      boundVars.insert(boundVars.end(), body[0].begin(), body[0].end());
    }
    continueCombine = false;
    if (body.getNumChildren() == 2 && body[1].getKind() == k)
    {
      bool process = true;
      if (checkStd)
      {
        // Should never combine a quantified formula with a pool or
        // non-standard quantified formula here.
        // Note that we technically should check
        // doOperation(body[1], COMPUTE_PRENEX, qa) here, although this
        // is too restrictive, as sometimes nested patterns should just be
        // applied to the top level, for example:
        // (forall ((x Int)) (forall ((y Int)) (! P :pattern ((f x y)))))
        // should be a pattern for the top-level quantifier here.
        QAttributes qa;
        QuantAttributes::computeQuantAttributes(body[1], qa);
        process = qa.isStandard();
      }
      if (process)
      {
        body = body[1];
        continueCombine = true;
        combineQuantifiers = true;
      }
    }
  } while (continueCombine);
  if (combineQuantifiers)
  {
    NodeManager* nm = nodeManager();
    std::vector<Node> children;
    children.push_back(nm->mkNode(Kind::BOUND_VAR_LIST, boundVars));
    children.push_back(body[1]);
    if (body.getNumChildren() == 3)
    {
      children.push_back(body[2]);
    }
    return nm->mkNode(k, children);
  }
  return q;
}

void QuantifiersRewriter::computeDtTesterIteSplit(
    Node n,
    std::map<Node, Node>& pcons,
    std::map<Node, std::map<int, Node>>& ncons,
    std::vector<Node>& conj) const
{
  if (n.getKind() == Kind::ITE && n[0].getKind() == Kind::APPLY_TESTER
      && n[1].getType().isBoolean())
  {
    Trace("quantifiers-rewrite-ite-debug") << "Split tester condition : " << n << std::endl;
    Node x = n[0][0];
    std::map< Node, Node >::iterator itp = pcons.find( x );
    if( itp!=pcons.end() ){
      Trace("quantifiers-rewrite-ite-debug") << "...condition already set " << itp->second << std::endl;
      computeDtTesterIteSplit( n[ itp->second==n[0] ? 1 : 2 ], pcons, ncons, conj );
    }else{
      Node tester = n[0].getOperator();
      int index = datatypes::utils::indexOf(tester);
      std::map< int, Node >::iterator itn = ncons[x].find( index );
      if( itn!=ncons[x].end() ){
        Trace("quantifiers-rewrite-ite-debug") << "...condition negated " << itn->second << std::endl;
        computeDtTesterIteSplit( n[ 2 ], pcons, ncons, conj );
      }else{
        for( unsigned i=0; i<2; i++ ){
          if( i==0 ){
            pcons[x] = n[0];
          }else{
            pcons.erase( x );
            ncons[x][index] = n[0].negate();
          }
          computeDtTesterIteSplit( n[i+1], pcons, ncons, conj );
        }
        ncons[x].erase( index );
      }
    }
  }
  else
  {
    NodeManager* nm = nodeManager();
    Trace("quantifiers-rewrite-ite-debug") << "Return value : " << n << std::endl;
    std::vector< Node > children;
    children.push_back( n );
    std::vector< Node > vars;
    //add all positive testers
    for( std::map< Node, Node >::iterator it = pcons.begin(); it != pcons.end(); ++it ){
      children.push_back( it->second.negate() );
      vars.push_back( it->first );
    }
    //add all negative testers
    for( std::map< Node, std::map< int, Node > >::iterator it = ncons.begin(); it != ncons.end(); ++it ){
      Node x = it->first;
      //only if we haven't settled on a positive tester
      if( std::find( vars.begin(), vars.end(), x )==vars.end() ){
        //check if we have exhausted all options but one
        const DType& dt = x.getType().getDType();
        std::vector< Node > nchildren;
        int pos_cons = -1;
        for( int i=0; i<(int)dt.getNumConstructors(); i++ ){
          std::map< int, Node >::iterator itt = it->second.find( i );
          if( itt==it->second.end() ){
            pos_cons = pos_cons==-1 ? i : -2;
          }else{
            nchildren.push_back( itt->second.negate() );
          }
        }
        if( pos_cons>=0 ){
          Node tester = dt[pos_cons].getTester();
          children.push_back(
              nm->mkNode(Kind::APPLY_TESTER, tester, x).negate());
        }else{
          children.insert( children.end(), nchildren.begin(), nchildren.end() );
        }
      }
    }
    //make condition/output pair
    Node c = children.size() == 1 ? children[0]
                                  : nodeManager()->mkNode(Kind::OR, children);
    conj.push_back( c );
  }
}

Node QuantifiersRewriter::computeProcessTerms(const Node& q,
                                              const std::vector<Node>& args,
                                              Node body,
                                              QAttributes& qa,
                                              TConvProofGenerator* pg) const
{
  options::IteLiftQuantMode iteLiftMode = options::IteLiftQuantMode::NONE;
  if (qa.isStandard())
  {
    iteLiftMode = d_opts.quantifiers.iteLiftQuant;
  }
  std::map<Node, Node> cache;
  return computeProcessTerms2(q, args, body, cache, iteLiftMode, pg);
}

Node QuantifiersRewriter::computeProcessTerms2(
    const Node& q,
    const std::vector<Node>& args,
    Node body,
    std::map<Node, Node>& cache,
    options::IteLiftQuantMode iteLiftMode,
    TConvProofGenerator* pg) const
{
  NodeManager* nm = nodeManager();
  Trace("quantifiers-rewrite-term-debug2")
      << "computeProcessTerms " << body << std::endl;
  std::map< Node, Node >::iterator iti = cache.find( body );
  if( iti!=cache.end() ){
    return iti->second;
  }
  bool changed = false;
  std::vector<Node> children;
  for (const Node& bc : body)
  {
    // do the recursive call on children
    Node nn = computeProcessTerms2(q, args, bc, cache, iteLiftMode, pg);
    children.push_back(nn);
    changed = changed || nn != bc;
  }

  // make return value
  Node ret;
  if (changed)
  {
    if (body.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.insert(children.begin(), body.getOperator());
    }
    ret = nm->mkNode(body.getKind(), children);
  }
  else
  {
    ret = body;
  }

  Node retOrig = ret;
  Trace("quantifiers-rewrite-term-debug2")
      << "Returning " << ret << " for " << body << std::endl;
  // do context-independent rewriting
  if (ret.isClosure())
  {
    // Ensure no shadowing. If this term is a closure quantifying a variable
    // in args, then we introduce fresh variable(s) and replace this closure
    // to be over the fresh variables instead.
    std::vector<Node> oldVars;
    std::vector<Node> newVars;
    for (size_t i = 0, nvars = ret[0].getNumChildren(); i < nvars; i++)
    {
      const Node& v = ret[0][i];
      if (std::find(args.begin(), args.end(), v) != args.end())
      {
        Trace("quantifiers-rewrite-unshadow")
            << "Found shadowed variable " << v << " in " << q << std::endl;
        oldVars.push_back(v);
        Node nv = ElimShadowNodeConverter::getElimShadowVar(q, ret, i);
        newVars.push_back(nv);
      }
    }
    if (!oldVars.empty())
    {
      Assert(oldVars.size() == newVars.size());
      Node sbody = ret.substitute(
          oldVars.begin(), oldVars.end(), newVars.begin(), newVars.end());
      ret = sbody;
    }
  }
  else if (ret.getKind() == Kind::EQUAL
           && iteLiftMode != options::IteLiftQuantMode::NONE)
  {
    for (size_t i = 0; i < 2; i++)
    {
      if (ret[i].getKind() == Kind::ITE)
      {
        Node no = i == 0 ? ret[1] : ret[0];
        if (no.getKind() != Kind::ITE)
        {
          bool doRewrite = (iteLiftMode == options::IteLiftQuantMode::ALL);
          std::vector<Node> childrenIte;
          childrenIte.push_back(ret[i][0]);
          for (size_t j = 1; j <= 2; j++)
          {
            // check if it rewrites to a constant
            Node nn = nm->mkNode(Kind::EQUAL, no, ret[i][j]);
            childrenIte.push_back(nn);
            // check if it will rewrite to a constant
            if (no == ret[i][j] || (no.isConst() && ret[i][j].isConst()))
            {
              doRewrite = true;
            }
          }
          if (doRewrite)
          {
            ret = nm->mkNode(Kind::ITE, childrenIte);
            break;
          }
        }
      }
    }
  }
  else if (ret.getKind() == Kind::SELECT && ret[0].getKind() == Kind::STORE)
  {
    Node st = ret[0];
    Node index = ret[1];
    std::vector<Node> iconds;
    std::vector<Node> elements;
    while (st.getKind() == Kind::STORE)
    {
      iconds.push_back(index.eqNode(st[1]));
      elements.push_back(st[2]);
      st = st[0];
    }
    ret = nm->mkNode(Kind::SELECT, st, index);
    // conditions
    for (int i = (iconds.size() - 1); i >= 0; i--)
    {
      ret = nm->mkNode(Kind::ITE, iconds[i], elements[i], ret);
    }
  }
  else if (ret.getKind() == Kind::HO_APPLY && !ret.getType().isFunction())
  {
    // fully applied functions are converted to APPLY_UF here.
    Node fullApp = uf::TheoryUfRewriter::getApplyUfForHoApply(ret);
    // it may not be possible to convert e.g. if the head is not a variable
    if (!fullApp.isNull())
    {
      ret = fullApp;
    }
  }
  if (pg != nullptr)
  {
    if (retOrig != ret)
    {
      pg->addRewriteStep(retOrig,
                         ret,
                         nullptr,
                         false,
                         TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
    }
  }
  cache[body] = ret;
  return ret;
}

Node QuantifiersRewriter::computeExtendedRewrite(TNode q,
                                                 const QAttributes& qa) const
{
  // do not apply to recursive functions
  if (qa.isFunDef())
  {
    return q;
  }
  Node body = q[1];
  // apply extended rewriter
  Node bodyr = d_rewriter->extendedRewrite(body);
  if (body != bodyr)
  {
    std::vector<Node> children;
    children.push_back(q[0]);
    children.push_back(bodyr);
    if (q.getNumChildren() == 3)
    {
      children.push_back(q[2]);
    }
    return nodeManager()->mkNode(Kind::FORALL, children);
  }
  return q;
}

Node QuantifiersRewriter::computeCondSplit(Node body,
                                           const std::vector<Node>& args,
                                           QAttributes& qa) const
{
  NodeManager* nm = nodeManager();
  Kind bk = body.getKind();
  if (d_opts.quantifiers.iteDtTesterSplitQuant && bk == Kind::ITE
      && body[0].getKind() == Kind::APPLY_TESTER)
  {
    Trace("quantifiers-rewrite-ite-debug") << "DTT split : " << body << std::endl;
    std::map< Node, Node > pcons;
    std::map< Node, std::map< int, Node > > ncons;
    std::vector< Node > conj;
    computeDtTesterIteSplit( body, pcons, ncons, conj );
    Assert(!conj.empty());
    if( conj.size()>1 ){
      Trace("quantifiers-rewrite-ite") << "*** Split ITE (datatype tester) " << body << " into : " << std::endl;
      for( unsigned i=0; i<conj.size(); i++ ){
        Trace("quantifiers-rewrite-ite") << "   " << conj[i] << std::endl;
      }
      return nm->mkNode(Kind::AND, conj);
    }
  }
  if (d_opts.quantifiers.condVarSplitQuant
      == options::CondVarSplitQuantMode::OFF)
  {
    return body;
  }
  Trace("cond-var-split-debug")
      << "Conditional var elim split " << body << "?" << std::endl;
  // we only do this splitting if miniscoping is enabled, as this is
  // required to eliminate variables in conjuncts below. We also never
  // miniscope non-standard quantifiers, so this is also guarded here.
  if (!doMiniscopeConj(d_opts) || !qa.isStandard())
  {
    return body;
  }

  bool aggCondSplit = (d_opts.quantifiers.condVarSplitQuant
                       == options::CondVarSplitQuantMode::AGG);
  if (bk == Kind::ITE
      || (bk == Kind::EQUAL && body[0].getType().isBoolean() && aggCondSplit))
  {
    Assert(!qa.isFunDef());
    bool do_split = false;
    unsigned index_max = bk == Kind::ITE ? 0 : 1;
    std::vector<Node> tmpArgs = args;
    for (unsigned index = 0; index <= index_max; index++)
    {
      if (hasVarElim(body[index], true, tmpArgs)
          || hasVarElim(body[index], false, tmpArgs))
      {
        do_split = true;
        break;
      }
    }
    if (do_split)
    {
      Node pos;
      Node neg;
      if (bk == Kind::ITE)
      {
        pos = nm->mkNode(Kind::OR, body[0].negate(), body[1]);
        neg = nm->mkNode(Kind::OR, body[0], body[2]);
      }
      else
      {
        pos = nm->mkNode(Kind::OR, body[0].negate(), body[1]);
        neg = nm->mkNode(Kind::OR, body[0], body[1].negate());
      }
      Trace("cond-var-split-debug") << "*** Split (conditional variable eq) "
                                    << body << " into : " << std::endl;
      Trace("cond-var-split-debug") << "   " << pos << std::endl;
      Trace("cond-var-split-debug") << "   " << neg << std::endl;
      return nm->mkNode(Kind::AND, pos, neg);
    }
  }

  if (bk == Kind::OR)
  {
    unsigned size = body.getNumChildren();
    bool do_split = false;
    unsigned split_index = 0;
    for (unsigned i = 0; i < size; i++)
    {
      // check if this child is a (conditional) variable elimination
      Node b = body[i];
      if (b.getKind() == Kind::AND)
      {
        std::vector<Node> vars;
        std::vector<Node> subs;
        std::vector<Node> tmpArgs = args;
        for (unsigned j = 0, bsize = b.getNumChildren(); j < bsize; j++)
        {
          bool pol = b[j].getKind() == Kind::NOT;
          Node batom = pol ? b[j][0] : b[j];
          if (getVarElimLit(body, batom, pol, tmpArgs, vars, subs))
          {
            Trace("cond-var-split-debug") << "Variable elimination in child #"
                                          << j << " under " << i << std::endl;
            // Figure out if we should split
            // Currently we split if the aggressive option is set, or
            // if the top-level OR is binary.
            if (aggCondSplit || size == 2)
            {
              do_split = true;
            }
            // other splitting criteria go here

            if (do_split)
            {
              split_index = i;
              break;
            }
            vars.clear();
            subs.clear();
            tmpArgs = args;
          }
        }
      }
      if (do_split)
      {
        break;
      }
    }
    if (do_split)
    {
      // For the sake of proofs, if we are not splitting the first child,
      // we first rearrange so that it is first, which can be proven by
      // ACI_NORM.
      std::vector<Node> splitChildren;
      if (split_index != 0)
      {
        splitChildren.push_back(body[split_index]);
        for (size_t i = 0; i < size; i++)
        {
          if (i != split_index)
          {
            splitChildren.push_back(body[i]);
          }
        }
        return nm->mkNode(Kind::OR, splitChildren);
      }
      // This is expected to be proven by the RARE rule bool-or-and-distrib.
      std::vector<Node> children;
      for (TNode bc : body)
      {
        children.push_back(bc);
      }
      for (TNode bci : body[split_index])
      {
        children[split_index] = bci;
        splitChildren.push_back(nm->mkNode(Kind::OR, children));
      }
      // split the AND child, for example:
      //  ( x!=a ^ P(x) ) V Q(x) ---> ( x!=a V Q(x) ) ^ ( P(x) V Q(x) )
      return nm->mkNode(Kind::AND, splitChildren);
    }
  }

  return body;
}

bool QuantifiersRewriter::isVarElim(Node v, Node s)
{
  Assert(v.getKind() == Kind::BOUND_VARIABLE);
  return !expr::hasSubterm(s, v) && s.getType() == v.getType();
}

Node QuantifiersRewriter::getVarElimEq(Node lit,
                                       const std::vector<Node>& args,
                                       Node& var,
                                       CDProof* cdp) const
{
  Assert(lit.getKind() == Kind::EQUAL);
  Node slv;
  TypeNode tt = lit[0].getType();
  if (tt.isRealOrInt())
  {
    slv = getVarElimEqReal(lit, args, var, cdp);
  }
  else if (tt.isBitVector())
  {
    slv = getVarElimEqBv(lit, args, var, cdp);
  }
  else if (tt.isStringLike())
  {
    slv = getVarElimEqString(lit, args, var, cdp);
  }
  return slv;
}

Node QuantifiersRewriter::getVarElimEqReal(Node lit,
                                           const std::vector<Node>& args,
                                           Node& var,
                                           CDProof* cdp) const
{
  // for arithmetic, solve the equality
  std::map<Node, Node> msum;
  if (!ArithMSum::getMonomialSumLit(lit, msum))
  {
    return Node::null();
  }
  std::vector<Node>::const_iterator ita;
  for (std::map<Node, Node>::iterator itm = msum.begin(); itm != msum.end();
       ++itm)
  {
    if (itm->first.isNull())
    {
      continue;
    }
    ita = std::find(args.begin(), args.end(), itm->first);
    if (ita != args.end())
    {
      Node veq_c;
      Node val;
      int ires = ArithMSum::isolate(itm->first, msum, veq_c, val, Kind::EQUAL);
      if (ires != 0 && veq_c.isNull() && isVarElim(itm->first, val))
      {
        var = itm->first;
        if (cdp != nullptr)
        {
          Node eq = var.eqNode(val);
          Node eqslv = lit.eqNode(eq);
          cdp->addTrustedStep(
              eqslv, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
        }
        return val;
      }
    }
  }
  return Node::null();
}

Node QuantifiersRewriter::getVarElimEqBv(Node lit,
                                         const std::vector<Node>& args,
                                         Node& var,
                                         CDProof* cdp) const
{
  if (TraceIsOn("quant-velim-bv"))
  {
    Trace("quant-velim-bv") << "Bv-Elim : " << lit << " varList = { ";
    for (const Node& v : args)
    {
      Trace("quant-velim-bv") << v << " ";
    }
    Trace("quant-velim-bv") << "} ?" << std::endl;
  }
  Assert(lit.getKind() == Kind::EQUAL);
  // TODO (#1494) : linearize the literal using utility

  // if the option varEntEqElimQuant is disabled, we must preserve equivalence
  // when solving the variable, meaning that BITVECTOR_CONCAT cannot be
  // on the path to the variable.
  std::unordered_set<Kind> disallowedKinds;
  if (!d_opts.quantifiers.varEntEqElimQuant)
  {
    // concatenation does not perserve equivalence i.e.
    // (concat x y) = z is not equivalent to x = ((_ extract n m) z)
    disallowedKinds.insert(Kind::BITVECTOR_CONCAT);
  }
  else if (cdp != nullptr)
  {
    // does not support proofs
    return Node::null();
  }

  // compute a subset active_args of the bound variables args that occur in lit
  std::vector<Node> active_args;
  computeArgVec(args, active_args, lit);

  for (const Node& cvar : active_args)
  {
    Node slv = booleans::TheoryBoolRewriter::getBvInvertSolve(
        d_nm, lit, cvar, disallowedKinds);
    if (!slv.isNull())
    {
      // if this is a proper variable elimination, that is, var = slv where
      // var is not in the free variables of slv, then we can return this
      // as the variable elimination for lit.
      if (isVarElim(cvar, slv))
      {
        var = cvar;
        // If we require a proof...
        if (cdp != nullptr)
        {
          Node eq = var.eqNode(slv);
          Node eqslv = lit.eqNode(eq);
          // usually just arith poly norm, e.g. if
          //   (= (bvadd x s) t) = (= x (bvsub t s))
          Rational rx, ry;
          if (arith::PolyNorm::isArithPolyNormRel(lit, eq, rx, ry))
          {
            // will elaborate with BV_POLY_NORM_EQ
            cdp->addTrustedStep(
                eqslv, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
          }
          else
          {
            // Otherwise we add (= (= t s) (= x r)) = true as a step
            // with MACRO_BOOL_BV_INVERT_SOLVE. This ensures that further
            // elaboration can replay the proof, knowing which variable we
            // solved for. This is used if arith poly norm does not suffice,
            // e.g. (= t (bvxor x s)) = (= x (bvxor t s)).
            Node truen = nodeManager()->mkConst(true);
            Node eqslvti = eqslv.eqNode(truen);
            // use trusted step, will elaborate
            cdp->addTrustedStep(
                eqslvti, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
            cdp->addStep(eqslv, ProofRule::TRUE_ELIM, {eqslvti}, {});
          }
        }
        return slv;
      }
    }
  }

  return Node::null();
}

Node QuantifiersRewriter::getVarElimEqString(Node lit,
                                             const std::vector<Node>& args,
                                             Node& var,
                                             CDProof* cdp) const
{
  Assert(lit.getKind() == Kind::EQUAL);
  // The reasoning below involves equality entailment as
  // (= (str.++ s x t) r) entails (= x (str.substr r (str.len s) _)),
  // but these equalities are not equivalent.
  if (!d_opts.quantifiers.varEntEqElimQuant || cdp != nullptr)
  {
    return Node::null();
  }
  NodeManager* nm = nodeManager();
  for (unsigned i = 0; i < 2; i++)
  {
    if (lit[i].getKind() == Kind::STRING_CONCAT)
    {
      TypeNode stype = lit[i].getType();
      for (unsigned j = 0, nchildren = lit[i].getNumChildren(); j < nchildren;
           j++)
      {
        if (std::find(args.begin(), args.end(), lit[i][j]) != args.end())
        {
          var = lit[i][j];
          Node slv = lit[1 - i];
          std::vector<Node> preL(lit[i].begin(), lit[i].begin() + j);
          std::vector<Node> postL(lit[i].begin() + j + 1, lit[i].end());
          Node tpre = strings::utils::mkConcat(preL, stype);
          Node tpost = strings::utils::mkConcat(postL, stype);
          Node slvL = nm->mkNode(Kind::STRING_LENGTH, slv);
          Node tpreL = nm->mkNode(Kind::STRING_LENGTH, tpre);
          Node tpostL = nm->mkNode(Kind::STRING_LENGTH, tpost);
          slv = nm->mkNode(
              Kind::STRING_SUBSTR,
              slv,
              tpreL,
              nm->mkNode(
                  Kind::SUB, slvL, nm->mkNode(Kind::ADD, tpreL, tpostL)));
          // forall x. r ++ x ++ t = s => P( x )
          //   is equivalent to
          // r ++ s' ++ t = s => P( s' ) where
          // s' = substr( s, |r|, |s|-(|t|+|r|) ).
          // We apply this only if r,t,s do not contain free variables.
          if (!expr::hasFreeVar(slv))
          {
            return slv;
          }
        }
      }
    }
  }

  return Node::null();
}

bool QuantifiersRewriter::getVarElimLit(Node body,
                                        Node lit,
                                        bool pol,
                                        std::vector<Node>& args,
                                        std::vector<Node>& vars,
                                        std::vector<Node>& subs,
                                        CDProof* cdp) const
{
  Assert(lit.getKind() != Kind::NOT);
  Trace("var-elim-quant-debug")
      << "Eliminate : " << lit << ", pol = " << pol << "?" << std::endl;
  // all eliminations below guarded by varElimQuant()
  if (!d_opts.quantifiers.varElimQuant)
  {
    return false;
  }

  if (lit.getKind() == Kind::EQUAL)
  {
    if (pol || lit[0].getType().isBoolean())
    {
      // In the loop below, we try solving for *both* sides to
      // maximize the determinism of the rewriter. For example,
      // given 2 Boolean variables x and y, when we construct
      // (not (= (not x) (not y))), the rewriter may order them in
      // either direction. Taking the first solved side leads to
      // nondeterminism based on when (not x) and (not y) are constructed.
      // However, if we compare the variables we will always solve
      // x -> y or vice versa based on when x,y are constructed.
      Node solvedVar;
      Node solvedSubs;
      for (unsigned i = 0; i < 2; i++)
      {
        bool tpol = pol;
        Node v_slv = lit[i];
        if (v_slv.getKind() == Kind::NOT)
        {
          v_slv = v_slv[0];
          tpol = !tpol;
        }
        // don't solve if we solved the opposite side
        // and it was smaller.
        if (!solvedVar.isNull() && v_slv>solvedVar)
        {
          break;
        }
        std::vector<Node>::iterator ita =
            std::find(args.begin(), args.end(), v_slv);
        if (ita != args.end())
        {
          if (isVarElim(v_slv, lit[1 - i]))
          {
            solvedVar = v_slv;
            solvedSubs = lit[1 - i];
            if (!tpol)
            {
              Assert(solvedSubs.getType().isBoolean());
              solvedSubs = solvedSubs.negate();
            }
          }
        }
      }
      if (!solvedVar.isNull())
      {
        if (cdp != nullptr)
        {
          Node eq = solvedVar.eqNode(solvedSubs);
          Node litn = pol ? lit : lit.notNode();
          Node eqslv = litn.eqNode(eq);
          cdp->addTrustedStep(
              eqslv, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
          Trace("var-elim-quant")
              << "...add trusted step " << eqslv << std::endl;
        }
        std::vector<Node>::iterator ita =
            std::find(args.begin(), args.end(), solvedVar);
        Trace("var-elim-quant")
            << "Variable eliminate based on equality : " << solvedVar << " -> "
            << solvedSubs << std::endl;
        vars.push_back(solvedVar);
        subs.push_back(solvedSubs);
        args.erase(ita);
        return true;
      }
    }
  }
  if (lit.getKind() == Kind::BOUND_VARIABLE)
  {
    std::vector< Node >::iterator ita = std::find( args.begin(), args.end(), lit );
    if( ita!=args.end() ){
      Trace("var-elim-bool") << "Variable eliminate : " << lit << std::endl;
      Node c = nodeManager()->mkConst(pol);
      if (cdp != nullptr)
      {
        // x = (x=true) or (not x) = (x = false)
        Node eq = lit.eqNode(c);
        Node litn = pol ? lit : lit.notNode();
        Node eqslv = litn.eqNode(eq);
        cdp->addTrustedStep(
            eqslv, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
      }
      vars.push_back( lit );
      subs.push_back(c);
      args.erase( ita );
      return true;
    }
  }
  if (lit.getKind() == Kind::EQUAL && pol)
  {
    Node var;
    Node slv = getVarElimEq(lit, args, var, cdp);
    if (!slv.isNull())
    {
      Assert(!var.isNull());
      std::vector<Node>::iterator ita =
          std::find(args.begin(), args.end(), var);
      Assert(ita != args.end());
      Trace("var-elim-quant")
          << "Variable eliminate based on theory-specific solving : " << var
          << " -> " << slv << std::endl;
      Assert(!expr::hasSubterm(slv, var));
      Assert(slv.getType() == var.getType());
      vars.push_back(var);
      subs.push_back(slv);
      args.erase(ita);
      return true;
    }
  }
  return false;
}

bool QuantifiersRewriter::getVarElim(Node body,
                                     std::vector<Node>& args,
                                     std::vector<Node>& vars,
                                     std::vector<Node>& subs,
                                     std::vector<Node>& lits,
                                     CDProof* cdp) const
{
  return getVarElimInternal(body, body, false, args, vars, subs, lits, cdp);
}

bool QuantifiersRewriter::getVarElimInternal(Node body,
                                             Node n,
                                             bool pol,
                                             std::vector<Node>& args,
                                             std::vector<Node>& vars,
                                             std::vector<Node>& subs,
                                             std::vector<Node>& lits,
                                             CDProof* cdp) const
{
  Kind nk = n.getKind();
  while (nk == Kind::NOT)
  {
    n = n[0];
    pol = !pol;
    nk = n.getKind();
  }
  if ((nk == Kind::AND && pol) || (nk == Kind::OR && !pol))
  {
    for (const Node& cn : n)
    {
      if (getVarElimInternal(body, cn, pol, args, vars, subs, lits, cdp))
      {
        return true;
      }
    }
    return false;
  }
  if (getVarElimLit(body, n, pol, args, vars, subs, cdp))
  {
    lits.emplace_back(pol ? n : n.notNode());
    return true;
  }
  return false;
}

bool QuantifiersRewriter::hasVarElim(Node n,
                                     bool pol,
                                     std::vector<Node>& args) const
{
  std::vector< Node > vars;
  std::vector< Node > subs;
  std::vector<Node> lits;
  return getVarElimInternal(n, n, pol, args, vars, subs, lits);
}

Node QuantifiersRewriter::getVarElimIneq(Node body,
                                         std::vector<Node>& args,
                                         QAttributes& qa) const
{
  Trace("var-elim-quant-debug") << "getVarElimIneq " << body << std::endl;
  // For each variable v, we compute a set of implied bounds in the body
  // of the quantified formula.
  //   num_bounds[x][-1] stores the entailed lower bounds for x
  //   num_bounds[x][1] stores the entailed upper bounds for x
  //   num_bounds[x][0] stores the entailed disequalities for x
  // These bounds are stored in a map that maps the literal for the bound to
  // its required polarity. For example, for quantified formula
  //   (forall ((x Int)) (or (= x 0) (>= x a)))
  // we have:
  //   num_bounds[x][0] contains { x -> { (= x 0) -> false } }
  //   num_bounds[x][-1] contains { x -> { (>= x a) -> false } }
  // This method succeeds in eliminating x if its only occurrences are in
  // entailed disequalities, and one kind of bound. This is the case for the
  // above quantified formula, which can be rewritten to false. The reason
  // is that we can always chose a value for x that is arbitrarily large (resp.
  // small) to satisfy all disequalities and inequalities for x.
  std::map<Node, std::map<int, std::map<Node, bool>>> num_bounds;
  // The set of variables that we know we can not eliminate
  std::unordered_set<Node> ineligVars;
  // compute the entailed literals
  std::vector<Node> lits;
  if (body.getKind() == Kind::OR)
  {
    lits.insert(lits.begin(), body.begin(), body.end());
  }
  else
  {
    lits.push_back(body);
  }
  for (const Node& l : lits)
  {
    // an inequality that is entailed with a given polarity
    bool pol = l.getKind() == Kind::NOT;
    Node lit = pol ? l[0] : l;
    Trace("var-elim-quant-debug") << "Process inequality bounds : " << lit
                                  << ", pol = " << pol << "..." << std::endl;
    std::map<Node, Node> msum;
    bool canSolve = lit.getKind() == Kind::GEQ
                    || (lit.getKind() == Kind::EQUAL
                        && lit[0].getType().isRealOrInt() && !pol);
    if (!canSolve || !ArithMSum::getMonomialSumLit(lit, msum))
    {
      // not an inequality, or failed to compute, we cannot use this and all
      // variables in it are ineligible.
      expr::getFreeVariables(lit, ineligVars);
      continue;
    }
    for (const std::pair<const Node, Node>& m : msum)
    {
      if (!m.first.isNull() && ineligVars.find(m.first) == ineligVars.end())
      {
        std::vector<Node>::iterator ita =
            std::find(args.begin(), args.end(), m.first);
        if (ita != args.end())
        {
          // store that this literal is upper/lower bound for itm->first
          Node veq_c;
          Node val;
          int ires =
              ArithMSum::isolate(m.first, msum, veq_c, val, lit.getKind());
          if (ires != 0 && veq_c.isNull())
          {
            if (lit.getKind() == Kind::GEQ)
            {
              bool is_upper = pol != (ires == 1);
              Trace("var-elim-ineq-debug")
                  << lit << " is a " << (is_upper ? "upper" : "lower")
                  << " bound for " << m.first << std::endl;
              Trace("var-elim-ineq-debug")
                  << "  pol/ires = " << pol << " " << ires << std::endl;
              num_bounds[m.first][is_upper ? 1 : -1][lit] = pol;
            }
            else
            {
              Trace("var-elim-ineq-debug")
                  << lit << " is a disequality for " << m.first << std::endl;
              num_bounds[m.first][0][lit] = pol;
            }
          }
          else
          {
            Trace("var-elim-ineq-debug")
                << "...ineligible " << m.first
                << " since it cannot be solved for (" << ires << ", " << veq_c
                << ")." << std::endl;
            num_bounds.erase(m.first);
            ineligVars.insert(m.first);
          }
        }
        else
        {
          // compute variables in itm->first, these are not eligible for
          // elimination
          expr::getFreeVariables(m.first, ineligVars);
        }
      }
    }
  }
  if (!qa.d_ipl.isNull())
  {
    // do not eliminate variables that occur in the annotation
    expr::getFreeVariables(qa.d_ipl, ineligVars);
  }
  // collect all variables that have only upper/lower bounds
  std::map<Node, bool> elig_vars;
  // the variable to eliminate
  Node v;
  bool vIsUpper = true;
  for (const std::pair<const Node, std::map<int, std::map<Node, bool>>>& nb :
       num_bounds)
  {
    if (ineligVars.find(nb.first) != ineligVars.end())
    {
      continue;
    }
    if (nb.second.find(1) == nb.second.end())
    {
      Trace("var-elim-ineq-debug")
          << "Variable " << nb.first << " has only lower bounds." << std::endl;
      v = nb.first;
      vIsUpper = false;
      break;
    }
    else if (nb.second.find(-1) == nb.second.end())
    {
      Trace("var-elim-ineq-debug")
          << "Variable " << nb.first << " has only upper bounds." << std::endl;
      v = nb.first;
      vIsUpper = true;
      break;
    }
  }
  if (v.isNull())
  {
    // no eligible variables
    return Node::null();
  }
  NodeManager* nm = nodeManager();
  Trace("var-elim-ineq-debug")
      << v << " is eligible for elimination." << std::endl;
  // Get the literals that corresponded to bounds for the given variable.
  // These can be dropped from the disjunction of the quantified formula,
  // which is justified based on an infinite projection of the eliminated
  // variable.
  std::map<int, std::map<Node, bool>>& nbv = num_bounds[v];
  std::unordered_set<Node> boundLits;
  for (size_t i = 0; i < 2; i++)
  {
    size_t nindex = i == 0 ? (vIsUpper ? 1 : -1) : 0;
    for (const std::pair<const Node, bool>& nb : nbv[nindex])
    {
      Trace("var-elim-ineq-debug")
          << "  subs : " << nb.first << " -> " << nb.second << std::endl;
      boundLits.insert(nb.first);
    }
  }
  // eliminate from args
  std::vector<Node>::iterator ita = std::find(args.begin(), args.end(), v);
  Assert(ita != args.end());
  args.erase(ita);
  // we leave the literals that did not involve the variable we eliminated
  std::vector<Node> remLits;
  for (const Node& l : lits)
  {
    Node atom = l.getKind() == Kind::NOT ? l[0] : l;
    if (boundLits.find(atom) == boundLits.end())
    {
      remLits.push_back(l);
    }
  }
  return nm->mkOr(remLits);
}

Node QuantifiersRewriter::computeVarElimination(Node body,
                                                std::vector<Node>& args,
                                                QAttributes& qa) const
{
  if (!d_opts.quantifiers.varElimQuant && !d_opts.quantifiers.varIneqElimQuant)
  {
    return body;
  }
  Trace("var-elim-quant-debug")
      << "computeVarElimination " << body << std::endl;
  std::vector<Node> vars;
  std::vector<Node> subs;
  // standard variable elimination
  if (d_opts.quantifiers.varElimQuant)
  {
    std::vector<Node> lits;
    getVarElim(body, args, vars, subs, lits);
  }
  // variable elimination based on one-direction inequalities
  if (vars.empty() && d_opts.quantifiers.varIneqElimQuant)
  {
    Node vibBody = getVarElimIneq(body, args, qa);
    if (!vibBody.isNull())
    {
      Trace("var-elim-quant-debug") << "...returns " << vibBody << std::endl;
      return vibBody;
    }
  }
  // if we eliminated a variable, update body and reprocess
  if (!vars.empty())
  {
    Trace("var-elim-quant-debug")
        << "VE " << vars.size() << "/" << args.size() << std::endl;
    Assert(vars.size() == subs.size());
    // remake with eliminated nodes
    body = body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    if (!qa.d_ipl.isNull())
    {
      qa.d_ipl = qa.d_ipl.substitute(
          vars.begin(), vars.end(), subs.begin(), subs.end());
    }
    Trace("var-elim-quant") << "Return " << body << std::endl;
  }
  return body;
}

Node QuantifiersRewriter::computeDtVarExpand(NodeManager* nm,
                                             const Node& q,
                                             size_t& index)
{
  std::vector<Node> lits;
  if (q[1].getKind() == Kind::OR)
  {
    lits.insert(lits.end(), q[1].begin(), q[1].end());
  }
  else
  {
    lits.push_back(q[1]);
  }
  for (const Node& lit : lits)
  {
    if (lit.getKind() == Kind::NOT && lit[0].getKind() == Kind::APPLY_TESTER
        && lit[0][0].getKind() == Kind::BOUND_VARIABLE)
    {
      for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
      {
        if (q[0][i] == lit[0][0])
        {
          index = i;
          // quant dt split for the given variable
          return QuantDSplit::split(nm, q, i);
        }
      }
    }
  }
  return q;
}

Node QuantifiersRewriter::computePrenex(Node q,
                                        Node body,
                                        std::vector<Node>& args,
                                        std::vector<Node>& nargs,
                                        bool pol,
                                        bool prenexAgg) const
{
  NodeManager* nm = nodeManager();
  Kind k = body.getKind();
  if (k == Kind::FORALL)
  {
    if ((pol || prenexAgg)
        && (d_opts.quantifiers.prenexQuantUser
            || !QuantAttributes::hasPattern(body)))
    {
      std::vector< Node > terms;
      std::vector< Node > subs;
      BoundVarManager* bvm = nm->getBoundVarManager();
      std::vector<Node>& argVec = pol ? args : nargs;
      //for doing prenexing of same-signed quantifiers
      //must rename each variable that already exists
      for (const Node& v : body[0])
      {
        terms.push_back(v);
        TypeNode vt = v.getType();
        Node vv;
        if (!q.isNull())
        {
          // We cache based on the original quantified formula, the subformula
          // that we are pulling variables from (body), the variable v and an
          // index ii.
          // The argument body is required since in rare cases, two subformulas
          // may share the same variables. This is the case for define-fun
          // or inferred substitutions that contain quantified formulas.
          // The argument ii is required in case we are prenexing the same
          // subformula multiple times, e.g.
          // forall x. (forall y. P(y) or forall y. P(y)) --->
          // forall x z w. (P(z) or P(w)).
          size_t index = 0;
          do
          {
            Node ii = nm->mkConstInt(index);
            Node cacheVal = nm->mkNode(Kind::SEXPR, {q, body, v, ii});
            vv = bvm->mkBoundVar(BoundVarId::QUANT_REW_PRENEX, cacheVal, vt);
            index++;
          } while (std::find(argVec.begin(), argVec.end(), vv) != argVec.end());
        }
        else
        {
          // not specific to a quantified formula, use normal
          vv = NodeManager::mkBoundVar(vt);
        }
        subs.push_back(vv);
      }
      argVec.insert(argVec.end(), subs.begin(), subs.end());
      Node newBody = body[1];
      newBody = newBody.substitute( terms.begin(), terms.end(), subs.begin(), subs.end() );
      return newBody;
    }
  //must remove structure
  }
  else if (prenexAgg && k == Kind::ITE && body.getType().isBoolean())
  {
    Node nn = nm->mkNode(Kind::AND,
                         nm->mkNode(Kind::OR, body[0].notNode(), body[1]),
                         nm->mkNode(Kind::OR, body[0], body[2]));
    return computePrenex(q, nn, args, nargs, pol, prenexAgg);
  }
  else if (prenexAgg && k == Kind::EQUAL && body[0].getType().isBoolean())
  {
    Node nn = nm->mkNode(Kind::AND,
                         nm->mkNode(Kind::OR, body[0].notNode(), body[1]),
                         nm->mkNode(Kind::OR, body[0], body[1].notNode()));
    return computePrenex(q, nn, args, nargs, pol, prenexAgg);
  }else if( body.getType().isBoolean() ){
    Assert(k != Kind::EXISTS);
    bool childrenChanged = false;
    std::vector< Node > newChildren;
    for (size_t i = 0, nchild = body.getNumChildren(); i < nchild; i++)
    {
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getPolarity( body, i, true, pol, newHasPol, newPol );
      if (!newHasPol)
      {
        newChildren.push_back( body[i] );
        continue;
      }
      Node n = computePrenex(q, body[i], args, nargs, newPol, prenexAgg);
      newChildren.push_back(n);
      childrenChanged = n != body[i] || childrenChanged;
    }
    if( childrenChanged ){
      if (k == Kind::NOT && newChildren[0].getKind() == Kind::NOT)
      {
        return newChildren[0][0];
      }
      return nm->mkNode(k, newChildren);
    }
  }
  return body;
}

Node QuantifiersRewriter::computeSplit(std::vector<Node>& args,
                                       Node body,
                                       QAttributes& qa) const
{
  Assert(body.getKind() == Kind::OR);
  size_t eqc_count = 0;
  size_t eqc_active = 0;
  std::map< Node, int > var_to_eqc;
  std::map< int, std::vector< Node > > eqc_to_var;
  std::map< int, std::vector< Node > > eqc_to_lit;

  std::vector<Node> lits;

  for( unsigned i=0; i<body.getNumChildren(); i++ ){
    //get variables contained in the literal
    Node n = body[i];
    std::vector< Node > lit_args;
    computeArgVec( args, lit_args, n );
    if( lit_args.empty() ){
      lits.push_back( n );
    }else {
      //collect the equivalence classes this literal belongs to, and the new variables it contributes
      std::vector< int > eqcs;
      std::vector< Node > lit_new_args;
      //for each variable in literal
      for( unsigned j=0; j<lit_args.size(); j++) {
        //see if the variable has already been found
        if (var_to_eqc.find(lit_args[j])!=var_to_eqc.end()) {
          int eqc = var_to_eqc[lit_args[j]];
          if (std::find(eqcs.begin(), eqcs.end(), eqc)==eqcs.end()) {
            eqcs.push_back(eqc);
          }
        }else{
          lit_new_args.push_back(lit_args[j]);
        }
      }
      if (eqcs.empty()) {
        eqcs.push_back(eqc_count);
        eqc_count++;
        eqc_active++;
      }

      int eqcz = eqcs[0];
      //merge equivalence classes with eqcz
      for (unsigned j=1; j<eqcs.size(); j++) {
        int eqc = eqcs[j];
        //move all variables from equivalence class
        for (unsigned k=0; k<eqc_to_var[eqc].size(); k++) {
          Node v = eqc_to_var[eqc][k];
          var_to_eqc[v] = eqcz;
          eqc_to_var[eqcz].push_back(v);
        }
        eqc_to_var.erase(eqc);
        //move all literals from equivalence class
        for (unsigned k=0; k<eqc_to_lit[eqc].size(); k++) {
          Node l = eqc_to_lit[eqc][k];
          eqc_to_lit[eqcz].push_back(l);
        }
        eqc_to_lit.erase(eqc);
        eqc_active--;
      }
      //add variables to equivalence class
      for (unsigned j=0; j<lit_new_args.size(); j++) {
        var_to_eqc[lit_new_args[j]] = eqcz;
        eqc_to_var[eqcz].push_back(lit_new_args[j]);
      }
      //add literal to equivalence class
      eqc_to_lit[eqcz].push_back(n);
    }
  }
  if ( eqc_active>1 || !lits.empty() || var_to_eqc.size()!=args.size() ){
    NodeManager* nm = nodeManager();
    if (TraceIsOn("clause-split-debug"))
    {
      Trace("clause-split-debug")
          << "Split quantified formula with body " << body << std::endl;
      Trace("clause-split-debug") << "   Ground literals: " << std::endl;
      for (size_t i = 0; i < lits.size(); i++)
      {
        Trace("clause-split-debug") << "      " << lits[i] << std::endl;
      }
      Trace("clause-split-debug") << std::endl;
      Trace("clause-split-debug") << "Equivalence classes: " << std::endl;
    }
    for (std::map< int, std::vector< Node > >::iterator it = eqc_to_lit.begin(); it != eqc_to_lit.end(); ++it ){
      int eqc = it->first;
      if (TraceIsOn("clause-split-debug"))
      {
        Trace("clause-split-debug") << "   Literals: " << std::endl;
        for (size_t i = 0; i < it->second.size(); i++)
        {
          Trace("clause-split-debug") << "      " << it->second[i] << std::endl;
        }
        Trace("clause-split-debug") << "   Variables: " << std::endl;
        for (size_t i = 0; i < eqc_to_var[eqc].size(); i++)
        {
          Trace("clause-split-debug")
              << "      " << eqc_to_var[eqc][i] << std::endl;
        }
        Trace("clause-split-debug") << std::endl;
      }
      std::vector<Node>& evars = eqc_to_var[eqc];
      // for the sake of proofs, we provide the variables in the order
      // they appear in the original quantified formula
      std::vector<Node> ovars;
      for (const Node& v : args)
      {
        if (std::find(evars.begin(), evars.end(), v) != evars.end())
        {
          ovars.emplace_back(v);
        }
      }
      Node bvl = nodeManager()->mkNode(Kind::BOUND_VAR_LIST, ovars);
      Node bd = it->second.size() == 1 ? it->second[0]
                                       : nm->mkNode(Kind::OR, it->second);
      Node fa = nm->mkNode(Kind::FORALL, bvl, bd);
      lits.push_back(fa);
    }
    Assert(!lits.empty());
    Node nf = nodeManager()->mkOr(lits);
    Trace("clause-split-debug") << "Made node : " << nf << std::endl;
    return nf;
  }
  return Node::null();
}

Node QuantifiersRewriter::mkForAll(const std::vector<Node>& args,
                                   Node body,
                                   QAttributes& qa) const
{
  if (args.empty())
  {
    return body;
  }
  NodeManager* nm = nodeManager();
  std::vector<Node> children;
  children.push_back(nm->mkNode(Kind::BOUND_VAR_LIST, args));
  children.push_back(body);
  if (!qa.d_ipl.isNull())
  {
    children.push_back(qa.d_ipl);
  }
  return nm->mkNode(Kind::FORALL, children);
}

Node QuantifiersRewriter::mkForall(const std::vector<Node>& args,
                                   Node body,
                                   bool marked) const
{
  std::vector< Node > iplc;
  return mkForall( args, body, iplc, marked );
}

Node QuantifiersRewriter::mkForall(const std::vector<Node>& args,
                                   Node body,
                                   std::vector<Node>& iplc,
                                   bool marked) const
{
  if (args.empty())
  {
    return body;
  }
  NodeManager* nm = nodeManager();
  std::vector<Node> children;
  children.push_back(nm->mkNode(Kind::BOUND_VAR_LIST, args));
  children.push_back(body);
  if (marked)
  {
    Node avar = NodeManager::mkDummySkolem("id", nm->booleanType());
    QuantIdNumAttribute ida;
    avar.setAttribute(ida, 0);
    iplc.push_back(nm->mkNode(Kind::INST_ATTRIBUTE, avar));
  }
  if (!iplc.empty())
  {
    children.push_back(nm->mkNode(Kind::INST_PATTERN_LIST, iplc));
  }
  return nm->mkNode(Kind::FORALL, children);
}

//computes miniscoping, also eliminates variables that do not occur free in body
Node QuantifiersRewriter::computeMiniscoping(Node q,
                                             QAttributes& qa,
                                             bool miniscopeConj,
                                             bool miniscopeFv) const
{
  NodeManager* nm = nodeManager();
  std::vector<Node> args(q[0].begin(), q[0].end());
  Node body = q[1];
  Kind k = body.getKind();
  if (k == Kind::AND || k == Kind::ITE)
  {
    bool doRewrite = miniscopeConj;
    if (k == Kind::ITE)
    {
      // ITE miniscoping is only valid if condition contains no variables
      if (expr::hasSubterm(body[0], args))
      {
        doRewrite = false;
      }
    }
    // aggressive miniscoping implies that structural miniscoping should
    // be applied first
    if (doRewrite)
    {
      BoundVarManager* bvm = nm->getBoundVarManager();
      // Break apart the quantifed formula
      // forall x. P1 ^ ... ^ Pn ---> forall x. P1 ^ ... ^ forall x. Pn
      NodeBuilder t(nm, k);
      std::vector<Node> argsc;
      for (size_t i = 0, nchild = body.getNumChildren(); i < nchild; i++)
      {
        if (argsc.empty())
        {
          // If not done so, we must create fresh copy of args. This is to
          // ensure that quantified formulas do not reuse variables.
          for (const Node& v : q[0])
          {
            TypeNode vt = v.getType();
            Node cacheVal = BoundVarManager::getCacheValue(q, v, i);
            Node vv =
                bvm->mkBoundVar(BoundVarId::QUANT_REW_MINISCOPE, cacheVal, vt);
            argsc.push_back(vv);
          }
        }
        Node b = body[i];
        Node bodyc =
            b.substitute(args.begin(), args.end(), argsc.begin(), argsc.end());
        if (b == bodyc)
        {
          // Did not contain variables in args, thus it is ground. Since we did
          // not use them, we keep the variables argsc for the next child.
          t << b;
        }
        else
        {
          // make the miniscoped quantified formula
          Node cbvl = nm->mkNode(Kind::BOUND_VAR_LIST, argsc);
          Node qq = nm->mkNode(Kind::FORALL, cbvl, bodyc);
          t << qq;
          // We used argsc, clear so we will construct a fresh copy above.
          argsc.clear();
        }
      }
      Node retVal = t;
      return retVal;
    }
  }
  else if (body.getKind() == Kind::OR)
  {
    if (miniscopeFv)
    {
      //splitting subsumes free variable miniscoping, apply it with higher priority
      Node ret = computeSplit(args, body, qa);
      if (!ret.isNull())
      {
        return ret;
      }
    }
  }
  else if (body.getKind() == Kind::NOT)
  {
    Assert(isLiteral(body[0]));
  }
  //remove variables that don't occur
  std::vector< Node > activeArgs;
  computeArgVec2( args, activeArgs, body, qa.d_ipl );
  return mkForAll( activeArgs, body, qa );
}

Node QuantifiersRewriter::computeAggressiveMiniscoping(std::vector<Node>& args,
                                                       Node body) const
{
  std::map<Node, std::vector<Node> > varLits;
  std::map<Node, std::vector<Node> > litVars;
  if (body.getKind() == Kind::OR)
  {
    Trace("ag-miniscope") << "compute aggressive miniscoping on " << body << std::endl;
    for (size_t i = 0; i < body.getNumChildren(); i++) {
      std::vector<Node> activeArgs;
      computeArgVec(args, activeArgs, body[i]);
      for (unsigned j = 0; j < activeArgs.size(); j++) {
        varLits[activeArgs[j]].push_back(body[i]);
      }
      std::vector<Node>& lit_body_i = litVars[body[i]];
      std::vector<Node>::iterator lit_body_i_begin = lit_body_i.begin();
      std::vector<Node>::const_iterator active_begin = activeArgs.begin();
      std::vector<Node>::const_iterator active_end = activeArgs.end();
      lit_body_i.insert(lit_body_i_begin, active_begin, active_end);
    }
    //find the variable in the least number of literals
    Node bestVar;
    for( std::map< Node, std::vector<Node> >::iterator it = varLits.begin(); it != varLits.end(); ++it ){
      if( bestVar.isNull() || varLits[bestVar].size()>it->second.size() ){
        bestVar = it->first;
      }
    }
    Trace("ag-miniscope-debug") << "Best variable " << bestVar << " occurs in " << varLits[bestVar].size() << "/ " << body.getNumChildren() << " literals." << std::endl;
    if( !bestVar.isNull() && varLits[bestVar].size()<body.getNumChildren() ){
      //we can miniscope
      Trace("ag-miniscope") << "Miniscope on " << bestVar << std::endl;
      //make the bodies
      std::vector<Node> qlit1;
      qlit1.insert( qlit1.begin(), varLits[bestVar].begin(), varLits[bestVar].end() );
      std::vector<Node> qlitt;
      //for all literals not containing bestVar
      for( size_t i=0; i<body.getNumChildren(); i++ ){
        if( std::find( qlit1.begin(), qlit1.end(), body[i] )==qlit1.end() ){
          qlitt.push_back( body[i] );
        }
      }
      //make the variable lists
      std::vector<Node> qvl1;
      std::vector<Node> qvl2;
      std::vector<Node> qvsh;
      for( unsigned i=0; i<args.size(); i++ ){
        bool found1 = false;
        bool found2 = false;
        for( size_t j=0; j<varLits[args[i]].size(); j++ ){
          if( !found1 && std::find( qlit1.begin(), qlit1.end(), varLits[args[i]][j] )!=qlit1.end() ){
            found1 = true;
          }else if( !found2 && std::find( qlitt.begin(), qlitt.end(), varLits[args[i]][j] )!=qlitt.end() ){
            found2 = true;
          }
          if( found1 && found2 ){
            break;
          }
        }
        if( found1 ){
          if( found2 ){
            qvsh.push_back( args[i] );
          }else{
            qvl1.push_back( args[i] );
          }
        }else{
          Assert(found2);
          qvl2.push_back( args[i] );
        }
      }
      Assert(!qvl1.empty());
      //check for literals that only contain shared variables
      std::vector<Node> qlitsh;
      std::vector<Node> qlit2;
      for( size_t i=0; i<qlitt.size(); i++ ){
        bool hasVar2 = false;
        for( size_t j=0; j<litVars[qlitt[i]].size(); j++ ){
          if( std::find( qvl2.begin(), qvl2.end(), litVars[qlitt[i]][j] )!=qvl2.end() ){
            hasVar2 = true;
            break;
          }
        }
        if( hasVar2 ){
          qlit2.push_back( qlitt[i] );
        }else{
          qlitsh.push_back( qlitt[i] );
        }
      }
      varLits.clear();
      litVars.clear();
      Trace("ag-miniscope-debug") << "Split into literals : " << qlit1.size() << " / " << qlit2.size() << " / " << qlitsh.size();
      Trace("ag-miniscope-debug") << ", variables : " << qvl1.size() << " / " << qvl2.size() << " / " << qvsh.size() << std::endl;
      Node n1 =
          qlit1.size() == 1 ? qlit1[0] : nodeManager()->mkNode(Kind::OR, qlit1);
      n1 = computeAggressiveMiniscoping( qvl1, n1 );
      qlitsh.push_back( n1 );
      if( !qlit2.empty() ){
        Node n2 = qlit2.size() == 1 ? qlit2[0]
                                    : nodeManager()->mkNode(Kind::OR, qlit2);
        n2 = computeAggressiveMiniscoping( qvl2, n2 );
        qlitsh.push_back( n2 );
      }
      Node n = nodeManager()->mkNode(Kind::OR, qlitsh);
      if( !qvsh.empty() ){
        Node bvl = nodeManager()->mkNode(Kind::BOUND_VAR_LIST, qvsh);
        n = nodeManager()->mkNode(Kind::FORALL, bvl, n);
      }
      Trace("ag-miniscope") << "Return " << n << " for " << body << std::endl;
      return n;
    }
  }
  QAttributes qa;
  return mkForAll( args, body, qa );
}

bool QuantifiersRewriter::isStandard(const Node& q, const Options& opts)
{
  QAttributes qa;
  QuantAttributes::computeQuantAttributes(q, qa);
  return isStandard(qa, opts);
}

bool QuantifiersRewriter::isStandard(QAttributes& qa, const Options& opts)
{
  bool is_strict_trigger =
      qa.d_hasPattern
      && opts.quantifiers.userPatternsQuant == options::UserPatMode::STRICT;
  return qa.isStandard() && !is_strict_trigger;
}

Node QuantifiersRewriter::computeRewriteBody(const Node& n,
                                             TConvProofGenerator* pg) const
{
  Assert(n.getKind() == Kind::FORALL);
  QAttributes qa;
  QuantAttributes::computeQuantAttributes(n, qa);
  std::vector<Node> args(n[0].begin(), n[0].end());
  Node body = computeProcessTerms(n, args, n[1], qa, pg);
  if (body != n[1])
  {
    std::vector<Node> children;
    children.push_back(n[0]);
    children.push_back(body);
    if (n.getNumChildren() == 3)
    {
      children.push_back(n[2]);
    }
    return d_nm->mkNode(Kind::FORALL, children);
  }
  return n;
}

bool QuantifiersRewriter::doOperation(Node q,
                                      RewriteStep computeOption,
                                      QAttributes& qa) const
{
  bool is_strict_trigger =
      qa.d_hasPattern
      && d_opts.quantifiers.userPatternsQuant == options::UserPatMode::STRICT;
  bool is_std = isStandard(qa, d_opts);
  if (computeOption == COMPUTE_ELIM_SYMBOLS)
  {
    return true;
  }
  else if (computeOption == COMPUTE_MINISCOPING
           || computeOption == COMPUTE_AGGRESSIVE_MINISCOPING)
  {
    // in the rare case the body is ground, we always eliminate unless it
    // is truly a non-standard quantified formula (e.g. one for QE).
    if (!expr::hasBoundVar(q[1]))
    {
      // This returns true if q is a non-standard quantified formula. Note that
      // is_std is additionally true if user-pat is strict and q has user
      // patterns.
      return qa.isStandard();
    }
    if (!is_std)
    {
      return false;
    }
    // do not miniscope if we have user patterns unless option is set
    if (!d_opts.quantifiers.miniscopeQuantUser && qa.d_hasPattern)
    {
      return false;
    }
    if (computeOption == COMPUTE_AGGRESSIVE_MINISCOPING)
    {
      return d_opts.quantifiers.miniscopeQuant
             == options::MiniscopeQuantMode::AGG;
    }
    return true;
  }
  else if (computeOption == COMPUTE_EXT_REWRITE)
  {
    return d_opts.quantifiers.extRewriteQuant;
  }
  else if (computeOption == COMPUTE_PROCESS_TERMS)
  {
    return true;
  }
  else if (computeOption == COMPUTE_COND_SPLIT)
  {
    return (d_opts.quantifiers.iteDtTesterSplitQuant
            || d_opts.quantifiers.condVarSplitQuant
                   != options::CondVarSplitQuantMode::OFF)
           && !is_strict_trigger;
  }
  else if (computeOption == COMPUTE_PRENEX)
  {
    // do not prenex to pull variables into those with user patterns
    if (!d_opts.quantifiers.prenexQuantUser && qa.d_hasPattern)
    {
      return false;
    }
    if (qa.d_hasPool)
    {
      return false;
    }
    return d_opts.quantifiers.prenexQuant != options::PrenexQuantMode::NONE
           && d_opts.quantifiers.miniscopeQuant
                  != options::MiniscopeQuantMode::AGG
           && is_std;
  }
  else if (computeOption == COMPUTE_VAR_ELIMINATION)
  {
    return d_opts.quantifiers.varElimQuant && is_std && !is_strict_trigger;
  }
  else if (computeOption == COMPUTE_DT_VAR_EXPAND)
  {
    return d_opts.quantifiers.dtVarExpandQuant && is_std && !is_strict_trigger;
  }
  else
  {
    return false;
  }
}

//general method for computing various rewrites
Node QuantifiersRewriter::computeOperation(Node f,
                                           RewriteStep computeOption,
                                           QAttributes& qa) const
{
  Trace("quantifiers-rewrite-debug") << "Compute operation " << computeOption << " on " << f << " " << qa.d_qid_num << std::endl;
  if (computeOption == COMPUTE_MINISCOPING)
  {
    if (d_opts.quantifiers.prenexQuant == options::PrenexQuantMode::NORMAL)
    {
      if( !qa.d_qid_num.isNull() ){
        //already processed this, return self
        return f;
      }
    }
    bool miniscopeConj = doMiniscopeConj(d_opts);
    bool miniscopeFv = doMiniscopeFv(d_opts);
    //return directly
    return computeMiniscoping(f, qa, miniscopeConj, miniscopeFv);
  }
  std::vector<Node> args(f[0].begin(), f[0].end());
  Node n = f[1];
  if (computeOption == COMPUTE_ELIM_SYMBOLS)
  {
    // relies on external utility
    n = booleans::TheoryBoolRewriter::computeNnfNorm(nodeManager(), n);
  }
  else if (computeOption == COMPUTE_AGGRESSIVE_MINISCOPING)
  {
    return computeAggressiveMiniscoping( args, n );
  }
  else if (computeOption == COMPUTE_EXT_REWRITE)
  {
    return computeExtendedRewrite(f, qa);
  }
  else if (computeOption == COMPUTE_PROCESS_TERMS)
  {
    n = computeProcessTerms(f, args, n, qa);
  }
  else if (computeOption == COMPUTE_COND_SPLIT)
  {
    n = computeCondSplit(n, args, qa);
  }
  else if (computeOption == COMPUTE_PRENEX)
  {
    if (d_opts.quantifiers.prenexQuant == options::PrenexQuantMode::NORMAL)
    {
      //will rewrite at preprocess time
      return f;
    }
    else
    {
      std::vector<Node> argsSet, nargsSet;
      n = computePrenex(f, n, argsSet, nargsSet, true, false);
      Assert(nargsSet.empty());
      args.insert(args.end(), argsSet.begin(), argsSet.end());
    }
  }
  else if (computeOption == COMPUTE_VAR_ELIMINATION)
  {
    n = computeVarElimination( n, args, qa );
  }
  else if (computeOption == COMPUTE_DT_VAR_EXPAND)
  {
    size_t index;
    return computeDtVarExpand(nodeManager(), f, index);
  }
  Trace("quantifiers-rewrite-debug") << "Compute Operation: return " << n << ", " << args.size() << std::endl;
  if( f[1]==n && args.size()==f[0].getNumChildren() ){
    return f;
  }else{
    if( args.empty() ){
      return n;
    }else{
      std::vector< Node > children;
      children.push_back(nodeManager()->mkNode(Kind::BOUND_VAR_LIST, args));
      children.push_back( n );
      if( !qa.d_ipl.isNull() && args.size()==f[0].getNumChildren() ){
        children.push_back( qa.d_ipl );
      }
      return nodeManager()->mkNode(Kind::FORALL, children);
    }
  }
}
bool QuantifiersRewriter::doMiniscopeConj(const Options& opts)
{
  options::MiniscopeQuantMode mqm = opts.quantifiers.miniscopeQuant;
  return mqm == options::MiniscopeQuantMode::CONJ_AND_FV
         || mqm == options::MiniscopeQuantMode::CONJ
         || mqm == options::MiniscopeQuantMode::AGG;
}

bool QuantifiersRewriter::doMiniscopeFv(const Options& opts)
{
  options::MiniscopeQuantMode mqm = opts.quantifiers.miniscopeQuant;
  return mqm == options::MiniscopeQuantMode::CONJ_AND_FV
         || mqm == options::MiniscopeQuantMode::FV
         || mqm == options::MiniscopeQuantMode::AGG;
}

bool QuantifiersRewriter::isPrenexNormalForm( Node n ) {
  if (n.getKind() == Kind::FORALL)
  {
    return n[1].getKind() != Kind::FORALL && isPrenexNormalForm(n[1]);
  }
  else if (n.getKind() == Kind::NOT)
  {
    return n[0].getKind() != Kind::NOT && isPrenexNormalForm(n[0]);
  }
  else
  {
    return !expr::hasClosure(n);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
