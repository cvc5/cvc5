/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of dynamic quantifiers splitting.
 */

#include "theory/quantifiers/quant_split.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "options/quantifiers_options.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QuantDSplit::QuantDSplit(Env& env,
                         QuantifiersState& qs,
                         QuantifiersInferenceManager& qim,
                         QuantifiersRegistry& qr,
                         TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr), d_added_split(userContext())
{
}

void QuantDSplit::checkOwnership(Node q)
{
  // If q is non-standard (marked as sygus, quantifier elimination, etc.), then
  // do no split it.
  QAttributes qa;
  QuantAttributes::computeQuantAttributes(q, qa);
  if (!qa.isStandard())
  {
    return;
  }
  bool takeOwnership = false;
  bool doSplit = false;
  QuantifiersBoundInference& qbi = d_qreg.getQuantifiersBoundInference();
  Trace("quant-dsplit-debug") << "Check split quantified formula : " << q << std::endl;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    TypeNode tn = q[0][i].getType();
    if( tn.isDatatype() ){
      bool isFinite = d_env.isFiniteType(tn);
      const DType& dt = tn.getDType();
      if (dt.isRecursiveSingleton(tn))
      {
        Trace("quant-dsplit-debug") << "Datatype " << dt.getName() << " is recursive singleton." << std::endl;
      }
      else
      {
        if (options().quantifiers.quantDynamicSplit
            == options::QuantDSplitMode::AGG)
        {
          // split if it is a finite datatype
          doSplit = isFinite;
        }
        else if (options().quantifiers.quantDynamicSplit
                 == options::QuantDSplitMode::DEFAULT)
        {
          if (!qbi.isFiniteBound(q, q[0][i]))
          {
            if (isFinite)
            {
              // split if goes from being unhandled -> handled by finite
              // instantiation. An example is datatypes with uninterpreted sort
              // fields which are "interpreted finite" but not "finite".
              doSplit = true;
              // we additionally take ownership of this formula, in other words,
              // we mark it reduced.
              takeOwnership = true;
            }
            else if (dt.getNumConstructors() == 1 && !dt.isCodatatype())
            {
              // split if only one constructor
              doSplit = true;
            }
          }
        }
        if (doSplit)
        {
          // store the index to split
          d_quant_to_reduce[q] = i;
          Trace("quant-dsplit-debug")
              << "Split at index " << i << " based on datatype " << dt.getName()
              << std::endl;
          break;
        }
        Trace("quant-dsplit-debug")
            << "Do not split based on datatype " << dt.getName() << std::endl;
      }
    }
  }

  if (takeOwnership)
  {
    Trace("quant-dsplit-debug") << "Will take ownership." << std::endl;
    d_qreg.setOwner(q, this);
  }
  // Notice we may not take ownership in some cases, meaning that both the
  // original quantified formula and the split one are generated. This may
  // increase our ability to answer "unsat", since quantifier instantiation
  // heuristics may be more effective for one or the other (see issues #993
  // and 3481).
}

/* whether this module needs to check this round */
bool QuantDSplit::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_FULL && !d_quant_to_reduce.empty();
}

bool QuantDSplit::checkCompleteFor( Node q ) {
  // true if we split q
  return d_added_split.find( q )!=d_added_split.end();
}

/* Call during quantifier engine's check */
void QuantDSplit::check(Theory::Effort e, QEffort quant_e)
{
  //add lemmas ASAP (they are a reduction)
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  Trace("quant-dsplit") << "QuantDSplit::check" << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  FirstOrderModel* m = d_treg.getModel();
  std::vector<Node> lemmas;
  for (std::map<Node, int>::iterator it = d_quant_to_reduce.begin();
       it != d_quant_to_reduce.end();
       ++it)
  {
    Node q = it->first;
    Trace("quant-dsplit") << "- Split quantifier " << q << std::endl;
    if (m->isQuantifierAsserted(q) && m->isQuantifierActive(q)
        && d_added_split.find(q) == d_added_split.end())
    {
      d_added_split.insert(q);
      std::vector<Node> bvs;
      for (unsigned i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
      {
        if (static_cast<int>(i) != it->second)
        {
          bvs.push_back(q[0][i]);
        }
      }
      std::vector<Node> disj;
      disj.push_back(q.negate());
      TNode svar = q[0][it->second];
      TypeNode tn = svar.getType();
      Assert(tn.isDatatype());
      std::vector<Node> cons;
      const DType& dt = tn.getDType();
      for (unsigned j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
      {
        std::vector<Node> vars;
        TypeNode dtjtn = dt[j].getInstantiatedConstructorType(tn);
        Assert(dtjtn.getNumChildren() == dt[j].getNumArgs() + 1);
        for (unsigned k = 0, nargs = dt[j].getNumArgs(); k < nargs; k++)
        {
          TypeNode tns = dtjtn[k];
          Node v = nm->mkBoundVar(tns);
          vars.push_back(v);
        }
        std::vector<Node> bvs_cmb;
        bvs_cmb.insert(bvs_cmb.end(), bvs.begin(), bvs.end());
        bvs_cmb.insert(bvs_cmb.end(), vars.begin(), vars.end());
        Node c = datatypes::utils::mkApplyCons(tn, dt, j, vars);
        TNode ct = c;
        Node body = q[1].substitute(svar, ct);
        if (!bvs_cmb.empty())
        {
          Node bvl = nm->mkNode(kind::BOUND_VAR_LIST, bvs_cmb);
          std::vector<Node> children;
          children.push_back(bvl);
          children.push_back(body);
          if (q.getNumChildren() == 3)
          {
            Node ipls = q[2].substitute(svar, ct);
            children.push_back(ipls);
          }
          body = nm->mkNode(kind::FORALL, children);
        }
        cons.push_back(body);
      }
      Node conc = cons.size() == 1 ? cons[0] : nm->mkNode(kind::AND, cons);
      disj.push_back(conc);
      lemmas.push_back(disj.size() == 1 ? disj[0] : nm->mkNode(kind::OR, disj));
    }
  }

  // add lemmas to quantifiers engine
  for (const Node& lem : lemmas)
  {
    Trace("quant-dsplit") << "QuantDSplit lemma : " << lem << std::endl;
    d_qim.addPendingLemma(lem, InferenceId::QUANTIFIERS_DSPLIT);
  }
  Trace("quant-dsplit") << "QuantDSplit::check finished" << std::endl;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
