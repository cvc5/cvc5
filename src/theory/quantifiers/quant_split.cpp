/*********************                                                        */
/*! \file quant_split.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of dynamic quantifiers splitting
 **/

#include "theory/quantifiers/quant_split.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/first_order_model.h"
#include "options/quantifiers_options.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;


QuantDSplit::QuantDSplit( QuantifiersEngine * qe, context::Context* c ) :
QuantifiersModule( qe ), d_added_split( qe->getUserContext() ){

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
  Trace("quant-dsplit-debug") << "Check split quantified formula : " << q << std::endl;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    TypeNode tn = q[0][i].getType();
    if( tn.isDatatype() ){
      const DType& dt = tn.getDType();
      if (dt.isRecursiveSingleton(tn))
      {
        Trace("quant-dsplit-debug") << "Datatype " << dt.getName() << " is recursive singleton." << std::endl;
      }
      else
      {
        if (options::quantDynamicSplit() == options::QuantDSplitMode::AGG)
        {
          // split if it is a finite datatype
          doSplit = dt.isInterpretedFinite(tn);
        }
        else if (options::quantDynamicSplit()
                 == options::QuantDSplitMode::DEFAULT)
        {
          if (!d_quantEngine->isFiniteBound(q, q[0][i]))
          {
            if (dt.isInterpretedFinite(tn))
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
    d_quantEngine->setOwner( q, this );
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
  NodeManager* nm = NodeManager::currentNM();
  FirstOrderModel* m = d_quantEngine->getModel();
  std::vector<Node> lemmas;
  for (std::map<Node, int>::iterator it = d_quant_to_reduce.begin();
       it != d_quant_to_reduce.end();
       ++it)
  {
    Node q = it->first;
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
        for (unsigned k = 0, nargs = dt[j].getNumArgs(); k < nargs; k++)
        {
          TypeNode tns = dt[j][k].getRangeType();
          Node v = nm->mkBoundVar(tns);
          vars.push_back(v);
        }
        std::vector<Node> bvs_cmb;
        bvs_cmb.insert(bvs_cmb.end(), bvs.begin(), bvs.end());
        bvs_cmb.insert(bvs_cmb.end(), vars.begin(), vars.end());
        vars.insert(vars.begin(), dt[j].getConstructor());
        Node c = nm->mkNode(kind::APPLY_CONSTRUCTOR, vars);
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
    d_quantEngine->addLemma(lem, false);
  }
}

