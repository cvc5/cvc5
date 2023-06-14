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
 * Utility for processing single invocation synthesis conjectures.
 */
#include "theory/quantifiers/sygus/template_infer.h"

#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/sygus/embedding_converter.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/quantifiers/term_util.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusTemplateInfer::SygusTemplateInfer(Env& env) : EnvObj(env), d_ti(env) {}

void SygusTemplateInfer::initialize(Node q)
{
  Assert(d_quant.isNull());
  Assert(q.getKind() == FORALL);
  d_quant = q;
  // We are processing without single invocation techniques, now check if
  // we should fix an invariant template (post-condition strengthening or
  // pre-condition weakening).
  options::SygusInvTemplMode tmode = options().quantifiers.sygusInvTemplMode;
  if (tmode != options::SygusInvTemplMode::NONE)
  {
    // currently only works for single predicate synthesis
    if (q[0].getNumChildren() > 1 || !q[0][0].getType().isPredicate())
    {
      tmode = options::SygusInvTemplMode::NONE;
    }
    else if (!options().quantifiers.sygusInvTemplWhenSyntax)
    {
      // only use invariant templates if no syntactic restrictions
      if (EmbeddingConverter::hasSyntaxRestrictions(q))
      {
        tmode = options::SygusInvTemplMode::NONE;
      }
    }
  }

  if (tmode == options::SygusInvTemplMode::NONE)
  {
    // not processing invariant templates
    return;
  }

  Node qq;
  if (q[1].getKind() == NOT && q[1][0].getKind() == FORALL)
  {
    qq = q[1][0][1];
  }
  else
  {
    qq = TermUtil::simpleNegate(q[1]);
  }
  if (qq.isConst())
  {
    // trivial, do not use transition inference
    return;
  }

  // if we are doing invariant templates, then construct the template
  Trace("sygus-si") << "- Do transition inference..." << std::endl;
  d_ti.process(qq, q[0][0]);
  Trace("cegqi-inv") << std::endl;
  Node prog = d_ti.getFunction();
  if (!d_ti.isComplete())
  {
    // the invariant could not be inferred
    return;
  }
  Assert(prog == q[0][0]);
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  // map the program back via non-single invocation map
  std::vector<Node> prog_templ_vars;
  d_ti.getVariables(prog_templ_vars);
  d_trans_pre[prog] = d_ti.getPreCondition();
  d_trans_post[prog] = d_ti.getPostCondition();
  Trace("cegqi-inv") << "   precondition : " << d_trans_pre[prog] << std::endl;
  Trace("cegqi-inv") << "  postcondition : " << d_trans_post[prog] << std::endl;

  // construct template argument
  TypeNode atn = prog.getType();
  if (atn.isFunction())
  {
    atn = atn.getRangeType();
  }
  d_templ_arg[prog] = sm->mkDummySkolem("I", atn);

  // construct template
  Node templ;
  if (options().quantifiers.sygusInvAutoUnfold)
  {
    if (d_ti.isComplete())
    {
      Trace("cegqi-inv-auto-unfold")
          << "Automatic deterministic unfolding... " << std::endl;
      // auto-unfold
      DetTrace dt;
      int init_dt = d_ti.initializeTrace(dt);
      if (init_dt == 0)
      {
        Trace("cegqi-inv-auto-unfold") << "  Init : ";
        dt.print("cegqi-inv-auto-unfold");
        Trace("cegqi-inv-auto-unfold") << std::endl;
        unsigned counter = 0;
        unsigned status = 0;
        while (counter < 100 && status == 0)
        {
          status = d_ti.incrementTrace(dt);
          counter++;
          Trace("cegqi-inv-auto-unfold") << "  #" << counter << " : ";
          dt.print("cegqi-inv-auto-unfold");
          Trace("cegqi-inv-auto-unfold")
              << "...status = " << status << std::endl;
        }
        if (status == 1)
        {
          // we have a trivial invariant
          templ = d_ti.constructFormulaTrace(dt);
          Trace("cegqi-inv") << "By finite deterministic terminating trace, a "
                                "solution invariant is : "
                             << std::endl;
          Trace("cegqi-inv") << "   " << templ << std::endl;
          // this should be unnecessary
          templ = nm->mkNode(AND, templ, d_templ_arg[prog]);
        }
      }
      else
      {
        Trace("cegqi-inv-auto-unfold") << "...failed initialize." << std::endl;
      }
    }
  }
  Trace("cegqi-inv") << "Make the template... " << tmode << " " << templ
                     << std::endl;
  if (templ.isNull())
  {
    if (tmode == options::SygusInvTemplMode::PRE)
    {
      templ = nm->mkNode(OR, d_trans_pre[prog], d_templ_arg[prog]);
    }
    else
    {
      Assert(tmode == options::SygusInvTemplMode::POST);
      templ = nm->mkNode(AND, d_trans_post[prog], d_templ_arg[prog]);
    }
  }
  Trace("cegqi-inv") << "       template (pre-substitution) : " << templ
                     << std::endl;
  Assert(!templ.isNull());

  // get the variables
  Node sfvl = SygusUtils::getOrMkSygusArgumentList(prog);
  if (!sfvl.isNull())
  {
    std::vector<Node> prog_vars(sfvl.begin(), sfvl.end());
    // subsitute the template arguments
    Trace("cegqi-inv") << "vars : " << prog_templ_vars << " " << prog_vars
                       << std::endl;
    Assert(prog_templ_vars.size() == prog_vars.size());
    templ = templ.substitute(prog_templ_vars.begin(),
                             prog_templ_vars.end(),
                             prog_vars.begin(),
                             prog_vars.end());
  }
  Trace("cegqi-inv") << "       template : " << templ << std::endl;
  d_templ[prog] = templ;
}

Node SygusTemplateInfer::getTemplate(Node prog) const
{
  std::map<Node, Node>::const_iterator tmpl = d_templ.find(prog);
  if (tmpl != d_templ.end())
  {
    return tmpl->second;
  }
  return Node::null();
}

Node SygusTemplateInfer::getTemplateArg(Node prog) const
{
  std::map<Node, Node>::const_iterator tmpla = d_templ_arg.find(prog);
  if (tmpla != d_templ_arg.end())
  {
    return tmpla->second;
  }
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
