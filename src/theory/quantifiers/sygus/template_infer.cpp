/*********************                                                        */
/*! \file ce_guided_single_inv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing single invocation synthesis conjectures
 **
 **/
#include "theory/quantifiers/sygus/template_infer.h"

#include "options/quantifiers_options.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void TemplateInfer::initialize(Node q)
{
  // We are processing without single invocation techniques, now check if
  // we should fix an invariant template (post-condition strengthening or
  // pre-condition weakening).
  options::SygusInvTemplMode tmode = options::sygusInvTemplMode();
  if (tmode != options::SygusInvTemplMode::NONE)
  {
    // currently only works for single predicate synthesis
    if (q[0].getNumChildren() > 1 || !q[0][0].getType().isPredicate())
    {
      tmode = options::SygusInvTemplMode::NONE;
    }
    else if (!options::sygusInvTemplWhenSyntax())
    {
      // only use invariant templates if no syntactic restrictions
      if (CegGrammarConstructor::hasSyntaxRestrictions(q))
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
  // if we are doing invariant templates, then construct the template
  Trace("sygus-si") << "- Do transition inference..." << std::endl;
  d_ti[q].process(qq, q[0][0]);
  Trace("cegqi-inv") << std::endl;
  Node prog = d_ti[q].getFunction();
  if (!d_ti[q].isComplete())
  {
    // the invariant could not be inferred
    return;
  }
  Assert(prog == q[0][0]);
  NodeManager* nm = NodeManager::currentNM();
  // map the program back via non-single invocation map
  std::vector<Node> prog_templ_vars;
  d_ti[q].getVariables(prog_templ_vars);
  d_trans_pre[prog] = d_ti[q].getPreCondition();
  d_trans_post[prog] = d_ti[q].getPostCondition();
  Trace("cegqi-inv") << "   precondition : " << d_trans_pre[prog] << std::endl;
  Trace("cegqi-inv") << "  postcondition : " << d_trans_post[prog] << std::endl;

  // construct template
  Node templ;
  if (options::sygusInvAutoUnfold())
  {
    if (d_ti[q].isComplete())
    {
      Trace("cegqi-inv-auto-unfold")
          << "Automatic deterministic unfolding... " << std::endl;
      // auto-unfold
      DetTrace dt;
      int init_dt = d_ti[q].initializeTrace(dt);
      if (init_dt == 0)
      {
        Trace("cegqi-inv-auto-unfold") << "  Init : ";
        dt.print("cegqi-inv-auto-unfold");
        Trace("cegqi-inv-auto-unfold") << std::endl;
        unsigned counter = 0;
        unsigned status = 0;
        while (counter < 100 && status == 0)
        {
          status = d_ti[q].incrementTrace(dt);
          counter++;
          Trace("cegqi-inv-auto-unfold") << "  #" << counter << " : ";
          dt.print("cegqi-inv-auto-unfold");
          Trace("cegqi-inv-auto-unfold")
              << "...status = " << status << std::endl;
        }
        if (status == 1)
        {
          // we have a trivial invariant
          templ = d_ti[q].constructFormulaTrace(dt);
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
  // subsitute the template arguments
  Assert(prog_templ_vars.size() == prog_vars[prog].size());
  templ = templ.substitute(prog_templ_vars.begin(),
                           prog_templ_vars.end(),
                           prog_vars[prog].begin(),
                           prog_vars[prog].end());
  Trace("cegqi-inv") << "       template : " << templ << std::endl;
  d_templ[prog] = templ;
}

Node getTransPre(Node prog) const {
  std::map<Node, Node>::const_iterator location = d_trans_pre.find(prog);
  return location->second;
}

Node getTransPost(Node prog) const {
  std::map<Node, Node>::const_iterator location = d_trans_post.find(prog);
  return location->second;
}
// get template for program prog. This returns a term of the form t[x] where x is the template argument (see below)
Node getTemplate(Node prog) const {
  std::map<Node, Node>::const_iterator tmpl = d_templ.find(prog);
  if( tmpl!=d_templ.end() ){
    return tmpl->second;
  }
  return Node::null();
}
Node getTemplateArg(Node prog) const {
  std::map<Node, Node>::const_iterator tmpla = d_templ_arg.find(prog);
  if( tmpla != d_templ_arg.end() ){
    return tmpla->second;
  }
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
