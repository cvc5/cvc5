/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of variable match generator class.
 */
#include "theory/quantifiers/ematching/var_match_generator.h"

#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace inst {

VarMatchGeneratorTermSubs::VarMatchGeneratorTermSubs(Trigger* tparent,
                                                     Node var,
                                                     Node subs)
    : InstMatchGenerator(tparent, Node::null()),
      d_var(var),
      d_subs(subs),
      d_rm_prev(false)
{
  d_children_types.push_back(d_var.getAttribute(InstVarNumAttribute()));
  d_var_type = d_var.getType();
}

bool VarMatchGeneratorTermSubs::reset(Node eqc)
{
  d_eq_class = eqc;
  return true;
}

int VarMatchGeneratorTermSubs::getNextMatch(Node q, InstMatch& m)
{
  int ret_val = -1;
  if (!d_eq_class.isNull())
  {
    Trace("var-trigger-matching") << "Matching " << d_eq_class << " against "
                                  << d_var << " in " << d_subs << std::endl;
    TNode tvar = d_var;
    Node s = d_subs.substitute(tvar, d_eq_class);
    s = Rewriter::rewrite(s);
    Trace("var-trigger-matching")
        << "...got " << s << ", " << s.getKind() << std::endl;
    d_eq_class = Node::null();
    // if( s.getType().isSubtypeOf( d_var_type ) ){
    d_rm_prev = m.get(d_children_types[0]).isNull();
    if (!m.set(d_qstate, d_children_types[0], s))
    {
      return -1;
    }
    else
    {
      ret_val = continueNextMatch(
          q, m, InferenceId::QUANTIFIERS_INST_E_MATCHING_VAR_GEN);
      if (ret_val > 0)
      {
        return ret_val;
      }
    }
  }
  if (d_rm_prev)
  {
    m.d_vals[d_children_types[0]] = Node::null();
    d_rm_prev = false;
  }
  return -1;
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
