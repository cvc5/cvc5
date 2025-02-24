/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of class for for simplifying SyGuS grammars after they
 * are encoded into datatypes.
 */

#include "theory/quantifiers/sygus/sygus_grammar_norm.h"

#include "expr/dtype_cons.h"
#include "expr/subs.h"
#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/sygus_grammar_red.h"
#include "theory/trust_substitutions.h"
#include "theory/type_enumerator.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusGrammarNorm::SygusGrammarNorm(Env& env) : EnvObj(env) {}

TypeNode SygusGrammarNorm::normalizeSygusType(TypeNode tn, Node sygusVars)
{
  Assert(tn.isSygusDatatype());
  std::vector<Node> svars;
  if (!sygusVars.isNull())
  {
    svars.insert(svars.end(), sygusVars.begin(), sygusVars.end());
  }
  Trace("sygus-grammar-norm") << "Normalize " << tn.getDType() << std::endl;
  // Make the sygus grammar for the sygus datatype, which makes things easier
  // to operate on.
  SygusGrammar sg(svars, tn);
  return normalizeSygusType(sg);
}
TypeNode SygusGrammarNorm::normalizeSygusType(SygusGrammar sg)
{
  const std::vector<Node>& svars = sg.getSygusVars();
  const std::vector<Node>& nts = sg.getNtSyms();
  Trace("sygus-grammar-norm") << "Reconstructed grammar " << nts << std::endl;
  bool changed = false;
  Subs inlineRules;
  std::vector<Node> incNtSyms;
  SygusGrammarReduce sgr(d_env);
  for (const Node& v : nts)
  {
    const std::vector<Node>& rules = sg.getRulesFor(v);
    Trace("sygus-grammar-norm") << "Rules " << v << " " << rules << std::endl;
    for (const Node& r : rules)
    {
      if (DTypeConstructor::isSygusAnyConstantOp(r))
      {
        TypeNode vtn = v.getType();
        Trace("sygus-grammar-norm")
            << "...any constant " << r << " " << vtn << std::endl;
        // If the cardinality is less than 3, we replace (Constant T) with a
        // concrete list.
        if (vtn.isCardinalityLessThan(3))
        {
          changed = true;
          sg.removeRule(v, r);
          TypeEnumerator te(vtn);
          while (!te.isFinished())
          {
            Node c = *te;
            sg.addRule(v, c);
            ++te;
          }
        }
      }
    }
    // remove the redundant rules if sygusMinGrammar is true
    if (options().quantifiers.sygusMinGrammar)
    {
      sgr.minimize(sg, v);
    }
    if (options().quantifiers.sygusInlineGrammar)
    {
      // now see if there is only one rule, if so, we can inline it
      const std::vector<Node>& rulesPost = sg.getRulesFor(v);
      if (v != nts[0] && rulesPost.size() == 1
          && !DTypeConstructor::isSygusAnyConstantOp(rulesPost[0]))
      {
        Node rs = inlineRules.apply(rulesPost[0]);
        // apply the current to the range
        Subs icurr;
        icurr.add(v, rs);
        icurr.applyToRange(inlineRules);
        inlineRules.add(v, rs);
        // don't include this symbol in the final construction below
        continue;
      }
    }
    incNtSyms.push_back(v);
  }
  TypeNode tnn;
  if (!inlineRules.empty())
  {
    // if we inlined any type, apply the substitution to all rules
    Trace("sygus-grammar-norm") << "Process inlined substitution "
                                << inlineRules.toString() << std::endl;
    SygusGrammar sgu(svars, incNtSyms);
    for (const Node& v : incNtSyms)
    {
      const std::vector<Node>& rules = sg.getRulesFor(v);
      for (const Node& r : rules)
      {
        Node rs = inlineRules.apply(r);
        sgu.addRule(v, rs);
      }
      // reduce again
      if (options().quantifiers.sygusMinGrammar)
      {
        sgr.minimize(sgu, v);
      }
    }
    tnn = sgu.resolve();
  }
  else
  {
    // otherwise recompute the type if we modified
    tnn = sg.resolve();
  }
  return tnn;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
