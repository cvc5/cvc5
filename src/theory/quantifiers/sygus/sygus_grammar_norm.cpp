/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "options/quantifiers_options.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "expr/sygus_grammar.h"
#include "theory/type_enumerator.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusGrammarNorm::SygusGrammarNorm(Env& env) : EnvObj(env) {}

TypeNode SygusGrammarNorm::normalizeSygusType(TypeNode tn, Node sygus_vars)
{
  Assert(tn.isSygusDatatype());
  std::vector<Node> svars;
  if (!sygus_vars.isNull())
  {
    svars.insert(svars.end(), sygus_vars.begin(), sygus_vars.end());
  }
  Trace("sygus-grammar-norm") << "Normalize " << tn.getDType() << std::endl;
  // Make the sygus grammar for the sygus datatype, which makes things easier
  // to operate on.
  SygusGrammar sg(svars, tn);
  const std::vector<Node>& nts = sg.getNtSyms();
  Trace("sygus-grammar-norm") << "Reconstructed grammar " << nts << std::endl;
  bool changed = false;
  std::vector<Node> vars;
  std::vector<Node> subs;
  std::vector<Node> incNtSyms;
  for (const Node& v : nts)
  {
    const std::vector<Node>& rules = sg.getRulesFor(v);
    if (v!=nts[0] && rules.size()==1 && !DTypeConstructor::isSygusAnyConstantOp(rules[0]))
    {
      Node rs = rules[0].substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      for (Node& s : subs)
      {
        TNode tv = v;
        TNode ts = rs;
        s = s.substitute(tv, ts);
      }
      vars.push_back(v);
      subs.push_back(rs);
      continue;
    }
    incNtSyms.push_back(v);
    Trace("sygus-grammar-norm") << "Rules " << v << " " << rules << std::endl;
    for (const Node& r : rules)
    {
      if (DTypeConstructor::isSygusAnyConstantOp(r))
      {
        TypeNode vtn = v.getType();
        Trace("sygus-grammar-norm")
            << "...any constant " << r << " " << vtn << std::endl;
        // if the cardinality is <3, we expand (Constant T) to concrete list.
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
  }
  if (!vars.empty())
  {
    Trace("sygus-grammar-norm") << "Substitution " << vars << " -> " << subs << std::endl;
    SygusGrammar sgu(svars, incNtSyms);
    for (const Node& v : incNtSyms)
    {
      const std::vector<Node>& rules = sg.getRulesFor(v);
      for (const Node& r : rules)
      {
        Node rs = r.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
        sgu.addRule(v, rs);
      }
    }
    return sgu.resolve();
  }
  else if (changed)
  {
    return sg.resolve();
  }
  return tn;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
