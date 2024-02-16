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
#include "expr/sygus_grammar.h"
#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/trust_substitutions.h"
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
    // now see if there is only one rule, if so, we can inline it
    const std::vector<Node>& rulesPost = sg.getRulesFor(v);
    if (v != nts[0] && rulesPost.size() == 1
        && !DTypeConstructor::isSygusAnyConstantOp(rulesPost[0]))
    {
      Node rs = rulesPost[0].substitute(
          vars.begin(), vars.end(), subs.begin(), subs.end());
      for (Node& s : subs)
      {
        TNode tv = v;
        TNode ts = rs;
        s = s.substitute(tv, ts);
      }
      vars.push_back(v);
      subs.push_back(rs);
      // don't include this symbol in the final construction below
      continue;
    }
    incNtSyms.push_back(v);
  }
  TypeNode tnn;
  if (!vars.empty())
  {
    // if we inlined any type
    Trace("sygus-grammar-norm") << "Process inlined substitution " << vars
                                << " -> " << subs << std::endl;
    SygusGrammar sgu(svars, incNtSyms);
    for (const Node& v : incNtSyms)
    {
      const std::vector<Node>& rules = sg.getRulesFor(v);
      for (const Node& r : rules)
      {
        Node rs =
            r.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
        sgu.addRule(v, rs);
      }
    }
    tnn = sgu.resolve();
  }
  else if (changed)
  {
    // otherwise if we modified
    tnn = sg.resolve();
  }
  else
  {
    // no change, just return original
    return tn;
  }
  // ensure the expanded definition forms are set
  std::unordered_set<TypeNode> processed;
  std::vector<TypeNode> toProcess;
  toProcess.push_back(tnn);
  size_t index = 0;
  while (index < toProcess.size())
  {
    TypeNode tnp = toProcess[index];
    index++;
    Assert(tnp.isSygusDatatype());
    const DType& dt = tnp.getDType();
    const std::vector<std::shared_ptr<DTypeConstructor>>& cons =
        dt.getConstructors();
    for (const std::shared_ptr<DTypeConstructor>& c : cons)
    {
      Node op = c->getSygusOp();
      Node eop = d_env.getTopLevelSubstitutions().apply(op);
      eop = rewrite(eop);
      datatypes::utils::setExpandedDefinitionForm(op, eop);
      // also must consider the arguments
      for (size_t j = 0, nargs = c->getNumArgs(); j < nargs; ++j)
      {
        TypeNode tnc = c->getArgType(j);
        if (tnc.isSygusDatatype() && processed.find(tnc) == processed.end())
        {
          toProcess.push_back(tnc);
          processed.insert(tnc);
        }
      }
    }
  }
  return tnn;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
