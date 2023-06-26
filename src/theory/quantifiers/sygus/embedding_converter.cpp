/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for applying the deep embedding for SyGuS
 */

#include "theory/quantifiers/sygus/embedding_converter.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/smt2/smt2_printer.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons_new.h"
#include "theory/quantifiers/sygus/sygus_grammar_norm.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EmbeddingConverter::EmbeddingConverter(Env& env,
                                       TermDbSygus* tds,
                                       SynthConjecture* p)
    : EnvObj(env), d_tds(tds), d_parent(p), d_is_syntax_restricted(false)
{
}

bool EmbeddingConverter::hasSyntaxRestrictions(Node q)
{
  Assert(q.getKind() == FORALL);
  for (const Node& f : q[0])
  {
    TypeNode tn = SygusUtils::getSygusType(f);
    if (tn.isDatatype() && tn.getDType().isSygus())
    {
      return true;
    }
  }
  return false;
}

void EmbeddingConverter::collectTerms(
    Node n, std::map<TypeNode, std::unordered_set<Node>>& consts)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, bool> visited;
  std::unordered_map<TNode, bool>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = true;
      // is this a constant?
      if (cur.isConst())
      {
        TypeNode tn = cur.getType();
        Node c = cur;
        if (tn.isRealOrInt())
        {
          c = nm->mkConstRealOrInt(tn, c.getConst<Rational>().abs());
        }
        consts[tn].insert(c);
        if (tn.isInteger())
        {
          c = nm->mkConstReal(c.getConst<Rational>().abs());
          TypeNode rtype = nm->realType();
          consts[rtype].insert(c);
        }
      }
      // recurse
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

Node EmbeddingConverter::process(Node q,
                                 const std::map<Node, Node>& templates,
                                 const std::map<Node, Node>& templates_arg)
{
  // convert to deep embedding and finalize single invocation here
  // now, construct the grammar
  Trace("cegqi") << "SynthConjecture : convert to deep embedding..."
                 << std::endl;
  std::map<TypeNode, std::unordered_set<Node>> extra_cons;
  if (options().quantifiers.sygusAddConstGrammar
      && options().quantifiers.sygusGrammarConsMode
             == options::SygusGrammarConsMode::SIMPLE)
  {
    Trace("cegqi") << "SynthConjecture : collect constants..." << std::endl;
    collectTerms(q[1], extra_cons);
  }
  std::map<TypeNode, std::unordered_set<Node>> exc_cons;
  std::map<TypeNode, std::unordered_set<Node>> inc_cons;

  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> ebvl;
  for (unsigned i = 0; i < q[0].getNumChildren(); i++)
  {
    Node sf = q[0][i];
    // if non-null, v encodes the syntactic restrictions (via an inductive
    // datatype) on sf from the input.
    TypeNode preGrammarType = SygusUtils::getSygusType(sf);
    if (preGrammarType.isNull())
    {
      // otherwise, the grammar is the default for the range of the function
      preGrammarType = sf.getType();
      if (preGrammarType.isFunction())
      {
        preGrammarType = preGrammarType.getRangeType();
      }
    }

    // the actual sygus datatype we will use (normalized below)
    TypeNode tn;
    Node sfvl;
    if (preGrammarType.isDatatype() && preGrammarType.getDType().isSygus())
    {
      sfvl = preGrammarType.getDType().getSygusVarList();
      tn = preGrammarType;
      // normalize type, if user-provided
      SygusGrammarNorm sygus_norm(d_env, d_tds);
      tn = sygus_norm.normalizeSygusType(tn, sfvl);
    }
    else
    {
      sfvl = SygusUtils::getOrMkSygusArgumentList(sf);
      // check which arguments are irrelevant
      std::unordered_set<unsigned> arg_irrelevant;
      d_parent->getProcess()->getIrrelevantArgs(sf, arg_irrelevant);
      std::vector<Node> trules;
      // add the variables from the free variable list that we did not
      // infer were irrelevant.
      for (size_t j = 0, nargs = sfvl.getNumChildren(); j < nargs; j++)
      {
        if (arg_irrelevant.find(j) == arg_irrelevant.end())
        {
          trules.push_back(sfvl[j]);
        }
      }
      // add the constants computed avove
      for (const std::pair<const TypeNode, std::unordered_set<Node>>& c :
           extra_cons)
      {
        trules.insert(trules.end(), c.second.begin(), c.second.end());
      }
      tn = SygusGrammarCons::mkDefaultSygusType(
          options(), preGrammarType, sfvl, trules);
    }
    // print the grammar
    if (isOutputOn(OutputTag::SYGUS_GRAMMAR))
    {
      output(OutputTag::SYGUS_GRAMMAR)
          << "(sygus-grammar " << sf
          << printer::smt2::Smt2Printer::sygusGrammarString(tn) << ")"
          << std::endl;
    }
    // sfvl may be null for constant synthesis functions
    Trace("cegqi-debug") << "...sygus var list associated with " << sf << " is "
                         << sfvl << std::endl;

    std::map<Node, Node>::const_iterator itt = templates.find(sf);
    if (itt != templates.end())
    {
      Node templ = itt->second;
      std::map<Node, Node>::const_iterator itta = templates_arg.find(sf);
      Assert(itta != templates_arg.end());
      TNode templ_arg = itta->second;
      Assert(!templ_arg.isNull());
    }

    // ev is the first-order variable corresponding to this synth fun
    Node ev = nm->mkBoundVar("f" + sf.getName(), tn);
    ebvl.push_back(ev);
    Trace("cegqi") << "...embedding synth fun : " << sf << " -> " << ev
                   << std::endl;
  }
  return process(q, templates, templates_arg, ebvl);
}

Node EmbeddingConverter::process(Node q,
                                 const std::map<Node, Node>& templates,
                                 const std::map<Node, Node>& templates_arg,
                                 const std::vector<Node>& ebvl)
{
  Assert(q[0].getNumChildren() == ebvl.size());
  Assert(d_synth_fun_vars.empty());

  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> qchildren;
  Node qbody_subs = q[1];
  for (unsigned i = 0, size = q[0].getNumChildren(); i < size; i++)
  {
    Node sf = q[0][i];
    d_synth_fun_vars[sf] = ebvl[i];
    Node sfvl = SygusUtils::getOrMkSygusArgumentList(sf);
    TypeNode tn = ebvl[i].getType();
    // check if there is a template
    std::map<Node, Node>::const_iterator itt = templates.find(sf);
    if (itt != templates.end())
    {
      Node templ = itt->second;
      std::map<Node, Node>::const_iterator itta = templates_arg.find(sf);
      Assert(itta != templates_arg.end());
      TNode templ_arg = itta->second;
      Assert(!templ_arg.isNull());
      // if there is a template for this argument, make a sygus type on top of
      // it
      // otherwise, apply it as a preprocessing pass
      Trace("cegqi-debug") << "Template for " << sf << " is : " << templ
                           << " with arg " << templ_arg << std::endl;
      Trace("cegqi-debug")
          << "  apply this template as a substituion during preprocess..."
          << std::endl;
      std::vector<Node> schildren;
      std::vector<Node> largs;
      for (unsigned j = 0; j < sfvl.getNumChildren(); j++)
      {
        schildren.push_back(sfvl[j]);
        largs.push_back(nm->mkBoundVar(sfvl[j].getType()));
      }
      std::vector<Node> subsfn_children;
      subsfn_children.push_back(sf);
      subsfn_children.insert(
          subsfn_children.end(), schildren.begin(), schildren.end());
      Node subsfn = nm->mkNode(kind::APPLY_UF, subsfn_children);
      TNode subsf = subsfn;
      Trace("cegqi-debug") << "  substitute arg : " << templ_arg << " -> "
                           << subsf << std::endl;
      templ = templ.substitute(templ_arg, subsf);
      // substitute lambda arguments
      templ = templ.substitute(
          schildren.begin(), schildren.end(), largs.begin(), largs.end());
      Node subsn =
          nm->mkNode(kind::LAMBDA, nm->mkNode(BOUND_VAR_LIST, largs), templ);
      TNode var = sf;
      TNode subs = subsn;
      Trace("cegqi-debug") << "  substitute : " << var << " -> " << subs
                           << std::endl;
      qbody_subs = qbody_subs.substitute(var, subs);
      Trace("cegqi-debug") << "  body is now : " << qbody_subs << std::endl;
    }
    d_tds->registerSygusType(tn);
    Assert(tn.isDatatype());
    const DType& dt = tn.getDType();
    Assert(dt.isSygus());
    if (!dt.getSygusAllowAll())
    {
      d_is_syntax_restricted = true;
    }
  }
  qchildren.push_back(nm->mkNode(kind::BOUND_VAR_LIST, ebvl));
  if (qbody_subs != q[1])
  {
    Trace("cegqi") << "...rewriting : " << qbody_subs << std::endl;
    qbody_subs = rewrite(qbody_subs);
    Trace("cegqi") << "...got : " << qbody_subs << std::endl;
  }
  qchildren.push_back(convertToEmbedding(qbody_subs));
  if (q.getNumChildren() == 3)
  {
    qchildren.push_back(q[2]);
  }
  return nm->mkNode(kind::FORALL, qchildren);
}

Node EmbeddingConverter::convertToEmbedding(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      Kind ret_k = cur.getKind();
      Node op;
      bool childChanged = false;
      std::vector<Node> children;
      // get the potential operator
      if (cur.getNumChildren() > 0)
      {
        if (cur.getKind() == kind::APPLY_UF)
        {
          op = cur.getOperator();
        }
      }
      else
      {
        op = cur;
      }
      // is the operator a synth function?
      bool makeEvalFun = false;
      if (!op.isNull())
      {
        std::map<Node, Node>::iterator its = d_synth_fun_vars.find(op);
        if (its != d_synth_fun_vars.end())
        {
          children.push_back(its->second);
          makeEvalFun = true;
        }
      }
      if (!makeEvalFun)
      {
        // otherwise, we apply the previous operator
        if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          children.push_back(cur.getOperator());
        }
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++)
      {
        it = visited.find(cur[i]);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur[i] != it->second;
        children.push_back(it->second);
      }
      if (makeEvalFun)
      {
        if (!cur.getType().isFunction())
        {
          // will make into an application of an evaluation function
          ret = nm->mkNode(DT_SYGUS_EVAL, children);
        }
        else
        {
          Assert(children.size() == 1);
          Node ef = children[0];
          // Otherwise, we are using the function-to-synthesize itself in a
          // higher-order setting. We must return the lambda term:
          //   lambda x1...xn. (DT_SYGUS_EVAL ef x1 ... xn)
          // where ef is the first order variable for the
          // function-to-synthesize.
          SygusTypeInfo& ti = d_tds->getTypeInfo(ef.getType());
          const std::vector<Node>& vars = ti.getVarList();
          Assert(!vars.empty());
          std::vector<Node> vs;
          for (const Node& v : vars)
          {
            vs.push_back(nm->mkBoundVar(v.getType()));
          }
          Node lvl = nm->mkNode(BOUND_VAR_LIST, vs);
          std::vector<Node> eargs;
          eargs.push_back(ef);
          eargs.insert(eargs.end(), vs.begin(), vs.end());
          ret = nm->mkNode(LAMBDA, lvl, nm->mkNode(DT_SYGUS_EVAL, eargs));
        }
      }
      else if (childChanged)
      {
        ret = nm->mkNode(ret_k, children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
