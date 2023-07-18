/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A technique for synthesizing candidate rewrites of the form t1 = t2,
 * where t1 and t2 are subterms of the input.
 */

#include "preprocessing/passes/synth_rew_rules.h"

#include <sstream>

#include "expr/term_canonize.h"
#include "options/base_options.h"
#include "options/datatypes_options.h"
#include "options/quantifiers_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "printer/printer.h"
#include "printer/smt2/smt2_printer.h"
#include "smt/set_defaults.h"
#include "theory/quantifiers/candidate_rewrite_database.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons_new.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/quantifiers/term_util.h"
#include "theory/smt_engine_subsolver.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

SynthRewRulesPass::SynthRewRulesPass(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "synth-rr"){};

PreprocessingPassResult SynthRewRulesPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  return PreprocessingPassResult::NO_CONFLICT;
}

std::vector<TypeNode> SynthRewRulesPass::getGrammarsFrom(
    const std::vector<Node>& assertions, uint64_t nvars)
{
  std::vector<TypeNode> ret;
  std::map<TypeNode, TypeNode> tlGrammarTypes =
      constructTopLevelGrammar(assertions, nvars);
  for (std::pair<const TypeNode, TypeNode> ttp : tlGrammarTypes)
  {
    ret.push_back(ttp.second);
  }
  return ret;
}

std::map<TypeNode, TypeNode> SynthRewRulesPass::constructTopLevelGrammar(
    const std::vector<Node>& assertions, uint64_t nvars)
{
  std::map<TypeNode, TypeNode> tlGrammarTypes;
  if (assertions.empty())
  {
    return tlGrammarTypes;
  }
  NodeManager* nm = NodeManager::currentNM();
  // initialize the candidate rewrite
  std::unordered_map<TNode, bool> visited;
  std::unordered_map<TNode, bool>::iterator it;
  std::vector<TNode> visit;
  // Get all usable terms from the input. A term is usable if it does not
  // contain a quantified subterm
  std::vector<Node> terms;
  // all variables (free constants) appearing in the input
  std::vector<Node> vars;
  // does the input contain a Boolean variable?
  bool hasBoolVar = false;
  // the types of subterms of our input
  std::map<TypeNode, bool> typesFound;
  // standard constants for each type (e.g. true, false for Bool)
  std::map<TypeNode, std::vector<Node> > consts;

  TNode cur;
  Trace("srs-input") << "Collect terms in assertions..." << std::endl;
  for (const Node& a : assertions)
  {
    Trace("srs-input-debug") << "Assertion : " << a << std::endl;
    visit.push_back(a);
    do
    {
      cur = visit.back();
      visit.pop_back();
      // we recurse on this node if it is not a quantified formula
      if (cur.isClosure())
      {
        visited[cur] = false;
        continue;
      }
      it = visited.find(cur);
      if (it == visited.end())
      {
        Trace("srs-input-debug") << "...preprocess " << cur << std::endl;
        visited[cur] = false;
        visit.push_back(cur);
        for (const Node& cc : cur)
        {
          visit.push_back(cc);
        }
      }
      else if (!it->second)
      {
        Trace("srs-input-debug") << "...postprocess " << cur << std::endl;
        // check if all of the children are valid
        // this ensures we do not register terms that have e.g. quantified
        // formulas as subterms
        bool childrenValid = true;
        for (const Node& cc : cur)
        {
          Assert(visited.find(cc) != visited.end());
          if (!visited[cc])
          {
            childrenValid = false;
          }
        }
        if (childrenValid)
        {
          Trace("srs-input-debug") << "...children are valid" << std::endl;
          Trace("srs-input-debug") << "Add term " << cur << std::endl;
          TypeNode tn = cur.getType();
          if (cur.isVar())
          {
            vars.push_back(cur);
            if (tn.isBoolean())
            {
              hasBoolVar = true;
            }
          }
          // register type information
          if (typesFound.find(tn) == typesFound.end())
          {
            typesFound[tn] = true;
            // add the standard constants for this type
            theory::quantifiers::SygusGrammarCons::mkSygusConstantsForType(
                tn, consts[tn]);
            // We prepend them so that they come first in the grammar
            // construction. The motivation is we'd prefer seeing e.g. "true"
            // instead of (= x x) as a canonical term.
            terms.insert(terms.begin(), consts[tn].begin(), consts[tn].end());
          }
          terms.push_back(cur);
        }
        visited[cur] = childrenValid;
      }
    } while (!visit.empty());
  }
  Trace("srs-input") << "...finished." << std::endl;

  Trace("srs-input") << "Make synth variables for types..." << std::endl;
  // We will generate a fixed number of variables per type. These are the
  // variables that appear as free variables in the rewrites we generate.
  // must have at least one variable per type
  nvars = nvars < 1 ? 1 : nvars;
  std::map<TypeNode, std::vector<Node> > tvars;
  std::vector<Node> allVars;
  uint64_t varCounter = 0;
  for (std::pair<const TypeNode, bool> tfp : typesFound)
  {
    TypeNode tn = tfp.first;
    // we do not allocate variables for non-first class types, e.g. regular
    // expressions
    if (!tn.isFirstClass())
    {
      continue;
    }
    // If we are not interested in purely propositional rewrites, we only
    // need to make one Boolean variable if the input has a Boolean variable.
    // This ensures that no type in our grammar has zero constructors. If
    // our input does not contain a Boolean variable, we need not allocate any
    // Boolean variables here.
    uint64_t useNVars = !tn.isBoolean() ? nvars : (hasBoolVar ? 1 : 0);
    for (uint64_t i = 0; i < useNVars; i++)
    {
      // We must have a good name for these variables, these are
      // the ones output in rewrite rules. We choose
      // a,b,c,...,y,z,x1,x2,...
      std::stringstream ssv;
      if (varCounter < 26)
      {
        ssv << static_cast<char>(varCounter + static_cast<uint64_t>('A'));
      }
      else
      {
        ssv << "x" << (varCounter - 26);
      }
      varCounter++;
      Node v = nm->mkBoundVar(ssv.str(), tn);
      Trace("srs-input") << "Make variable " << v << " of type " << tn
                         << std::endl;
      tvars[tn].push_back(v);
      allVars.push_back(v);
    }
  }
  Trace("srs-input") << "...finished." << std::endl;

  // if the problem is trivial, e.g. contains no non-constant terms, then we
  // exit with an exception.
  if (allVars.empty())
  {
    return tlGrammarTypes;
  }

  Trace("srs-input") << "Convert subterms to free variable form..."
                     << std::endl;
  // Replace all free variables with bound variables. This ensures that
  // we can perform term canonization on subterms.
  std::vector<Node> vsubs;
  for (const Node& v : vars)
  {
    TypeNode tnv = v.getType();
    Node vs = nm->mkBoundVar(tnv);
    vsubs.push_back(vs);
  }
  if (!vars.empty())
  {
    for (unsigned i = 0, nterms = terms.size(); i < nterms; i++)
    {
      terms[i] = terms[i].substitute(
          vars.begin(), vars.end(), vsubs.begin(), vsubs.end());
    }
  }
  Trace("srs-input") << "...finished." << std::endl;

  Trace("srs-input") << "Process " << terms.size() << " subterms..."
                     << std::endl;
  // We've collected all terms in the input. We construct a sygus grammar in
  // following which generates terms that correspond to abstractions of the
  // terms in the input.

  // We map terms to a canonical (ordered variable) form. This ensures that
  // we don't generate distinct grammar types for distinct alpha-equivalent
  // terms, which would produce grammars of identical shape.
  std::map<Node, Node> term_to_cterm;
  std::map<Node, Node> cterm_to_term;
  std::vector<Node> cterms;
  // canonical terms for each type
  std::map<TypeNode, std::vector<Node> > t_cterms;
  expr::TermCanonize tcanon;
  for (unsigned i = 0, nterms = terms.size(); i < nterms; i++)
  {
    Node n = terms[i];
    Node cn = tcanon.getCanonicalTerm(n);
    term_to_cterm[n] = cn;
    Trace("srs-input-debug") << "Canon : " << n << " -> " << cn << std::endl;
    std::map<Node, Node>::iterator itc = cterm_to_term.find(cn);
    if (itc == cterm_to_term.end())
    {
      cterm_to_term[cn] = n;
      cterms.push_back(cn);
      t_cterms[cn.getType()].push_back(cn);
    }
  }
  Trace("srs-input") << "...finished." << std::endl;
  // the sygus variable list
  Node sygusVarList = nm->mkNode(BOUND_VAR_LIST, allVars);
  Trace("srs-input") << "Have " << cterms.size() << " canonical subterms."
                     << std::endl;

  Trace("srs-input") << "Construct unresolved types..." << std::endl;
  // each canonical subterm corresponds to a grammar type
  std::vector<SygusDatatype> sdts;
  // make unresolved types for each canonical term
  std::map<Node, TypeNode> cterm_to_utype;
  for (unsigned i = 0, ncterms = cterms.size(); i < ncterms; i++)
  {
    Node ct = cterms[i];
    std::stringstream ss;
    ss << "T" << i;
    std::string tname = ss.str();
    TypeNode tnu = nm->mkUnresolvedDatatypeSort(tname);
    cterm_to_utype[ct] = tnu;
    sdts.push_back(SygusDatatype(tname));
  }
  Trace("srs-input") << "...finished." << std::endl;

  Trace("srs-input") << "Construct sygus datatypes..." << std::endl;
  for (unsigned i = 0, ncterms = cterms.size(); i < ncterms; i++)
  {
    Node ct = cterms[i];
    Node t = cterm_to_term[ct];

    // add the variables for the type
    TypeNode ctt = ct.getType();
    std::vector<TypeNode> argList;
    // we add variable constructors if we are not Boolean, we are interested
    // in purely propositional rewrites (via the option), or this term is
    // a Boolean variable.
    if (!ctt.isBoolean() || ct.getKind() == BOUND_VARIABLE)
    {
      // may or may not have variables for this type
      if (tvars.find(ctt) != tvars.end())
      {
        for (const Node& v : tvars[ctt])
        {
          std::stringstream ssc;
          ssc << "C_" << i << "_" << v;
          sdts[i].addConstructor(v, ssc.str(), argList);
        }
      }
    }
    // add the constructor for the operator if it is not a variable
    if (!ct.isVar())
    {
      // note that some terms like re.allchar have operators despite having
      // no children, we should take ct itself in these cases
      Node op =
          (ct.getNumChildren() > 0 && ct.hasOperator()) ? ct.getOperator() : ct;
      // iterate over the original term
      for (const Node& tc : t)
      {
        // map its arguments back to canonical
        Assert(term_to_cterm.find(tc) != term_to_cterm.end());
        Node ctc = term_to_cterm[tc];
        Assert(cterm_to_utype.find(ctc) != cterm_to_utype.end());
        // get the type
        argList.push_back(cterm_to_utype[ctc]);
      }
      // check if we should chain
      Kind k = NodeManager::operatorToKind(op);
      bool do_chain = argList.size() > 2
                      && theory::quantifiers::TermUtil::isAssoc(k)
                      && theory::quantifiers::TermUtil::isComm(k);
      if (do_chain)
      {
        // eliminate duplicate child types
        std::set<TypeNode> argSet(argList.begin(), argList.end());

        // we make one type per child
        // the operator of each constructor is a no-op
        Node tbv = nm->mkBoundVar(ctt);
        Node lambdaOp =
            nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, tbv), tbv);
        std::vector<TypeNode> argListc;
        // the following construction admits any number of repeated factors,
        // so for instance, t1+t2+t3, we generate the grammar:
        // T_{t1+t2+t3} ->
        //   +( T_{t1+t2+t3}, T_{t1+t2+t3} ) | T_{t1} | T_{t2} | T_{t3}
        // where we write T_t to denote "the type that abstracts term t".
        // Notice this construction allows to abstract subsets of the factors
        // of t1+t2+t3. This is particularly helpful for terms t1+...+tn for
        // large n, where we would like to consider binary applications of +.
        size_t j = 0;
        for (const TypeNode& arg : argSet)
        {
          argListc.clear();
          argListc.push_back(arg);
          std::stringstream sscs;
          sscs << "C_factor_" << i << "_" << j;
          Trace("srs-input-cons") << "Add (nested chain) " << lambdaOp << " "
                                  << lambdaOp.getType() << std::endl;
          // ID function is not printed and does not count towards weight
          sdts[i].addConstructor(lambdaOp,
                                 sscs.str(),
                                 argListc,
                                 0);
          j++;
        }
        // recursive apply
        TypeNode recType = cterm_to_utype[ct];
        argListc.clear();
        argListc.push_back(recType);
        argListc.push_back(recType);
        std::stringstream ssc;
        ssc << "C_" << i << "_rec_" << op;
        Trace("srs-input-cons")
            << "Add (chain) " << op << " " << op.getType() << std::endl;
        sdts[i].addConstructor(op, ssc.str(), argListc);
      }
      else
      {
        std::stringstream ssc;
        ssc << "C_" << i << "_" << op;
        Trace("srs-input-cons")
            << "Add " << op << " " << op.getType() << std::endl;
        sdts[i].addConstructor(op, ssc.str(), argList);
      }
    }
    Assert(sdts[i].getNumConstructors() > 0);
    sdts[i].initializeDatatype(ctt, sygusVarList, false, false);
  }
  Trace("srs-input") << "...finished." << std::endl;

  Trace("srs-input") << "Make mutual datatype types for subterms..."
                     << std::endl;
  // extract the datatypes
  std::vector<DType> datatypes;
  for (unsigned i = 0, ndts = sdts.size(); i < ndts; i++)
  {
    datatypes.push_back(sdts[i].getDatatype());
  }
  std::vector<TypeNode> types = nm->mkMutualDatatypeTypes(datatypes);
  Trace("srs-input") << "...finished." << std::endl;
  Assert(types.size() == datatypes.size());
  std::map<Node, TypeNode> subtermTypes;
  for (unsigned i = 0, ncterms = cterms.size(); i < ncterms; i++)
  {
    subtermTypes[cterms[i]] = types[i];
  }

  Trace("srs-input") << "Construct the top-level types..." << std::endl;
  // we now are ready to create the "top-level" types
  for (std::pair<const TypeNode, std::vector<Node> >& tcp : t_cterms)
  {
    TypeNode t = tcp.first;
    std::stringstream ss;
    ss << "T_" << t;
    SygusDatatype sdttl(ss.str());
    Node tbv = nm->mkBoundVar(t);
    // the operator of each constructor is a no-op
    Node lambdaOp = nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, tbv), tbv);
    Trace("srs-input") << "  We have " << tcp.second.size()
                       << " subterms of type " << t << std::endl;
    for (unsigned i = 0, size = tcp.second.size(); i < size; i++)
    {
      Node n = tcp.second[i];
      // add constructor that encodes abstractions of this subterm
      std::vector<TypeNode> argList;
      Assert(subtermTypes.find(n) != subtermTypes.end());
      argList.push_back(subtermTypes[n]);
      std::stringstream ssc;
      ssc << "Ctl_" << i;
      // the no-op should not be printed, hence we pass an empty callback
      sdttl.addConstructor(lambdaOp,
                           ssc.str(),
                           argList,
                           0);
      Trace("srs-input-debug")
          << "Grammar for subterm " << n << " is: " << std::endl;
      Trace("srs-input-debug") << subtermTypes[n].getDType() << std::endl;
    }
    // set that this is a sygus datatype
    sdttl.initializeDatatype(t, sygusVarList, false, false);
    DType dttl = sdttl.getDatatype();
    TypeNode tlt = nm->mkDatatypeType(dttl);
    tlGrammarTypes[t] = tlt;
    Trace("srs-input") << "Grammar is: " << std::endl;
    Trace("srs-input") << printer::smt2::Smt2Printer::sygusGrammarString(tlt)
                       << std::endl;
  }
  Trace("srs-input") << "...finished." << std::endl;
  return tlGrammarTypes;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
