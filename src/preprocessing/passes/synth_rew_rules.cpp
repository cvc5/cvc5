/*********************                                                        */
/*! \file synth_rew_rules.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A technique for synthesizing candidate rewrites of the form t1 = t2,
 ** where t1 and t2 are subterms of the input.
 **/

#include "preprocessing/passes/synth_rew_rules.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "printer/sygus_print_callback.h"
#include "theory/quantifiers/candidate_rewrite_database.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_canonize.h"
#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

// Attribute for whether we have computed rewrite rules for a given term.
// Notice that this currently must be a global attribute, since if
// we've computed rewrites for a term, we should not compute rewrites for the
// same term in a subcall to another SmtEngine (for instance, when using
// "exact" equivalence checking).
struct SynthRrComputedAttributeId
{
};
typedef expr::Attribute<SynthRrComputedAttributeId, bool>
    SynthRrComputedAttribute;

SynthRewRulesPass::SynthRewRulesPass(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "synth-rr"){};

PreprocessingPassResult SynthRewRulesPass::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Trace("synth-rr-prep") << "Synthesize rewrite rules from assertions..."
                         << std::endl;
  std::vector<Node>& assertions = assertionsToPreprocess->ref();

  NodeManager* nm = NodeManager::currentNM();

  // attribute to mark processed terms
  SynthRrComputedAttribute srrca;

  // initialize the candidate rewrite
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  // Get all usable terms from the input. A term is usable if it does not
  // contain a quantified subterm
  std::vector<Node> terms;
  // all variables
  std::vector<Node> vars;
  TNode cur;
  Trace("synth-rr-prep") << "Collect terms in assertions..." << std::endl;
  for (const Node& a : assertions)
  {
    Trace("synth-rr-prep-debug") << "Assertion : " << a << std::endl;
    visit.push_back(a);
    do
    {
      cur = visit.back();
      visit.pop_back();
      it = visited.find(cur);
      // if already processed, ignore
      if (cur.getAttribute(SynthRrComputedAttribute()))
      {
        Trace("synth-rr-prep-debug")
            << "...already processed " << cur << std::endl;
      }
      else if (it == visited.end())
      {
        Trace("synth-rr-prep-debug") << "...preprocess " << cur << std::endl;
        visited[cur] = false;
        Kind k = cur.getKind();
        bool isQuant = k == FORALL || k == EXISTS || k == LAMBDA || k == CHOICE;
        // we recurse on this node if it is not a quantified formula
        if (!isQuant)
        {
          visit.push_back(cur);
          for (const Node& cc : cur)
          {
            visit.push_back(cc);
          }
        }
      }
      else if (!it->second)
      {
        Trace("synth-rr-prep-debug") << "...postprocess " << cur << std::endl;
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
          Trace("synth-rr-prep-debug") << "...children are valid" << std::endl;
          // for now, ignore Boolean terms
          if (!cur.getType().isBoolean())
          {
            Trace("synth-rr-prep-debug") << "Add term " << cur << std::endl;
            terms.push_back(cur);
            if (cur.isVar())
            {
              vars.push_back(cur);
            }
          }
          // mark as processed
          cur.setAttribute(srrca, true);
        }
        visited[cur] = childrenValid;
      }
    } while (!visit.empty());
  }
  Trace("synth-rr-prep") << "...finished." << std::endl;

  Trace("synth-rr-prep") << "Convert subterms to free variable form..."
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
  Trace("synth-rr-prep") << "...finished." << std::endl;

  Trace("synth-rr-prep") << "Process " << terms.size() << " subterms..."
                         << std::endl;
  // We've collected all terms in the input. We will produce skeletons from
  // these terms. We start by constructing a fixed number of variables per
  // type.
  unsigned nvars = options::sygusRewSynthInputNVars();
  std::map<TypeNode, std::vector<Node> > tvars;
  std::vector<TypeNode> allVarTypes;
  std::vector<Node> allVars;
  // We also map terms to a canonical (ordered) form. This ensures that
  // we don't generate distinct grammar types for distinct alpha-equivalent
  // terms, which would produce grammars of identical shape.
  std::map<Node, Node> term_to_cterm;
  std::map<Node, Node> cterm_to_term;
  std::vector<Node> cterms;
  // canonical terms for each type
  std::map<TypeNode, std::vector<Node> > t_cterms;
  theory::quantifiers::TermCanonize tcanon;
  unsigned varCounter = 0;
  for (unsigned i = 0, nterms = terms.size(); i < nterms; i++)
  {
    Node n = terms[i];
    Node cn = tcanon.getCanonicalTerm(n);
    term_to_cterm[n] = cn;
    Trace("synth-rr-prep-debug")
        << "Canon : " << n << " -> " << cn << std::endl;
    std::map<Node, Node>::iterator itc = cterm_to_term.find(cn);
    if (itc == cterm_to_term.end())
    {
      cterm_to_term[cn] = n;
      cterms.push_back(cn);
      // register type information
      TypeNode tn = n.getType();
      if (tvars.find(tn) == tvars.end())
      {
        for (unsigned i = 0; i < nvars; i++)
        {
          // We must have a good name for these variables, these are
          // the ones output in rewrite rules. We choose a,b,c,...,y,z,x1,x2,...
          std::stringstream ssv;
          if( varCounter<26 )
          {
            ssv << String::convertUnsignedIntToChar(varCounter+32);
          }
          else
          {
            ssv << "x" << (varCounter-26);
          }
          varCounter++;
          Node v = nm->mkBoundVar(ssv.str(),tn);
          tvars[tn].push_back(v);
          allVars.push_back(v);
          allVarTypes.push_back(tn);
        }
      }
      t_cterms[tn].push_back(cn);
    }
  }
  Trace("synth-rr-prep") << "...finished." << std::endl;
  // the sygus variable list
  Node sygusVarList = nm->mkNode(BOUND_VAR_LIST, allVars);
  Expr sygusVarListE = sygusVarList.toExpr();
  Trace("synth-rr-prep") << "Have " << cterms.size() << " canonical subterms."
                         << std::endl;

  Trace("synth-rr-prep") << "Construct unresolved types..." << std::endl;
  // each canonical subterm corresponds to a grammar type
  std::set<Type> unres;
  std::vector<Datatype> datatypes;
  // make unresolved types for each canonical term
  std::map<Node, TypeNode> cterm_to_utype;
  std::map<Node, std::string> tnames;
  for (unsigned i = 0, ncterms = cterms.size(); i < ncterms; i++)
  {
    Node ct = cterms[i];
    std::stringstream ss;
    ss << "T" << i;
    std::string tname = ss.str();
    tnames[ct] = tname;
    TypeNode tnu = nm->mkSort(tname, ExprManager::SORT_FLAG_PLACEHOLDER);
    cterm_to_utype[ct] = tnu;
    unres.insert(tnu.toType());
  }
  Trace("synth-rr-prep") << "...finished." << std::endl;

  Trace("synth-rr-prep") << "Construct datatypes..." << std::endl;
  for (unsigned i = 0, ncterms = cterms.size(); i < ncterms; i++)
  {
    Node ct = cterms[i];
    Node t = cterm_to_term[ct];
    Datatype dt(tnames[ct]);

    // add the variables for the type
    TypeNode ctt = ct.getType();
    Assert(tvars.find(ctt) != tvars.end());
    std::vector<Type> argList;
    for (const Node& v : tvars[ctt])
    {
      std::stringstream ssc;
      ssc << "C_" << i << "_" << v;
      dt.addSygusConstructor(v.toExpr(), ssc.str(), argList);
    }
    // add the constructor for the operator if it is not a variable
    if (ct.getKind() != BOUND_VARIABLE)
    {
      Assert(!ct.isVar());
      Node op = ct.hasOperator() ? ct.getOperator() : ct;
      // iterate over the original term
      for (const Node& tc : t)
      {
        // map its arguments back to canonical
        Assert(term_to_cterm.find(tc) != term_to_cterm.end());
        Node ctc = term_to_cterm[tc];
        Assert(cterm_to_utype.find(ctc) != cterm_to_utype.end());
        // get the type
        argList.push_back(cterm_to_utype[ctc].toType());
      }
      std::stringstream ssc;
      ssc << "C_" << i << "_" << op;
      dt.addSygusConstructor(op.toExpr(), ssc.str(), argList);
    }
    dt.setSygus(ctt.toType(), sygusVarListE, false, false);
    datatypes.push_back(dt);
  }
  Trace("synth-rr-prep") << "...finished." << std::endl;

  Trace("synth-rr-prep") << "Make mutual datatype types for subterms..."
                         << std::endl;
  std::vector<DatatypeType> types = nm->toExprManager()->mkMutualDatatypeTypes(
      datatypes, unres, ExprManager::DATATYPE_FLAG_PLACEHOLDER);
  Trace("synth-rr-prep") << "...finished." << std::endl;
  Assert(types.size() == unres.size());
  std::map<Node, DatatypeType> subtermTypes;
  for (unsigned i = 0, ncterms = cterms.size(); i < ncterms; i++)
  {
    subtermTypes[cterms[i]] = types[i];
  }

  Trace("synth-rr-prep") << "Construct the top-level types..." << std::endl;
  // we now are ready to create the "top-level" types
  std::map<TypeNode, TypeNode> tlGrammarTypes;
  for (std::pair<const TypeNode, std::vector<Node> >& tcp : t_cterms)
  {
    TypeNode t = tcp.first;
    std::stringstream ss;
    ss << "T_" << t;
    Datatype dttl(ss.str());
    Node tbv = nm->mkBoundVar(t);
    // the operator of each constructor is a no-op
    Expr lambdaOp =
        nm->mkNode(LAMBDA, nm->mkNode(BOUND_VAR_LIST, tbv), tbv).toExpr();
    Trace("synth-rr-prep") << "  We have " << tcp.second.size()
                           << " subterms of type " << t << std::endl;
    for (unsigned i = 0, size = tcp.second.size(); i < size; i++)
    {
      Node n = tcp.second[i];
      // add constructor that encodes abstractions of this subterm
      std::vector<Type> argList;
      Assert(subtermTypes.find(n) != subtermTypes.end());
      argList.push_back(subtermTypes[n]);
      std::stringstream ssc;
      ssc << "Ctl_" << i;
      // the no-op should not be printed, hence we pass an empty callback
      dttl.addSygusConstructor(lambdaOp,
                               ssc.str(),
                               argList,
                               printer::SygusEmptyPrintCallback::getEmptyPC());
      Trace("synth-rr-prep-debug")
          << "Grammar for subterm " << n << " is: " << std::endl;
      Trace("synth-rr-prep-debug")
          << subtermTypes[n].getDatatype() << std::endl;
    }
    // set that this is a sygus datatype
    dttl.setSygus(t.toType(), sygusVarListE, false, false);
    DatatypeType tlt = nm->toExprManager()->mkDatatypeType(
        dttl, ExprManager::DATATYPE_FLAG_PLACEHOLDER);
    tlGrammarTypes[t] = TypeNode::fromType(tlt);
    Trace("synth-rr-prep") << "Grammar is: " << std::endl;
    Trace("synth-rr-prep") << tlt.getDatatype() << std::endl;
  }
  Trace("synth-rr-prep") << "...finished." << std::endl;

  // sygus attribute to mark the conjecture as a sygus conjecture
  Trace("synth-rr-prep") << "Make sygus conjecture..." << std::endl;
  Node iaVar = nm->mkSkolem("sygus", nm->booleanType());
  // the attribute to mark the conjecture as being a sygus conjecture
  theory::SygusAttribute ca;
  iaVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(INST_ATTRIBUTE, iaVar);
  Node instAttrList = nm->mkNode(INST_PATTERN_LIST, instAttr);
  // we are "synthesizing" functions for each type of subterm
  std::vector<Node> synthFuns;
  unsigned fCounter = 1;
  for (std::pair<const TypeNode, TypeNode> ttp : tlGrammarTypes)
  {
    Node gvar = nm->mkBoundVar("sfproxy", ttp.second);
    theory::SygusSynthGrammarAttribute ssg;
    TypeNode ft = nm->mkFunctionType(allVarTypes, ttp.first);
    // likewise, it is helpful if these have good names, we choose f1, f2, ...
    std::stringstream ssf;
    ssf << "f" << fCounter;
    fCounter++;
    Node sfun = nm->mkBoundVar(ssf.str(), ft);
    // this marks that the grammar used for solutions for sfun is the type of
    // gvar, which is the sygus datatype type constructed above.
    sfun.setAttribute(ssg, gvar);
    synthFuns.push_back(sfun);
  }
  Node fvarBvl = nm->mkNode(BOUND_VAR_LIST, synthFuns);

  Node body = nm->mkConst(false);
  body = nm->mkNode(FORALL, fvarBvl, body, instAttrList);
  Trace("synth-rr-prep") << "got : " << body << std::endl;
  Trace("synth-rr-prep") << "...finished." << std::endl;

  Node trueNode = nm->mkConst(true);
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    if (i == 0)
    {
      assertionsToPreprocess->replace(i, body);
    }
    else
    {
      assertionsToPreprocess->replace(i, trueNode);
    }
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
