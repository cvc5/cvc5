/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the theory of strings.
 */

#include "theory/strings/core_solver.h"

#include "base/configuration.h"
#include "expr/sequence.h"
#include "options/strings_options.h"
#include "smt/logic_exception.h"
#include "theory/rewriter.h"
#include "theory/strings/sequences_rewriter.h"
#include "theory/strings/strings_entail.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/rational.h"
#include "util/string.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

CoreInferInfo::CoreInferInfo(InferenceId id) : d_infer(id), d_index(0), d_rev(false) {}

CoreSolver::CoreSolver(Env& env,
                       SolverState& s,
                       InferenceManager& im,
                       TermRegistry& tr,
                       BaseSolver& bs)
    : EnvObj(env),
      d_state(s),
      d_im(im),
      d_termReg(tr),
      d_bsolver(bs),
      d_nfPairs(context()),
      d_extDeq(userContext()),
      d_modelUnsoundId(IncompleteId::NONE)
{
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  d_one = NodeManager::currentNM()->mkConstInt(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConstInt(Rational(-1));
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

CoreSolver::~CoreSolver() {

}

void CoreSolver::debugPrintFlatForms( const char * tc ){
  for( unsigned k=0; k<d_strings_eqc.size(); k++ ){
    Node eqc = d_strings_eqc[k];
    if( d_eqc[eqc].size()>1 ){
      Trace( tc ) << "EQC [" << eqc << "]" << std::endl;
    }else{
      Trace( tc ) << "eqc [" << eqc << "]";
    }
    Node c = d_bsolver.getConstantEqc(eqc);
    if( !c.isNull() ){
      Trace( tc ) << "  C: " << c;
      if( d_eqc[eqc].size()>1 ){
        Trace( tc ) << std::endl;
      }
    }
    if( d_eqc[eqc].size()>1 ){
      for( unsigned i=0; i<d_eqc[eqc].size(); i++ ){
        Node n = d_eqc[eqc][i];
        Trace( tc ) << "    ";
        for( unsigned j=0; j<d_flat_form[n].size(); j++ ){
          Node fc = d_flat_form[n][j];
          Node fcc = d_bsolver.getConstantEqc(fc);
          Trace( tc ) << " ";
          if( !fcc.isNull() ){
            Trace( tc ) << fcc;
          }else{
            Trace( tc ) << fc;
          }
        }
        if( n!=eqc ){
          Trace( tc ) << ", from " << n;
        }
        Trace( tc ) << std::endl;
      }
    }else{
      Trace( tc ) << std::endl;
    }
  }
  Trace( tc ) << std::endl;
}

void CoreSolver::checkCycles()
{
  // first check for cycles, while building ordering of equivalence classes
  d_flat_form.clear();
  d_flat_form_index.clear();
  d_eqc.clear();
  // Rebuild strings eqc based on acyclic ordering, first copy the equivalence
  // classes from the base solver.
  const std::vector<Node>& eqc = d_bsolver.getStringLikeEqc();
  d_strings_eqc.clear();
  for (const Node& r : eqc)
  {
    std::vector< Node > curr;
    std::vector< Node > exp;
    checkCycles(r, curr, exp);
    if (d_im.hasProcessed())
    {
      return;
    }
  }
}

void CoreSolver::checkFlatForms()
{
  // debug print flat forms
  if (TraceIsOn("strings-ff"))
  {
    Trace("strings-ff") << "Flat forms : " << std::endl;
    debugPrintFlatForms("strings-ff");
  }

  // inferences without recursively expanding flat forms

  //(1) approximate equality by containment, infer conflicts
  for (const Node& eqc : d_strings_eqc)
  {
    Node c = d_bsolver.getConstantEqc(eqc);
    if (!c.isNull())
    {
      // if equivalence class is constant, all component constants in flat forms
      // must be contained in it, in order
      std::map<Node, std::vector<Node> >::iterator it = d_eqc.find(eqc);
      if (it != d_eqc.end())
      {
        for (const Node& n : it->second)
        {
          int firstc, lastc;
          if (!StringsEntail::canConstantContainList(
                  c, d_flat_form[n], firstc, lastc))
          {
            Trace("strings-ff-debug") << "Flat form for " << n
                                      << " cannot be contained in constant "
                                      << c << std::endl;
            Trace("strings-ff-debug") << "  indices = " << firstc << "/"
                                      << lastc << std::endl;
            // conflict, explanation is n = base ^ base = c ^ relevant portion
            // of ( n = f[n] )
            std::vector<Node> exp;
            for (int e = firstc; e <= lastc; e++)
            {
              if (d_flat_form[n][e].isConst())
              {
                Assert(e >= 0 && e < (int)d_flat_form_index[n].size());
                Assert(d_flat_form_index[n][e] >= 0
                       && d_flat_form_index[n][e] < (int)n.getNumChildren());
                d_im.addToExplanation(
                    n[d_flat_form_index[n][e]], d_flat_form[n][e], exp);
              }
            }
            d_bsolver.explainConstantEqc(n, eqc, exp);
            Node conc = d_false;
            d_im.sendInference(exp, conc, InferenceId::STRINGS_F_NCTN);
            return;
          }
        }
      }
    }
  }

  //(2) scan lists, unification to infer conflicts and equalities
  for (const Node& eqc : d_strings_eqc)
  {
    std::map<Node, std::vector<Node> >::iterator it = d_eqc.find(eqc);
    if (it == d_eqc.end() || it->second.size() <= 1)
    {
      continue;
    }
    // iterate over start index
    for (unsigned start = 0; start < it->second.size() - 1; start++)
    {
      for (unsigned r = 0; r < 2; r++)
      {
        bool isRev = r == 1;
        checkFlatForm(it->second, start, isRev);
        if (d_state.isInConflict())
        {
          return;
        }

        for (const Node& n : it->second)
        {
          std::reverse(d_flat_form[n].begin(), d_flat_form[n].end());
          std::reverse(d_flat_form_index[n].begin(),
                       d_flat_form_index[n].end());
        }
      }
    }
  }
}

void CoreSolver::checkFlatForm(std::vector<Node>& eqc,
                                  size_t start,
                                  bool isRev)
{
  size_t count = 0;
  // We check for flat form inferences involving `eqc[start]` and terms past
  // `start`. If there was a flat form inference involving `eqc[start]` and a
  // term at a smaller index `i`, we would have found it with when `start` was
  // `i`. Thus, we mark the preceeding terms in the equivalence class as
  // ineligible.
  std::vector<Node> inelig(eqc.begin(), eqc.begin() + start + 1);
  Node a = eqc[start];
  Trace("strings-ff-debug")
      << "Check flat form for a = " << a << ", whose flat form is "
      << d_flat_form[a] << ")" << std::endl;
  Node b;
  // the length explanation
  Node lant;
  do
  {
    std::vector<Node> exp;
    Node conc;
    InferenceId infType = InferenceId::UNKNOWN;
    size_t eqc_size = eqc.size();
    size_t asize = d_flat_form[a].size();
    if (count == asize)
    {
      for (size_t i = start + 1; i < eqc_size; i++)
      {
        b = eqc[i];
        if (std::find(inelig.begin(), inelig.end(), b) != inelig.end())
        {
          continue;
        }

        size_t bsize = d_flat_form[b].size();
        if (count < bsize)
        {
          Trace("strings-ff-debug")
              << "Found endpoint (in a) with non-empty b = " << b
              << ", whose flat form is " << d_flat_form[b] << std::endl;
          // endpoint
          Node emp = Word::mkEmptyWord(a.getType());
          std::vector<Node> conc_c;
          for (unsigned j = count; j < bsize; j++)
          {
            conc_c.push_back(b[d_flat_form_index[b][j]].eqNode(emp));
          }
          Assert(!conc_c.empty());
          conc = utils::mkAnd(conc_c);
          infType = InferenceId::STRINGS_F_ENDPOINT_EMP;
          Assert(count > 0);
          // swap, will enforce is empty past current
          a = eqc[i];
          b = eqc[start];
          break;
        }
        inelig.push_back(eqc[i]);
      }
    }
    else
    {
      Node curr = d_flat_form[a][count];
      Node curr_c = d_bsolver.getConstantEqc(curr);
      Node ac = a[d_flat_form_index[a][count]];
      std::vector<Node> lexp;
      Node lcurr = d_state.getLength(ac, lexp);
      for (size_t i = start + 1; i < eqc_size; i++)
      {
        b = eqc[i];
        if (std::find(inelig.begin(), inelig.end(), b) != inelig.end())
        {
          continue;
        }

        if (count == d_flat_form[b].size())
        {
          inelig.push_back(b);
          Trace("strings-ff-debug")
              << "Found endpoint in b = " << b << ", whose flat form is "
              << d_flat_form[b] << std::endl;
          // endpoint
          Node emp = Word::mkEmptyWord(a.getType());
          std::vector<Node> conc_c;
          for (size_t j = count; j < asize; j++)
          {
            conc_c.push_back(a[d_flat_form_index[a][j]].eqNode(emp));
          }
          Assert(!conc_c.empty());
          conc = utils::mkAnd(conc_c);
          infType = InferenceId::STRINGS_F_ENDPOINT_EMP;
          Assert(count > 0);
          break;
        }
        else
        {
          Node cc = d_flat_form[b][count];
          if (cc != curr)
          {
            Node bc = b[d_flat_form_index[b][count]];
            inelig.push_back(b);
            Assert(!d_state.areEqual(curr, cc));
            Node cc_c = d_bsolver.getConstantEqc(cc);
            if (!curr_c.isNull() && !cc_c.isNull())
            {
              // check for constant conflict
              size_t index;
              Node s = Word::splitConstant(cc_c, curr_c, index, isRev);
              if (s.isNull())
              {
                d_bsolver.explainConstantEqc(ac,curr,exp);
                d_bsolver.explainConstantEqc(bc,cc,exp);
                conc = d_false;
                infType = InferenceId::STRINGS_F_CONST;
                break;
              }
            }
            else if ((d_flat_form[a].size() - 1) == count
                     && (d_flat_form[b].size() - 1) == count)
            {
              conc = ac.eqNode(bc);
              infType = InferenceId::STRINGS_F_ENDPOINT_EQ;
              break;
            }
            else
            {
              // if lengths are the same, apply LengthEq
              std::vector<Node> lexp2;
              Node lcc = d_state.getLength(bc, lexp2);
              if (d_state.areEqual(lcurr, lcc))
              {
                if (TraceIsOn("strings-ff-debug"))
                {
                  Trace("strings-ff-debug")
                      << "Infer " << ac << " == " << bc << " since " << lcurr
                      << " == " << lcc << std::endl;
                  Trace("strings-ff-debug")
                      << "Explanation for " << lcurr << " is ";
                  for (size_t j = 0; j < lexp.size(); j++)
                  {
                    Trace("strings-ff-debug") << lexp[j] << std::endl;
                  }
                  Trace("strings-ff-debug")
                      << "Explanation for " << lcc << " is ";
                  for (size_t j = 0; j < lexp2.size(); j++)
                  {
                    Trace("strings-ff-debug") << lexp2[j] << std::endl;
                  }
                }
                std::vector<Node> lexpc;
                lexpc.insert(lexpc.end(), lexp.begin(), lexp.end());
                lexpc.insert(lexpc.end(), lexp2.begin(), lexp2.end());
                d_im.addToExplanation(lcurr, lcc, lexpc);
                lant = utils::mkAnd(lexpc);
                conc = ac.eqNode(bc);
                infType = InferenceId::STRINGS_F_UNIFY;
                break;
              }
            }
          }
        }
      }
    }
    if (!conc.isNull())
    {
      Trace("strings-ff-debug") << "Found inference (" << infType
                                << "): " << conc << " based on equality " << a
                                << " == " << b << ", " << isRev << std::endl;
      // explain why prefixes up to now were the same
      for (size_t j = 0; j < count; j++)
      {
        Trace("strings-ff-debug") << "Add at " << d_flat_form_index[a][j] << " "
                                  << d_flat_form_index[b][j] << std::endl;
        d_im.addToExplanation(
            a[d_flat_form_index[a][j]], b[d_flat_form_index[b][j]], exp);
      }
      // explain why other components up to now are empty
      for (unsigned t = 0; t < 2; t++)
      {
        Node c = t == 0 ? a : b;
        ssize_t jj;
        if (infType == InferenceId::STRINGS_F_ENDPOINT_EQ
            || (t == 1 && infType == InferenceId::STRINGS_F_ENDPOINT_EMP))
        {
          // explain all the empty components for F_EndpointEq, all for
          // the short end for F_EndpointEmp
          jj = isRev ? -1 : c.getNumChildren();
        }
        else
        {
          jj = t == 0 ? d_flat_form_index[a][count]
                      : d_flat_form_index[b][count];
        }
        ssize_t startj = isRev ? jj + 1 : 0;
        ssize_t endj = isRev ? c.getNumChildren() : jj;
        Node emp = Word::mkEmptyWord(a.getType());
        for (ssize_t j = startj; j < endj; j++)
        {
          if (d_state.areEqual(c[j], emp))
          {
            d_im.addToExplanation(c[j], emp, exp);
          }
        }
      }
      d_im.addToExplanation(a, b, exp);
      if (!lant.isNull())
      {
        // add the length explanation
        exp.push_back(lant);
      }
      // Notice that F_EndpointEmp is not typically applied, since
      // strict prefix equality ( a.b = a ) where a,b non-empty
      // is conflicting by arithmetic len(a.b)=len(a)+len(b)!=len(a)
      // when len(b)!=0. Although if we do not infer this conflict eagerly,
      // it may be applied (see #3272).
      d_im.sendInference(exp, conc, infType, isRev);
      if (d_state.isInConflict())
      {
        return;
      }
      break;
    }
    count++;
  } while (inelig.size() < eqc.size());
}

Node CoreSolver::checkCycles( Node eqc, std::vector< Node >& curr, std::vector< Node >& exp ){
  if( std::find( curr.begin(), curr.end(), eqc )!=curr.end() ){
    // a loop
    return eqc;
  }else if( std::find( d_strings_eqc.begin(), d_strings_eqc.end(), eqc )==d_strings_eqc.end() ){
    curr.push_back( eqc );
    Node emp = Word::mkEmptyWord(eqc.getType());
    //look at all terms in this equivalence class
    eq::EqualityEngine* ee = d_state.getEqualityEngine();
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, ee );
    const std::set<Node>& rlvSet = d_termReg.getRelevantTermSet();
    while( !eqc_i.isFinished() ) {
      Node n = (*eqc_i);
      ++eqc_i;
      if (n.getKind() != kind::STRING_CONCAT || rlvSet.find(n) == rlvSet.end()
          || d_bsolver.isCongruent(n))
      {
        continue;
      }
      Trace("strings-cycle")
          << eqc << " check term : " << n << " in " << eqc << std::endl;
      if (eqc != emp)
      {
        d_eqc[eqc].push_back(n);
      }
      size_t nchild = n.getNumChildren();
      for (size_t i=0; i<nchild; i++)
      {
        Node nc = n[i];
        Node nr = d_state.getRepresentative(nc);
        if (eqc == emp)
        {
          // for empty eqc, ensure all components are empty
          if (nr != emp)
          {
            std::vector<Node> exps;
            exps.push_back(n.eqNode(emp));
            d_im.sendInference(
                exps, nc.eqNode(emp), InferenceId::STRINGS_I_CYCLE_E);
            return Node::null();
          }
        }
        else
        {
          if (nr != emp)
          {
            d_flat_form[n].push_back(nr);
            d_flat_form_index[n].push_back(i);
          }
          // for non-empty eqc, recurse and see if we find a loop
          Node ncy = checkCycles(nr, curr, exp);
          if (!ncy.isNull())
          {
            Trace("strings-cycle") << eqc << " cycle: " << ncy << " at " << n
                                   << "[" << i << "] : " << nc << std::endl;
            d_im.addToExplanation(n, eqc, exp);
            d_im.addToExplanation(nr, nc, exp);
            if (ncy == eqc)
            {
              // can infer all other components must be empty
              for (size_t j = 0; j < nchild; j++)
              {
                // take first non-empty
                if (j != i && !d_state.areEqual(n[j], emp))
                {
                  d_im.sendInference(
                      exp, n[j].eqNode(emp), InferenceId::STRINGS_I_CYCLE);
                  return Node::null();
                }
              }
              Trace("strings-error")
                  << "Looping term should be congruent : " << n << " " << eqc
                  << " " << ncy << std::endl;
              // should find a non-empty component, otherwise would have been
              // singular congruent (I_Norm_S)
              Assert(false);
            }
            else
            {
              return ncy;
            }
          }
          else if (d_im.hasProcessed())
          {
            return Node::null();
          }
        }
      }
    }
    curr.pop_back();
    Trace("strings-eqc") << "* add string eqc: " << eqc << std::endl;
    //now we can add it to the list of equivalence classes
    d_strings_eqc.push_back( eqc );
  }else{
    //already processed
  }
  return Node::null();
}

void CoreSolver::checkNormalFormsEqProp()
{
  // Reset the possible inferences and model unsoundness id. These are
  // set in this method and processed in checkNormalFormsEq.
  d_pinfers.clear();
  d_modelUnsoundId = IncompleteId::NONE;
  // calculate normal forms for each equivalence class, possibly adding
  // splitting lemmas
  d_normal_form.clear();
  // map from normal form terms (the concatenation of the terms in the normal
  // form) to the equivalence that had that normal form
  std::map<Node, Node> nf_to_eqc;
  for (const Node& eqc : d_strings_eqc)
  {
    Assert(d_pinfers.empty());
    TypeNode stype = eqc.getType();
    Trace("strings-process-debug") << "- Verify normal forms are the same for "
                                   << eqc << std::endl;
    normalizeEquivalenceClass(eqc, stype, d_pinfers);
    Trace("strings-debug") << "Finished normalizing eqc..." << std::endl;
    if (d_im.hasProcessed())
    {
      return;
    }
    if (!d_pinfers.empty())
    {
      // if we had a possible inference, we were unable to assign
      // a normal form to this equivalence class based on the call to
      // normalizeEquivalenceClass, we return. We process the possible
      // inferences later in checkNormalFormsEq if necessary.
      return;
    }
    NormalForm& nfe = getNormalForm(eqc);
    Node nf_term = d_termReg.mkNConcat(nfe.d_nf, stype);
    std::map<Node, Node>::iterator itn = nf_to_eqc.find(nf_term);
    if (itn != nf_to_eqc.end())
    {
      NormalForm& nfe_eq = getNormalForm(itn->second);
      // two equivalence classes have same normal form, merge
      std::vector<Node> nf_exp(nfe.d_exp.begin(), nfe.d_exp.end());
      if (!nfe_eq.d_exp.empty())
      {
        nf_exp.push_back(utils::mkAnd(nfe_eq.d_exp));
      }
      Node eq = nfe.d_base.eqNode(nfe_eq.d_base);
      d_im.sendInference(nf_exp, eq, InferenceId::STRINGS_NORMAL_FORM);
      if (d_im.hasProcessed())
      {
        return;
      }
    }
    else
    {
      nf_to_eqc[nf_term] = eqc;
    }
    Trace("strings-process-debug")
        << "Done verifying normal forms are the same for " << eqc << std::endl;
  }
}

//compute d_normal_forms_(base,exp,exp_depend)[eqc]
void CoreSolver::normalizeEquivalenceClass(Node eqc,
                                           TypeNode stype,
                                           std::vector<CoreInferInfo>& pinfer)
{
  Trace("strings-process-debug") << "Process equivalence class " << eqc << std::endl;
  Node emp = Word::mkEmptyWord(stype);
  if (d_state.areEqual(eqc, emp))
  {
#ifdef CVC5_ASSERTIONS
    for( unsigned j=0; j<d_eqc[eqc].size(); j++ ){
      Node n = d_eqc[eqc][j];
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Assert(d_state.areEqual(n[i], emp));
      }
    }
#endif
    //do nothing
    Trace("strings-process-debug") << "Return process equivalence class " << eqc << " : empty." << std::endl;
    d_normal_form[eqc].init(emp);
  }
  else
  {
    // should not have computed the normal form of this equivalence class yet
    Assert(d_normal_form.find(eqc) == d_normal_form.end());
    // Normal forms for the relevant terms in the equivalence class of eqc
    std::vector<NormalForm> normal_forms;
    // map each term to its index in the above vector
    std::map<Node, unsigned> term_to_nf_index;
    // get the normal forms
    getNormalForms(eqc, normal_forms, term_to_nf_index, stype);
    if (d_im.hasProcessed())
    {
      return;
    }
    // process the normal forms
    processNEqc(eqc, normal_forms, stype, pinfer);
    // If we sent a lemma, or if pinfer is non-empty (a normal form could not
    // be assigned to this equivalence class), then we return. The possible
    // inferences (if necessary) will be processed in checkNormalFormsEq.
    if (d_im.hasProcessed() || !pinfer.empty())
    {
      return;
    }

    //construct the normal form
    Assert(!normal_forms.empty());
    unsigned nf_index = 0;
    std::map<Node, unsigned>::iterator it = term_to_nf_index.find(eqc);
    // we prefer taking the normal form whose base is the equivalence
    // class representative, since this leads to shorter explanations in
    // some cases.
    if (it != term_to_nf_index.end())
    {
      nf_index = it->second;
    }
    d_normal_form[eqc] = normal_forms[nf_index];
    Trace("strings-process-debug")
        << "Return process equivalence class " << eqc
        << " : returned = " << d_normal_form[eqc].d_nf << std::endl;
  }
}

const std::vector<Node>& CoreSolver::getRelevantDeq() const { return d_rlvDeq; }

NormalForm& CoreSolver::getNormalForm(Node n)
{
  std::map<Node, NormalForm>::iterator itn = d_normal_form.find(n);
  if (itn == d_normal_form.end())
  {
    Trace("strings-warn") << "WARNING: returning empty normal form for " << n
                          << std::endl;
    // Shouln't ask for normal forms of strings that weren't computed. This
    // likely means that n is not a representative or not a term in the current
    // context. We simply return a default normal form here in this case.
    Assert(false);
    return d_normal_form[n];
  }
  return itn->second;
}

Node CoreSolver::getNormalString(Node x, std::vector<Node>& nf_exp)
{
  if (!x.isConst())
  {
    Node xr = d_state.getRepresentative(x);
    TypeNode stype = xr.getType();
    std::map<Node, NormalForm>::iterator it = d_normal_form.find(xr);
    if (it != d_normal_form.end())
    {
      NormalForm& nf = it->second;
      Node ret = d_termReg.mkNConcat(nf.d_nf, stype);
      nf_exp.insert(nf_exp.end(), nf.d_exp.begin(), nf.d_exp.end());
      d_im.addToExplanation(x, nf.d_base, nf_exp);
      Trace("strings-debug")
          << "Term: " << x << " has a normal form " << ret << std::endl;
      return ret;
    }
    // if x does not have a normal form, then it should not occur in the
    // equality engine and hence should be its own representative.
    Assert(xr == x);
    if (x.getKind() == kind::STRING_CONCAT)
    {
      std::vector<Node> vec_nodes;
      for (unsigned i = 0; i < x.getNumChildren(); i++)
      {
        Node nc = getNormalString(x[i], nf_exp);
        vec_nodes.push_back(nc);
      }
      return d_termReg.mkNConcat(vec_nodes, stype);
    }
  }
  return x;
}

Node CoreSolver::getConclusion(Node x,
                               Node y,
                               PfRule rule,
                               bool isRev,
                               SkolemCache* skc,
                               std::vector<Node>& newSkolems)
{
  Trace("strings-csolver") << "CoreSolver::getConclusion: " << x << " " << y
                           << " " << rule << " " << isRev << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  Node conc;
  if (rule == PfRule::CONCAT_SPLIT || rule == PfRule::CONCAT_LPROP)
  {
    // must compare so that we are agnostic to order of x/y
    Node ux = x < y ? x : y;
    Node uy = x < y ? y : x;
    Node sk = skc->mkSkolemCached(ux,
                                  uy,
                                  isRev ? SkolemCache::SK_ID_V_UNIFIED_SPT_REV
                                        : SkolemCache::SK_ID_V_UNIFIED_SPT,
                                  "v_spt");
    newSkolems.push_back(sk);
    Node eq1 = x.eqNode(isRev ? nm->mkNode(STRING_CONCAT, sk, y)
                              : nm->mkNode(STRING_CONCAT, y, sk));

    if (rule == PfRule::CONCAT_LPROP)
    {
      conc = eq1;
    }
    else
    {
      Node eq2 = y.eqNode(isRev ? nm->mkNode(STRING_CONCAT, sk, x)
                                : nm->mkNode(STRING_CONCAT, x, sk));
      // make agnostic to x/y
      conc = x < y ? nm->mkNode(OR, eq1, eq2) : nm->mkNode(OR, eq2, eq1);
    }
    // we can assume its length is greater than zero
    Node emp = Word::mkEmptyWord(sk.getType());
    conc = nm->mkNode(
        AND,
        conc,
        sk.eqNode(emp).negate(),
        nm->mkNode(
            GT, nm->mkNode(STRING_LENGTH, sk), nm->mkConstInt(Rational(0))));
  }
  else if (rule == PfRule::CONCAT_CSPLIT)
  {
    Assert(y.isConst());
    size_t yLen = Word::getLength(y);
    Node firstChar =
        yLen == 1 ? y : (isRev ? Word::suffix(y, 1) : Word::prefix(y, 1));
    Node sk = skc->mkSkolemCached(
        x,
        isRev ? SkolemCache::SK_ID_VC_SPT_REV : SkolemCache::SK_ID_VC_SPT,
        "c_spt");
    newSkolems.push_back(sk);
    conc = x.eqNode(isRev ? nm->mkNode(STRING_CONCAT, sk, firstChar)
                          : nm->mkNode(STRING_CONCAT, firstChar, sk));
  }
  else if (rule == PfRule::CONCAT_CPROP)
  {
    // expect (str.++ z d) and c
    Assert(x.getKind() == STRING_CONCAT && x.getNumChildren() == 2);
    Node z = x[isRev ? 1 : 0];
    Node d = x[isRev ? 0 : 1];
    Assert(d.isConst());
    Node c = y;
    Assert(c.isConst());
    size_t cLen = Word::getLength(c);
    size_t p = getSufficientNonEmptyOverlap(c, d, isRev);
    Node preC =
        p == cLen ? c : (isRev ? Word::suffix(c, p) : Word::prefix(c, p));
    Node sk = skc->mkSkolemCached(
        z,
        preC,
        isRev ? SkolemCache::SK_ID_C_SPT_REV : SkolemCache::SK_ID_C_SPT,
        "c_spt");
    newSkolems.push_back(sk);
    conc = z.eqNode(isRev ? nm->mkNode(STRING_CONCAT, sk, preC)
                          : nm->mkNode(STRING_CONCAT, preC, sk));
  }

  return conc;
}

size_t CoreSolver::getSufficientNonEmptyOverlap(Node c, Node d, bool isRev)
{
  Assert(c.isConst() && c.getType().isStringLike());
  Assert(d.isConst() && d.getType().isStringLike());
  size_t p;
  size_t p2;
  size_t cLen = Word::getLength(c);
  if (isRev)
  {
    // Since non-empty, we start with character 1
    Node c1 = Word::prefix(c, cLen - 1);
    p = cLen - Word::roverlap(c1, d);
    p2 = Word::rfind(c1, d);
  }
  else
  {
    Node c1 = Word::substr(c, 1);
    p = cLen - Word::overlap(c1, d);
    p2 = Word::find(c1, d);
  }
  return p2 == std::string::npos ? p : (p > p2 + 1 ? p2 + 1 : p);
}

Node CoreSolver::getDecomposeConclusion(Node x,
                                        Node l,
                                        bool isRev,
                                        SkolemCache* skc,
                                        std::vector<Node>& newSkolems)
{
  Assert(l.getType().isInteger());
  NodeManager* nm = NodeManager::currentNM();
  Node n = isRev ? nm->mkNode(SUB, nm->mkNode(STRING_LENGTH, x), l) : l;
  Node sk1 = skc->mkSkolemCached(x, n, SkolemCache::SK_PREFIX, "dc_spt1");
  newSkolems.push_back(sk1);
  Node sk2 = skc->mkSkolemCached(x, n, SkolemCache::SK_SUFFIX_REM, "dc_spt2");
  newSkolems.push_back(sk2);
  Node conc = x.eqNode(nm->mkNode(STRING_CONCAT, sk1, sk2));
  // add the length constraint to the conclusion
  Node lc = nm->mkNode(STRING_LENGTH, isRev ? sk2 : sk1).eqNode(l);
  return nm->mkNode(AND, conc, lc);
}

void CoreSolver::getNormalForms(Node eqc,
                                std::vector<NormalForm>& normal_forms,
                                std::map<Node, unsigned>& term_to_nf_index,
                                TypeNode stype)
{
  Node emp = Word::mkEmptyWord(stype);
  //constant for equivalence class
  Node eqc_non_c = eqc;
  Trace("strings-process-debug") << "Get normal forms " << eqc << std::endl;
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, ee );
  while( !eqc_i.isFinished() ){
    Node n = (*eqc_i);
    if( !d_bsolver.isCongruent(n) ){
      Kind nk = n.getKind();
      bool isCLike = utils::isConstantLike(n);
      if (isCLike || nk == STRING_CONCAT)
      {
        Trace("strings-process-debug") << "Get Normal Form : Process term " << n << " in eqc " << eqc << std::endl;
        NormalForm nf_curr;
        if (isCLike)
        {
          nf_curr.init(n);
        }
        else if (nk == STRING_CONCAT)
        {
          // set the base to n, we construct the other portions of nf_curr in
          // the following.
          nf_curr.d_base = n;
          for( unsigned i=0; i<n.getNumChildren(); i++ ) {
            Node nr = ee->getRepresentative( n[i] );
            // get the normal form for the component
            NormalForm& nfr = getNormalForm(nr);
            std::vector<Node>& nfrv = nfr.d_nf;
            Trace("strings-process-debug")
                << "Normalizing subterm " << n[i] << " = " << nr
                << ", which is " << nfrv << std::endl;
            unsigned orig_size = nf_curr.d_nf.size();
            unsigned add_size = nfrv.size();
            //if not the empty string, add to current normal form
            if (!nfrv.empty())
            {
              // if in a build with assertions, we run the following block,
              // which checks that normal forms do not have concat terms.
              if (Configuration::isAssertionBuild())
              {
                for (const Node& nn : nfrv)
                {
                  if (TraceIsOn("strings-error"))
                  {
                    if (nn.getKind() == STRING_CONCAT)
                    {
                      Trace("strings-error")
                          << "Strings::Error: From eqc = " << eqc << ", " << n
                          << " index " << i << ", bad normal form : ";
                      for (unsigned rr = 0; rr < nfrv.size(); rr++)
                      {
                        Trace("strings-error") << nfrv[rr] << " ";
                      }
                      Trace("strings-error") << std::endl;
                    }
                  }
                  Assert(nn.getKind() != kind::STRING_CONCAT);
                }
              }
              nf_curr.d_nf.insert(nf_curr.d_nf.end(), nfrv.begin(), nfrv.end());
            }
            // Track explanation for the normal form. This is in two parts.
            // First, we must carry the explanation of the normal form computed
            // for the representative nr.
            for (const Node& exp : nfr.d_exp)
            {
              // The explanation is only relevant for the subsegment it was
              // previously relevant for, shifted now based on its relative
              // placement in the normal form of n.
              nf_curr.addToExplanation(
                  exp,
                  orig_size + nfr.d_expDep[exp][false],
                  orig_size + (add_size - nfr.d_expDep[exp][true]));
            }
            // Second, must explain that the component n[i] is equal to the
            // base of the normal form for nr.
            Node base = nfr.d_base;
            if (base != n[i])
            {
              Node eq = n[i].eqNode(base);
              // The equality is relevant for the entire current segment
              nf_curr.addToExplanation(eq, orig_size, orig_size + add_size);
            }
          }
          // Now that we are finished with the loop, we convert forward indices
          // to reverse indices in the explanation dependency information
          int total_size = nf_curr.d_nf.size();
          for (std::pair<const Node, std::map<bool, unsigned> >& ed :
               nf_curr.d_expDep)
          {
            ed.second[true] = total_size - ed.second[true];
            Assert(ed.second[true] >= 0);
          }
        }
        //if not equal to self
        std::vector<Node>& currv = nf_curr.d_nf;
        if (currv.size() > 1
            || (currv.size() == 1 && utils::isConstantLike(currv[0])))
        {
          // if in a build with assertions, check that normal form is acyclic
          if (Configuration::isAssertionBuild())
          {
            if (currv.size() > 1)
            {
              for (unsigned i = 0; i < currv.size(); i++)
              {
                if (TraceIsOn("strings-error"))
                {
                  Trace("strings-error") << "Cycle for normal form ";
                  utils::printConcatTrace(currv, "strings-error");
                  Trace("strings-error") << "..." << currv[i] << std::endl;
                }
                Assert(!d_state.areEqual(currv[i], n));
              }
            }
          }
          term_to_nf_index[n] = normal_forms.size();
          normal_forms.push_back(nf_curr);
        }else{
          //this was redundant: combination of self + empty string(s)
          Node nn = currv.size() == 0 ? emp : currv[0];
          Assert(d_state.areEqual(nn, eqc));
        }
      }else{
        eqc_non_c = n;
      }
    }
    else
    {
      Trace("strings-process-debug")
          << "Get Normal Form : term " << n << " in eqc " << eqc
          << " is congruent" << std::endl;
    }
    ++eqc_i;
  }

  if( normal_forms.empty() ) {
    Trace("strings-solve-debug2") << "construct the normal form" << std::endl;
    // This case happens when there are no non-trivial normal forms for this
    // equivalence class. For example, given assertions:
    //   { x = y ++ z, x = y, z = "" }
    // The equivalence class of { x, y, y ++ z } is such that the normal form
    // of all terms is a variable (either x or y) in the equivalence class
    // itself. Thus, the normal form of this equivalence class can be assigned
    // to one of these variables.
    // We use a non-concatenation term among the terms in this equivalence
    // class, which is stored in eqc_non_c. The reason is this does not require
    // an explanation, whereas e.g. y ++ z would require the explanation z = ""
    // to justify its normal form is y.
    Assert(eqc_non_c.getKind() != STRING_CONCAT);
    NormalForm nf_triv;
    nf_triv.init(eqc_non_c);
    normal_forms.push_back(nf_triv);
  }else{
    if(TraceIsOn("strings-solve")) {
      Trace("strings-solve") << "--- Normal forms for equivalance class " << eqc << " : " << std::endl;
      for (unsigned i = 0, size = normal_forms.size(); i < size; i++)
      {
        NormalForm& nf = normal_forms[i];
        Trace("strings-solve") << "#" << i << " (from " << nf.d_base << ") : ";
        for (unsigned j = 0, sizej = nf.d_nf.size(); j < sizej; j++)
        {
          if(j>0) {
            Trace("strings-solve") << ", ";
          }
          Trace("strings-solve") << nf.d_nf[j];
        }
        Trace("strings-solve") << std::endl;
        Trace("strings-solve") << "   Explanation is : ";
        if (nf.d_exp.size() == 0)
        {
          Trace("strings-solve") << "NONE";
        } else {
          for (unsigned j = 0, sizej = nf.d_exp.size(); j < sizej; j++)
          {
            if(j>0) {
              Trace("strings-solve") << " AND ";
            }
            Trace("strings-solve") << nf.d_exp[j];
          }
          Trace("strings-solve") << std::endl;
          Trace("strings-solve") << "WITH DEPENDENCIES : " << std::endl;
          for (unsigned j = 0, sizej = nf.d_exp.size(); j < sizej; j++)
          {
            Node exp = nf.d_exp[j];
            Trace("strings-solve") << "   " << exp << " -> ";
            Trace("strings-solve") << nf.d_expDep[exp][false] << ",";
            Trace("strings-solve") << nf.d_expDep[exp][true] << std::endl;
          }
        }
        Trace("strings-solve") << std::endl;
      }
    } else {
      Trace("strings-solve") << "--- Single normal form for equivalence class " << eqc << std::endl;
    }
  }
}

void CoreSolver::processNEqc(Node eqc,
                             std::vector<NormalForm>& normal_forms,
                             TypeNode stype,
                             std::vector<CoreInferInfo>& pinfer)
{
  if (normal_forms.size() <= 1)
  {
    return;
  }
  // if equivalence class is constant, approximate as containment, infer
  // conflicts
  Node c = d_bsolver.getConstantEqc(eqc);
  // compute normal forms that are effectively unique
  std::unordered_map<Node, size_t> nfCache;
  std::vector<size_t> nfIndices;
  bool hasConstIndex = false;
  for (size_t i = 0, nnforms = normal_forms.size(); i < nnforms; i++)
  {
    NormalForm& nfi = normal_forms[i];
    Node ni = d_termReg.mkNConcat(nfi.d_nf, stype);
    if (nfCache.find(ni) == nfCache.end())
    {
      // If the equivalence class is entailed to be constant, check
      // if the normal form cannot be contained in that constant.
      if (!c.isNull())
      {
        int firstc, lastc;
        if (!StringsEntail::canConstantContainList(c, nfi.d_nf, firstc, lastc))
        {
          Node n = nfi.d_base;
          std::vector<Node> exp(nfi.d_exp.begin(), nfi.d_exp.end());
          //conflict
          Trace("strings-solve") << "Normal form for " << n << " cannot be contained in constant " << c << std::endl;
          // conflict, explanation is:
          //  n = base ^ base = c ^ relevant porition of ( n = N[n] )
          // Notice although not implemented, this can be minimized based on
          // firstc/lastc, normal_forms_exp_depend.
          d_bsolver.explainConstantEqc(n, eqc, exp);
          d_im.sendInference(exp, d_false, InferenceId::STRINGS_N_NCTN);
          // conflict, finished
          return;
        }
      }

      nfCache[ni] = i;
      if (ni.isConst())
      {
        hasConstIndex = true;
        nfIndices.insert(nfIndices.begin(), i);
      }
      else
      {
        nfIndices.push_back(i);
      }
    }
  }
  size_t nnfs = nfIndices.size();
  Trace("strings-solve") << "CoreSolver::processNEqc: " << nnfs << "/"
                         << normal_forms.size() << " normal forms are unique."
                         << std::endl;

  // loop over all pairs
  for (unsigned i = 0; i < nnfs - 1; i++)
  {
    //unify each normalform[j] with normal_forms[i]
    for (unsigned j = i + 1; j < nnfs; j++)
    {
      NormalForm& nfi = normal_forms[nfIndices[i]];
      NormalForm& nfj = normal_forms[nfIndices[j]];
      //ensure that normal_forms[i] and normal_forms[j] are the same modulo equality, add to pinfer if not
      Trace("strings-solve") << "Strings: Process normal form #" << i << " against #" << j << "..." << std::endl;
      if (isNormalFormPair(nfi.d_base, nfj.d_base))
      {
        Trace("strings-solve") << "Strings: Already cached." << std::endl;
        continue;
      }
      // process the reverse direction first (check for easy conflicts and
      // inferences)
      unsigned rindex = 0;
      nfi.reverse();
      nfj.reverse();
      processSimpleNEq(nfi, nfj, rindex, true, 0, pinfer, stype);
      nfi.reverse();
      nfj.reverse();
      if (d_im.hasProcessed())
      {
        break;
      }
      // AJR: for less aggressive endpoint inference
      // rindex = 0;

      unsigned index = 0;
      processSimpleNEq(nfi, nfj, index, false, rindex, pinfer, stype);
      if (d_im.hasProcessed())
      {
        break;
      }
    }
    if (hasConstIndex || d_im.hasProcessed())
    {
      break;
    }
  }
  if (d_state.isInConflict())
  {
    // conflict, we are done
    return;
  }
  // Go back and check for normal form equality conflicts. These take
  // precedence over any facts and lemmas.
  for (const std::pair<const Node, size_t>& ni : nfCache)
  {
    for (const std::pair<const Node, size_t>& nj : nfCache)
    {
      if (ni.first >= nj.first)
      {
        // avoid duplicate comparisons
        continue;
      }
      Node eq = ni.first.eqNode(nj.first);
      eq = rewrite(eq);
      if (eq == d_false)
      {
        std::vector<Node> exp;
        NormalForm& nfi = normal_forms[ni.second];
        NormalForm& nfj = normal_forms[nj.second];
        exp.insert(exp.end(), nfi.d_exp.begin(), nfi.d_exp.end());
        exp.insert(exp.end(), nfj.d_exp.begin(), nfj.d_exp.end());
        exp.push_back(nfi.d_base.eqNode(nfj.d_base));
        d_im.sendInference(exp, d_false, InferenceId::STRINGS_N_EQ_CONF);
        return;
      }
    }
    if (d_im.hasProcessed())
    {
      break;
    }
  }
}

void CoreSolver::processSimpleNEq(NormalForm& nfi,
                                  NormalForm& nfj,
                                  unsigned& index,
                                  bool isRev,
                                  unsigned rproc,
                                  std::vector<CoreInferInfo>& pinfer,
                                  TypeNode stype)
{
  NodeManager* nm = NodeManager::currentNM();
  Node emp = Word::mkEmptyWord(stype);

  const std::vector<Node>& nfiv = nfi.d_nf;
  const std::vector<Node>& nfjv = nfj.d_nf;
  Assert(rproc <= nfiv.size() && rproc <= nfjv.size());
  while (true)
  {
    bool lhsDone = (index == (nfiv.size() - rproc));
    bool rhsDone = (index == (nfjv.size() - rproc));
    if (lhsDone && rhsDone)
    {
      // We are done with both normal forms
      break;
    }
    else if (lhsDone || rhsDone)
    {
      // Only one side is done so the remainder of the other side must be empty
      NormalForm& nfk = index == (nfiv.size() - rproc) ? nfj : nfi;
      std::vector<Node>& nfkv = nfk.d_nf;
      unsigned index_k = index;
      std::vector<Node> curr_exp;
      NormalForm::getExplanationForPrefixEq(nfi, nfj, -1, -1, curr_exp);
      while (!d_state.isInConflict() && index_k < (nfkv.size() - rproc))
      {
        // can infer that this string must be empty
        Node eq = nfkv[index_k].eqNode(emp);
        Assert(!d_state.areEqual(emp, nfkv[index_k]));
        d_im.sendInference(curr_exp, eq, InferenceId::STRINGS_N_ENDPOINT_EMP, isRev);
        index_k++;
      }
      break;
    }

    // We have inferred that the normal forms up to position `index` are
    // equivalent. Below, we refer to the components at the current position of
    // the normal form as `x` and `y`.
    //
    // E.g. x ++ ... = y ++ ...
    Node x = nfiv[index];
    Node y = nfjv[index];
    Trace("strings-solve-debug")
        << "Process " << x << " ... " << y << std::endl;

    // require checking equal here, usually x == y, but this also holds the
    // case of (str.unit a) and (str.unit b) for distinct a, b, where we do
    // not want to unify these terms here.
    if (d_state.areEqual(x, y))
    {
      // The normal forms have the same term at the current position. We just
      // continue with the next index. By construction of the normal forms, we
      // end up in this case if the two components are equal according to the
      // equality engine (i.e. we cannot have different x and y terms that are
      // equal in the equality engine).
      //
      // E.g. x ++ x' ++ ... = x ++ y' ++ ... ---> x' ++ ... = y' ++ ...
      Trace("strings-solve-debug")
          << "Simple Case 1 : strings are equal" << std::endl;
      index++;
      continue;
    }

    std::vector<Node> lenExp;
    Node xLenTerm = d_state.getLength(x, lenExp);
    Node yLenTerm = d_state.getLength(y, lenExp);

    if (d_state.areEqual(xLenTerm, yLenTerm))
    {
      std::vector<Node> ant;
      NormalForm::getExplanationForPrefixEq(nfi, nfj, index, index, ant);
      if (x.isConst() && y.isConst())
      {
        // if both are constant, it's just a constant conflict
        d_im.sendInference(ant, d_false, InferenceId::STRINGS_N_CONST, isRev, true);
        return;
      }
      // `x` and `y` have the same length. We infer that the two components
      // have to be the same.
      //
      // E.g. x ++ ... = y ++ ... ^ len(x) = len(y) ---> x = y
      Trace("strings-solve-debug")
          << "Simple Case 2 : string lengths are equal" << std::endl;
      Node eq = x.eqNode(y);
      d_im.addToExplanation(xLenTerm, yLenTerm, lenExp);
      // set the explanation for length
      Node lant = utils::mkAnd(lenExp);
      ant.push_back(lant);
      d_im.sendInference(ant, eq, InferenceId::STRINGS_N_UNIFY, isRev);
      break;
    }
    else if ((!x.isConst() && index == nfiv.size() - rproc - 1)
             || (!y.isConst() && index == nfjv.size() - rproc - 1))
    {
      // We have reached the last component in one of the normal forms and it
      // is not a constant. Thus, the last component must be equal to the
      // remainder of the other normal form.
      //
      // E.g. x = y ++ y' ---> x = y ++ y'
      Trace("strings-solve-debug")
          << "Simple Case 3 : at endpoint" << std::endl;
      Node eqn[2];
      for (unsigned r = 0; r < 2; r++)
      {
        const NormalForm& nfk = r == 0 ? nfi : nfj;
        const std::vector<Node>& nfkv = nfk.d_nf;
        std::vector<Node> eqnc;
        for (unsigned i = index, size = (nfkv.size() - rproc); i < size; i++)
        {
          if (isRev)
          {
            eqnc.insert(eqnc.begin(), nfkv[i]);
          }
          else
          {
            eqnc.push_back(nfkv[i]);
          }
        }
        eqn[r] = d_termReg.mkNConcat(eqnc, stype);
      }
      Trace("strings-solve-debug")
          << "Endpoint eq check: " << eqn[0] << " " << eqn[1] << std::endl;
      if (!d_state.areEqual(eqn[0], eqn[1]))
      {
        std::vector<Node> antec;
        NormalForm::getExplanationForPrefixEq(nfi, nfj, -1, -1, antec);
        d_im.sendInference(antec,
                           eqn[0].eqNode(eqn[1]),
                           InferenceId::STRINGS_N_ENDPOINT_EQ,
                           isRev,
                           true);
      }
      else
      {
        Assert(nfiv.size() == nfjv.size());
        index = nfiv.size() - rproc;
      }
      break;
    }
    else if (x.isConst() && y.isConst())
    {
      // Constants in both normal forms.
      //
      // E.g. "abc" ++ ... = "ab" ++ ...
      size_t lenX = Word::getLength(x);
      size_t lenY = Word::getLength(y);
      Trace("strings-solve-debug")
          << "Simple Case 4 : Const Split : " << x << " vs " << y
          << " at index " << index << ", isRev = " << isRev << std::endl;
      size_t minLen = std::min(lenX, lenY);
      bool isSameFix =
          isRev ? Word::rstrncmp(x, y, minLen) : Word::strncmp(x, y, minLen);
      if (isSameFix)
      {
        // The shorter constant is a prefix/suffix of the longer constant. We
        // split the longer constant into the shared part and the remainder and
        // continue from there.
        //
        // E.g. "abc" ++ x' ++ ... = "ab" ++ y' ++ ... --->
        //      "c" ++ x' ++ ... = y' ++ ...
        bool xShorter = lenX < lenY;
        NormalForm& nfl = xShorter ? nfj : nfi;
        Node cl = xShorter ? y : x;
        Node ns = xShorter ? x : y;

        Node remainderStr;
        if (isRev)
        {
          size_t newlen = std::max(lenX, lenY) - minLen;
          remainderStr = Word::substr(cl, 0, newlen);
        }
        else
        {
          remainderStr = Word::substr(cl, minLen);
        }
        Trace("strings-solve-debug-test")
            << "Break normal form of " << cl << " into " << ns << ", "
            << remainderStr << std::endl;
        nfl.splitConstant(index, ns, remainderStr);
        index++;
        continue;
      }
      else
      {
        // Conflict because the shorter constant is not a prefix/suffix of the
        // other.
        //
        // E.g. "abc" ++ ... = "bc" ++ ... ---> conflict
        std::vector<Node> antec;
        NormalForm::getExplanationForPrefixEq(nfi, nfj, index, index, antec);
        d_im.sendInference(antec, d_false, InferenceId::STRINGS_N_CONST, isRev, true);
        break;
      }
    }

    // The candidate inference "info"
    CoreInferInfo info(InferenceId::UNKNOWN);
    InferInfo& iinfo = info.d_infer;
    info.d_index = index;
    // for debugging
    info.d_i = nfi.d_base;
    info.d_j = nfj.d_base;
    info.d_rev = isRev;
    Assert(index < nfiv.size() - rproc && index < nfjv.size() - rproc);
    if (!d_state.areDisequal(xLenTerm, yLenTerm) && !d_state.areEqual(xLenTerm, yLenTerm)
        && !x.isConst()
        && !y.isConst())  // AJR: remove the latter 2 conditions?
    {
      // We don't know whether `x` and `y` have the same length or not. We
      // split on whether they are equal or not (note that splitting on
      // equality between strings is worse since it is harder to process).
      //
      // E.g. x ++ ... = y ++ ... ---> (len(x) = len(y)) v (len(x) != len(y))
      Trace("strings-solve-debug")
          << "Non-simple Case 1 : string lengths neither equal nor disequal"
          << std::endl;
      Node lenEq = nm->mkNode(EQUAL, xLenTerm, yLenTerm);
      lenEq = rewrite(lenEq);
      iinfo.d_conc = nm->mkNode(OR, lenEq, lenEq.negate());
      iinfo.setId(InferenceId::STRINGS_LEN_SPLIT);
      info.d_infer.d_pendingPhase[lenEq] = true;
      pinfer.push_back(info);
      break;
    }

    Trace("strings-solve-debug")
        << "Non-simple Case 2 : must compare strings" << std::endl;
    int lhsLoopIdx = -1;
    int rhsLoopIdx = -1;
    if (detectLoop(nfi, nfj, index, lhsLoopIdx, rhsLoopIdx, rproc))
    {
      // We are dealing with a looping word equation.
      // Note we could make this code also run in the reverse direction, but
      // this is not implemented currently.
      if (!isRev)
      {
        // add temporarily to the antecedant of iinfo.
        NormalForm::getExplanationForPrefixEq(nfi, nfj, -1, -1, iinfo.d_premises);
        ProcessLoopResult plr =
            processLoop(lhsLoopIdx != -1 ? nfi : nfj,
                        lhsLoopIdx != -1 ? nfj : nfi,
                        lhsLoopIdx != -1 ? lhsLoopIdx : rhsLoopIdx,
                        index,
                        info);
        if (plr == ProcessLoopResult::INFERENCE)
        {
          pinfer.push_back(info);
          break;
        }
        else if (plr == ProcessLoopResult::CONFLICT)
        {
          break;
        }
        Assert(plr == ProcessLoopResult::SKIPPED);
        // not processing an inference here, undo changes to ant
        iinfo.d_premises.clear();
      }
    }

    // AJR: length entailment here?
    if (x.isConst() || y.isConst())
    {
      // Below, we deal with the case where `x` or `y` is a constant string. We
      // refer to the non-constant component as `nc` below.
      //
      // E.g. "abc" ++ ... = nc ++ ...
      Assert(!x.isConst() || !y.isConst());
      NormalForm& nfc = x.isConst() ? nfi : nfj;
      const std::vector<Node>& nfcv = nfc.d_nf;
      NormalForm& nfnc = x.isConst() ? nfj : nfi;
      const std::vector<Node>& nfncv = nfnc.d_nf;
      Node nc = nfncv[index];
      Assert(!nc.isConst()) << "Other string is not constant.";
      Assert(nc.getKind() != STRING_CONCAT) << "Other string is not CONCAT.";
      // explanation for why nc is non-empty
      Node expNonEmpty = d_state.explainNonEmpty(nc);
      if (expNonEmpty.isNull())
      {
        // The non-constant side may be equal to the empty string. Split on
        // whether it is.
        //
        // E.g. "abc" ++ ... = nc ++ ... ---> (nc = "") v (nc != "")
        Node eq = nc.eqNode(emp);
        eq = rewrite(eq);
        if (eq.isConst())
        {
          // If the equality rewrites to a constant, we must use the
          // purify variable for this string to communicate that
          // we have inferred whether it is empty.
          SkolemCache* skc = d_termReg.getSkolemCache();
          Node p = skc->mkSkolemCached(nc, SkolemCache::SK_PURIFY, "lsym");
          Node pEq = p.eqNode(emp);
          // should not be constant
          Assert(!rewrite(pEq).isConst());
          // infer the purification equality, and the (dis)equality
          // with the empty string in the direction that the rewriter
          // inferred
          iinfo.d_conc = nm->mkNode(
              AND, p.eqNode(nc), !eq.getConst<bool>() ? pEq.negate() : pEq);
          iinfo.setId(InferenceId::STRINGS_INFER_EMP);
        }
        else
        {
          iinfo.d_conc = nm->mkNode(OR, eq, eq.negate());
          iinfo.setId(InferenceId::STRINGS_LEN_SPLIT_EMP);
        }
        pinfer.push_back(info);
        break;
      }

      // At this point, we know that `nc` is non-empty, so we add expNonEmpty
      // to our explanation below. We do this after adding other parts of the
      // explanation for consistency with other inferences.

      size_t ncIndex = index + 1;
      Node nextConstStr = nfnc.collectConstantStringAt(ncIndex);
      if (!nextConstStr.isNull())
      {
        // We are in the case where we have a constant after `nc`, so we
        // split `nc`.
        //
        // E.g. "abc" ++ ... = nc ++ "b" ++ ... ---> nc = "a" ++ k
        size_t cIndex = index;
        Node stra = nfc.collectConstantStringAt(cIndex);
        Assert(!stra.isNull());
        stra = rewrite(stra);
        Assert(stra.isConst());
        Node strb = rewrite(nextConstStr);
        Assert(strb.isConst());

        // Since `nc` is non-empty, we use the non-empty overlap
        size_t p = getSufficientNonEmptyOverlap(stra, strb, isRev);

        // If we can't split off more than a single character from the
        // constant, we might as well do regular constant/non-constant
        // inference (see below).
        if (p > 1)
        {
          NormalForm::getExplanationForPrefixEq(
              nfc, nfnc, cIndex, ncIndex, iinfo.d_premises);
          iinfo.d_premises.push_back(expNonEmpty);
          // make the conclusion
          SkolemCache* skc = d_termReg.getSkolemCache();
          Node xcv =
              nm->mkNode(STRING_CONCAT, isRev ? strb : nc, isRev ? nc : strb);
          std::vector<Node> newSkolems;
          iinfo.d_conc = getConclusion(
              xcv, stra, PfRule::CONCAT_CPROP, isRev, skc, newSkolems);
          Assert(newSkolems.size() == 1);
          iinfo.d_skolems[LENGTH_SPLIT].push_back(newSkolems[0]);
          iinfo.setId(InferenceId::STRINGS_SSPLIT_CST_PROP);
          iinfo.d_idRev = isRev;
          pinfer.push_back(info);
          break;
        }
      }

      // Since none of the other inferences apply, we just infer that `nc` has
      // to start with the first character of the constant.
      //
      // E.g. "abc" ++ ... = nc ++ ... ---> nc = "a" ++ k
      SkolemCache* skc = d_termReg.getSkolemCache();
      std::vector<Node> newSkolems;
      iinfo.d_conc = getConclusion(
          nc, nfcv[index], PfRule::CONCAT_CSPLIT, isRev, skc, newSkolems);
      NormalForm::getExplanationForPrefixEq(
          nfi, nfj, index, index, iinfo.d_premises);
      iinfo.d_premises.push_back(expNonEmpty);
      Assert(newSkolems.size() == 1);
      iinfo.d_skolems[LENGTH_SPLIT].push_back(newSkolems[0]);
      iinfo.setId(InferenceId::STRINGS_SSPLIT_CST);
      iinfo.d_idRev = isRev;
      pinfer.push_back(info);
      break;
    }

    // Below, we deal with the case where `x` and `y` are two non-constant
    // terms of different lengths. In this case, we have to split on which term
    // is a prefix/suffix of the other.
    //
    // E.g. x ++ ... = y ++ ... ---> (x = y ++ k) v (y = x ++ k)
    Assert(d_state.areDisequal(xLenTerm, yLenTerm));
    Assert(!x.isConst());
    Assert(!y.isConst());

    int32_t lentTestSuccess = -1;
    Node lenConstraint;
    if (options().strings.stringCheckEntailLen)
    {
      // If length entailment checks are enabled, we can save the case split by
      // inferring that `x` has to be longer than `y` or vice-versa.
      for (size_t e = 0; e < 2; e++)
      {
        Node t = e == 0 ? x : y;
        // do not infer constants are larger than variables
        if (!t.isConst())
        {
          Node lt1 = e == 0 ? xLenTerm : yLenTerm;
          Node lt2 = e == 0 ? yLenTerm : xLenTerm;
          Node entLit = rewrite(nm->mkNode(GT, lt1, lt2));
          std::pair<bool, Node> et = d_state.entailmentCheck(
              options::TheoryOfMode::THEORY_OF_TYPE_BASED, entLit);
          if (et.first)
          {
            Trace("strings-entail")
                << "Strings entailment : " << entLit
                << " is entailed in the current context." << std::endl;
            Trace("strings-entail")
                << "  explanation was : " << et.second << std::endl;
            lentTestSuccess = e;
            lenConstraint = entLit;
            // Its not explained by the equality engine of this class, so its
            // marked as not being explained. The length constraint is
            // additionally being saved and added to the length constraint
            // vector lcVec below, which is added to iinfo.d_ant below. Length
            // constraints are being added as the last antecedant for the sake
            // of proof reconstruction, which expect length constraints to come
            // last.
            iinfo.d_noExplain.push_back(lenConstraint);
            break;
          }
        }
      }
    }
    // lcVec stores the length constraint portion of the antecedant.
    std::vector<Node> lcVec;
    if (lenConstraint.isNull())
    {
      // will do split on length
      lenConstraint = nm->mkNode(EQUAL, xLenTerm, yLenTerm).negate();
      lcVec.push_back(lenConstraint);
    }
    else
    {
      utils::flattenOp(AND, lenConstraint, lcVec);
    }

    NormalForm::getExplanationForPrefixEq(nfi, nfj, index, index, iinfo.d_premises);
    // Add premises for x != "" ^ y != ""
    for (unsigned xory = 0; xory < 2; xory++)
    {
      Node t = xory == 0 ? x : y;
      Node tnz = d_state.explainNonEmpty(t);
      if (!tnz.isNull())
      {
        lcVec.push_back(tnz);
      }
      else
      {
        tnz = x.eqNode(emp).negate();
        lcVec.push_back(tnz);
        iinfo.d_noExplain.push_back(tnz);
      }
    }
    SkolemCache* skc = d_termReg.getSkolemCache();
    std::vector<Node> newSkolems;
    // make the conclusion
    if (lentTestSuccess == -1)
    {
      iinfo.setId(InferenceId::STRINGS_SSPLIT_VAR);
      iinfo.d_conc =
          getConclusion(x, y, PfRule::CONCAT_SPLIT, isRev, skc, newSkolems);
    }
    else if (lentTestSuccess == 0)
    {
      iinfo.setId(InferenceId::STRINGS_SSPLIT_VAR_PROP);
      iinfo.d_conc =
          getConclusion(x, y, PfRule::CONCAT_LPROP, isRev, skc, newSkolems);
    }
    else
    {
      Assert(lentTestSuccess == 1);
      iinfo.setId(InferenceId::STRINGS_SSPLIT_VAR_PROP);
      iinfo.d_conc =
          getConclusion(y, x, PfRule::CONCAT_LPROP, isRev, skc, newSkolems);
    }
    // add the length constraint(s) as the last antecedant
    Node lc = utils::mkAnd(lcVec);
    iinfo.d_premises.push_back(lc);
    iinfo.d_idRev = isRev;
    pinfer.push_back(info);
    break;
  }
}

bool CoreSolver::detectLoop(NormalForm& nfi,
                               NormalForm& nfj,
                               int index,
                               int& loop_in_i,
                               int& loop_in_j,
                               unsigned rproc)
{
  int has_loop[2] = { -1, -1 };
  for (unsigned r = 0; r < 2; r++)
  {
    NormalForm& nf = r == 0 ? nfi : nfj;
    NormalForm& nfo = r == 0 ? nfj : nfi;
    std::vector<Node>& nfv = nf.d_nf;
    std::vector<Node>& nfov = nfo.d_nf;
    if (nfov[index].isConst())
    {
      continue;
    }
    for (unsigned lp = index + 1, lpEnd = nfv.size() - rproc; lp < lpEnd; lp++)
    {
      if (nfv[lp] == nfov[index])
      {
        has_loop[r] = lp;
        break;
      }
    }
  }
  if( has_loop[0]!=-1 || has_loop[1]!=-1 ) {
    loop_in_i = has_loop[0];
    loop_in_j = has_loop[1];
    return true;
  } else {
    Trace("strings-solve-debug") << "No loops detected." << std::endl;
    return false;
  }
}

//xs(zy)=t(yz)xr
CoreSolver::ProcessLoopResult CoreSolver::processLoop(NormalForm& nfi,
                                                      NormalForm& nfj,
                                                      int loop_index,
                                                      int index,
                                                      CoreInferInfo& info)
{
  NodeManager* nm = NodeManager::currentNM();
  Node conc;
  const std::vector<Node>& veci = nfi.d_nf;
  const std::vector<Node>& vecoi = nfj.d_nf;

  TypeNode stype = veci[loop_index].getType();

  if (options().strings.stringProcessLoopMode
      == options::ProcessLoopMode::ABORT)
  {
    throw LogicException("Looping word equation encountered.");
  }
  else if (options().strings.stringProcessLoopMode
               == options::ProcessLoopMode::NONE
           || stype.isSequence())
  {
    // note we cannot convert looping word equations into regular expressions if
    // we are handling sequences, since there is no analog for regular
    // expressions over sequences currently
    d_modelUnsoundId = IncompleteId::STRINGS_LOOP_SKIP;
    return ProcessLoopResult::SKIPPED;
  }

  Trace("strings-loop") << "Detected possible loop for " << veci[loop_index]
                        << std::endl;
  Trace("strings-loop") << " ... (X)= " << vecoi[index] << std::endl;
  Trace("strings-loop") << " ... T(Y.Z)= ";
  std::vector<Node> vec_t(veci.begin() + index, veci.begin() + loop_index);
  Node t_yz = d_termReg.mkNConcat(vec_t, stype);
  Trace("strings-loop") << " (" << t_yz << ")" << std::endl;
  Trace("strings-loop") << " ... S(Z.Y)= ";
  std::vector<Node> vec_s(vecoi.begin() + index + 1, vecoi.end());
  Node s_zy = d_termReg.mkNConcat(vec_s, stype);
  Trace("strings-loop") << s_zy << std::endl;
  Trace("strings-loop") << " ... R= ";
  std::vector<Node> vec_r(veci.begin() + loop_index + 1, veci.end());
  Node r = d_termReg.mkNConcat(vec_r, stype);
  Trace("strings-loop") << r << std::endl;

  Node emp = Word::mkEmptyWord(stype);

  InferInfo& iinfo = info.d_infer;
  if (s_zy.isConst() && r.isConst() && r != emp)
  {
    int c;
    bool flag = true;
    if (s_zy.getConst<String>().tailcmp(r.getConst<String>(), c))
    {
      if (c >= 0)
      {
        s_zy = Word::substr(s_zy, 0, c);
        r = emp;
        vec_r.clear();
        Trace("strings-loop") << "Strings::Loop: Refactor S(Z.Y)= " << s_zy
                              << ", c=" << c << std::endl;
        flag = false;
      }
    }
    if (flag)
    {
      Trace("strings-loop") << "Strings::Loop: tails are different."
                            << std::endl;
      d_im.sendInference(
          iinfo.d_premises, conc, InferenceId::STRINGS_FLOOP_CONFLICT, false, true);
      return ProcessLoopResult::CONFLICT;
    }
  }

  Node split_eq;
  for (unsigned i = 0; i < 2; i++)
  {
    Node t = i == 0 ? veci[loop_index] : t_yz;
    split_eq = t.eqNode(emp);
    Node split_eqr = rewrite(split_eq);
    // the equality could rewrite to false
    if (!split_eqr.isConst())
    {
      Node expNonEmpty = d_state.explainNonEmpty(t);
      if (expNonEmpty.isNull())
      {
        // no antecedants necessary
        iinfo.d_premises.clear();
        // try to make t equal to empty to avoid loop
        iinfo.d_conc = nm->mkNode(kind::OR, split_eq, split_eq.negate());
        iinfo.setId(InferenceId::STRINGS_LEN_SPLIT_EMP);
        return ProcessLoopResult::INFERENCE;
      }
      else
      {
        iinfo.d_premises.push_back(expNonEmpty);
      }
    }
    else
    {
      Assert(!split_eqr.getConst<bool>());
    }
  }

  Node str_in_re;
  if (s_zy == t_yz && r == emp && s_zy.isConst()
      && s_zy.getConst<String>().isRepeated())
  {
    Node rep_c = Word::substr(s_zy, 0, 1);
    Trace("strings-loop") << "Special case (X)=" << vecoi[index] << " "
                          << std::endl;
    Trace("strings-loop") << "... (C)=" << rep_c << " " << std::endl;
    // special case
    str_in_re = nm->mkNode(
        STRING_IN_REGEXP,
        vecoi[index],
        nm->mkNode(REGEXP_STAR, nm->mkNode(STRING_TO_REGEXP, rep_c)));
    conc = str_in_re;
  }
  else if (t_yz.isConst())
  {
    Trace("strings-loop") << "Strings::Loop: Const Normal Breaking."
                          << std::endl;
    unsigned size = Word::getLength(t_yz);
    std::vector<Node> vconc;
    for (unsigned len = 1; len <= size; len++)
    {
      Node y = Word::substr(t_yz, 0, len);
      Node z = Word::substr(t_yz, len, size - len);
      Node restr = s_zy;
      Node cc;
      if (r != emp)
      {
        std::vector<Node> v2(vec_r);
        v2.insert(v2.begin(), y);
        v2.insert(v2.begin(), z);
        restr = d_termReg.mkNConcat(z, y);
        cc = rewrite(s_zy.eqNode(d_termReg.mkNConcat(v2, stype)));
      }
      else
      {
        cc = rewrite(s_zy.eqNode(d_termReg.mkNConcat(z, y)));
      }
      if (cc == d_false)
      {
        continue;
      }
      Node conc2 = nm->mkNode(
          STRING_IN_REGEXP,
          vecoi[index],
          nm->mkNode(
              REGEXP_CONCAT,
              nm->mkNode(STRING_TO_REGEXP, y),
              nm->mkNode(REGEXP_STAR, nm->mkNode(STRING_TO_REGEXP, restr))));
      cc = cc == d_true ? conc2 : nm->mkNode(kind::AND, cc, conc2);
      vconc.push_back(cc);
    }
    conc = vconc.size() == 0 ? Node::null() : vconc.size() == 1
                                                  ? vconc[0]
                                                  : nm->mkNode(kind::OR, vconc);
  }
  else
  {
    if (options().strings.stringProcessLoopMode
        == options::ProcessLoopMode::SIMPLE_ABORT)
    {
      throw LogicException("Normal looping word equation encountered.");
    }
    else if (options().strings.stringProcessLoopMode
             == options::ProcessLoopMode::SIMPLE)
    {
      d_modelUnsoundId = IncompleteId::STRINGS_LOOP_SKIP;
      return ProcessLoopResult::SKIPPED;
    }

    Trace("strings-loop") << "Strings::Loop: Normal Loop Breaking."
                          << std::endl;
    // right
    SkolemCache* skc = d_termReg.getSkolemCache();
    Node sk_w = skc->mkSkolem("w_loop");
    Node sk_y = skc->mkSkolem("y_loop");
    iinfo.d_skolems[LENGTH_GEQ_ONE].push_back(sk_y);
    Node sk_z = skc->mkSkolem("z_loop");
    // t1 * ... * tn = y * z
    Node conc1 = t_yz.eqNode(d_termReg.mkNConcat(sk_y, sk_z));
    // s1 * ... * sk = z * y * r
    vec_r.insert(vec_r.begin(), sk_y);
    vec_r.insert(vec_r.begin(), sk_z);
    Node conc2 = s_zy.eqNode(d_termReg.mkNConcat(vec_r, stype));
    Node conc3 = vecoi[index].eqNode(d_termReg.mkNConcat(sk_y, sk_w));
    Node restr = r == emp ? s_zy : d_termReg.mkNConcat(sk_z, sk_y);
    str_in_re =
        nm->mkNode(kind::STRING_IN_REGEXP,
                   sk_w,
                   nm->mkNode(kind::REGEXP_STAR,
                              nm->mkNode(kind::STRING_TO_REGEXP, restr)));

    std::vector<Node> vec_conc;
    vec_conc.push_back(conc1);
    vec_conc.push_back(conc2);
    vec_conc.push_back(conc3);
    vec_conc.push_back(str_in_re);
    conc = nm->mkNode(kind::AND, vec_conc);
  }  // normal case

  // we will be done
  iinfo.d_conc = conc;
  iinfo.setId(InferenceId::STRINGS_FLOOP);
  info.d_infer.d_nfPair[0] = nfi.d_base;
  info.d_infer.d_nfPair[1] = nfj.d_base;
  return ProcessLoopResult::INFERENCE;
}

void CoreSolver::processDeq(Node ni, Node nj)
{
  NodeManager* nm = NodeManager::currentNM();
  NormalForm& nfni = getNormalForm(ni);
  NormalForm& nfnj = getNormalForm(nj);

  if (nfni.d_nf.size() <= 1 && nfnj.d_nf.size() <= 1)
  {
    // If normal forms have size <=1, then we are comparing either:
    // (1) variable to variable,
    // (2) variable to constant-like (empty, constant string/seq or SEQ_UNIT),
    // (3) SEQ_UNIT to constant-like.
    // We only have to process (3) here, since disequalities of the form of (1)
    // and (2) are satisfied by construction.
    for (size_t i = 0; i < 2; i++)
    {
      NormalForm& nfc = i == 0 ? nfni : nfnj;
      if (nfc.d_nf.size() == 0)
      {
        // may need to look at the other side
        continue;
      }
      Node u = nfc.d_nf[0];
      if (u.getKind() != SEQ_UNIT && u.getKind() != STRING_UNIT)
      {
        continue;
      }
      // if the other side is constant like
      NormalForm& nfo = i == 0 ? nfnj : nfni;
      if (nfo.d_nf.size() == 0 || !utils::isConstantLike(nfo.d_nf[0]))
      {
        break;
      }
      // v is the other side (a possibly constant seq.unit term)
      Node v = nfo.d_nf[0];
      Node vc;
      if (v.isConst())
      {
        // get the list of characters (strings of length 1)
        std::vector<Node> vchars = Word::getChars(v);
        if (vchars.size() != 1)
        {
          // constant of size != 1, disequality is satisfied
          break;
        }
        // get the element of the character
        vc = Word::getNth(vchars[0], 0);
      }
      else
      {
        Assert(v.getKind() == SEQ_UNIT || v.getKind() == STRING_UNIT);
        vc = v[0];
      }
      Assert(u[0].getType() == vc.getType());
      // if already disequal, we are done
      if (d_state.areDisequal(u[0], vc))
      {
        break;
      }
      // seq.unit(x) != seq.unit(y) => x != y
      // Notice this is a special case, since the code below would justify this
      // disequality by reasoning that a component is disequal. However, the
      // disequality components are the entire disequality.
      Node deq = u.eqNode(v).notNode();
      std::vector<Node> premises;
      premises.push_back(deq);
      Assert(u[0].getType()==vc.getType());
      Node conc = u[0].eqNode(vc).notNode();
      d_im.sendInference(premises, conc, InferenceId::STRINGS_UNIT_INJ_DEQ, false, true);
      return;
    }
    Trace("strings-solve-debug") << "...trivial" << std::endl;
    return;
  }

  std::vector<Node> nfi = nfni.d_nf;
  std::vector<Node> nfj = nfnj.d_nf;

  // See if one side is constant, if so, the disequality ni != nj is satisfied
  // if it cannot contain the other side.
  //
  // E.g. "abc" != x ++ "d" ++ y
  for (uint32_t i = 0; i < 2; i++)
  {
    Node c = d_bsolver.getConstantEqc(i == 0 ? ni : nj);
    if (!c.isNull())
    {
      int findex, lindex;
      if (!StringsEntail::canConstantContainList(
              c, i == 0 ? nfj : nfi, findex, lindex))
      {
        Trace("strings-solve-debug")
            << "Disequality: constant cannot contain list" << std::endl;
        return;
      }
    }
  }

  if (processReverseDeq(nfi, nfj, ni, nj))
  {
    Trace("strings-solve-debug") << "...processed reverse" << std::endl;
    return;
  }

  nfi = nfni.d_nf;
  nfj = nfnj.d_nf;

  size_t index = 0;
  while (index < nfi.size() || index < nfj.size())
  {
    if (processSimpleDeq(nfi, nfj, ni, nj, index, false))
    {
      Trace("strings-solve-debug") << "...processed simple" << std::endl;
      return;
    }

    // We have inferred that the normal forms up to position `index` are
    // equivalent. Below, we refer to the components at the current position of
    // the normal form as `x` and `y`.
    //
    // E.g. x ++ ... = y ++ ...
    Assert(index < nfi.size() && index < nfj.size());
    Node x = nfi[index];
    Node y = nfj[index];
    Trace("strings-solve-debug")
        << "...Processing(DEQ) " << x << " " << y << std::endl;
    if (d_state.areEqual(x, y))
    {
      // The normal forms have an equivalent term at `index` in the current
      // context. We move to the next `index`.
      //
      // E.g. x ++ x' ++ ... != z ++ y' ++ ... ^ x = z
      index++;
      continue;
    }

    Assert(!x.isConst() || !y.isConst());
    std::vector<Node> lenExp;
    Node xLenTerm = d_state.getLength(x, lenExp);
    Node yLenTerm = d_state.getLength(y, lenExp);
    if (d_state.areDisequal(xLenTerm, yLenTerm))
    {
      // Below, we deal with the cases where the components at the current
      // index are of different lengths in the current context.
      //
      // E.g. x ++ x' ++ ... != y ++ y' ++ ... ^ len(x) != len(y)
      if (x.isConst() || y.isConst())
      {
        Node ck = x.isConst() ? x : y;
        Node nck = x.isConst() ? y : x;
        Node nckLenTerm = x.isConst() ? yLenTerm : xLenTerm;
        Node expNonEmpty = d_state.explainNonEmpty(nck);
        if (expNonEmpty.isNull())
        {
          // Either `x` or `y` is a constant and the other may be equal to the
          // empty string in the current context. We split on whether it
          // actually is empty in that case.
          //
          // E.g. x ++ x' ++ ... != "abc" ++ y' ++ ... ^ len(x) != len(y) --->
          //      x = "" v x != ""
          Node emp = Word::mkEmptyWord(nck.getType());
          d_im.sendSplit(nck, emp, InferenceId::STRINGS_DEQ_DISL_EMP_SPLIT);
          return;
        }

        Node firstChar = Word::getLength(ck) == 1 ? ck : Word::prefix(ck, 1);
        if (d_state.areEqual(nckLenTerm, d_one))
        {
          if (d_state.areDisequal(firstChar, nck))
          {
            // Either `x` or `y` is a constant and the other is a string of
            // length one. If the non-constant is disequal to the first
            // character of the constant in the current context, we satisfy the
            // disequality and there is nothing else to do.
            //
            // E.g. "d" ++ x' ++ ... != "abc" ++ y' ++ ... ^ len(x) = 1
            return;
          }
          else if (!d_state.areEqual(firstChar, nck))
          {
            // Either `x` or `y` is a constant and the other is a string of
            // length one. If we do not know whether the non-constant is equal
            // or disequal to the first character in the constant, we split on
            // whether it is.
            //
            // E.g. x ++ x' ++ ... != "abc" ++ y' ++ ... ^ len(x) = 1 --->
            //      x = "a" v x != "a"
            if (d_im.sendSplit(firstChar,
                               nck,
                               InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_EQ_SPLIT,
                               false))
            {
              return;
            }
          }
        }
        else
        {
          // Either `x` or `y` is a constant and it is not know whether the
          // non-empty non-constant is of length one. We split the non-constant
          // into a string of length one and the remainder.
          //
          // len(x)>=1 => x = k1 ++ k2 ^ len(k1) = 1
          SkolemCache* skc = d_termReg.getSkolemCache();
          std::vector<Node> newSkolems;
          Node conc = getDecomposeConclusion(
              nck, d_one, false, skc, newSkolems);
          Assert(newSkolems.size() == 2);
          std::vector<Node> antecLen;
          antecLen.push_back(nm->mkNode(GEQ, nckLenTerm, d_one));
          d_im.sendInference(antecLen,
                             antecLen,
                             conc,
                             InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_STRING_SPLIT,
                             false,
                             true);
          return;
        }
      }
      else
      {
        // `x` and `y` have different lengths in the current context and they
        // are both non-constants. We split them into parts that have the same
        // lengths.
        //
        // len(x) > len(y) => x = k1 ++ k2 ^ len(k1) = len(y)
        // len(y) > len(x) => y = k3 ++ k4 ^ len(k3) = len(x)
        Trace("strings-solve")
            << "Non-Simple Case 1 : add lemmas " << std::endl;
        SkolemCache* skc = d_termReg.getSkolemCache();

        for (unsigned r = 0; r < 2; r++)
        {
          Node ux = r == 0 ? x : y;
          Node uy = r == 0 ? y : x;
          Node uxLen = nm->mkNode(STRING_LENGTH, ux);
          Node uyLen = nm->mkNode(STRING_LENGTH, uy);
          // We always add the length constraint in the conclusion here
          // because the skolem needs to have length `uyLen`. If we only assert
          // that the skolem's length is greater or equal to one, we can end up
          // in a loop:
          //
          // 1. Split: x = k1 ++ k2 ^ len(k1) >= 1
          // 2. Assume: k2 = ""
          // 3. Deduce: x = k1
          //
          // After step 3, `k1` is marked congruent because `x` is the older
          // variable. So we get `x` in the normal form again.
          std::vector<Node> newSkolems;
          Node conc =
              getDecomposeConclusion(ux, uyLen, false, skc, newSkolems);
          Assert(newSkolems.size() == 2);
          Node lenConstraint = nm->mkNode(GT, uxLen, uyLen);
          Node lenConstraintr = rewrite(lenConstraint);
          // If the length constraint rewrites to false, don't bother sending
          // the lemma. If it rewrites to true, then we include it as a
          // (trivial) antecedant for the sake of consistency (for proofs).
          // It will be removed when the lemma is rewritten.
          if (lenConstraintr.isConst() && !lenConstraintr.getConst<bool>())
          {
            continue;
          }
          std::vector<Node> antecLen;
          antecLen.push_back(lenConstraint);
          d_im.sendInference(antecLen,
                             antecLen,
                             conc,
                             InferenceId::STRINGS_DEQ_DISL_STRINGS_SPLIT,
                             false,
                             true);
        }

        return;
      }
    }
    else if (d_state.areEqual(xLenTerm, yLenTerm))
    {
      // `x` and `y` have the same length in the current context. We split on
      // whether they are actually equal.
      //
      // E.g. x ++ x' ++ ... != y ++ y' ++ ... ^ len(x) = len(y) --->
      //      x = y v x != y
      Assert(!d_state.areDisequal(x, y));
      if (d_im.sendSplit(x, y, InferenceId::STRINGS_DEQ_STRINGS_EQ, false))
      {
        return;
      }
    }
    else
    {
      // It is not known whether `x` and `y` have the same length in the
      // current context. We split on whether they do.
      //
      // E.g. x ++ x' ++ ... != y ++ y' ++ ... --->
      //      len(x) = len(y) v len(x) != len(y)
      if (d_im.sendSplit(xLenTerm, yLenTerm, InferenceId::STRINGS_DEQ_LENS_EQ))
      {
        return;
      }
    }
  }
  Unreachable();
}

bool CoreSolver::processReverseDeq(std::vector<Node>& nfi,
                                   std::vector<Node>& nfj,
                                   Node ni,
                                   Node nj)
{
  // reverse normal form of i, j
  std::reverse(nfi.begin(), nfi.end());
  std::reverse(nfj.begin(), nfj.end());

  size_t index = 0;
  bool ret = processSimpleDeq(nfi, nfj, ni, nj, index, true);

  // reverse normal form of i, j
  std::reverse(nfi.begin(), nfi.end());
  std::reverse(nfj.begin(), nfj.end());

  return ret;
}

bool CoreSolver::processSimpleDeq(std::vector<Node>& nfi,
                                  std::vector<Node>& nfj,
                                  Node ni,
                                  Node nj,
                                  size_t& index,
                                  bool isRev)
{
  TypeNode stype = ni.getType();
  Node emp = Word::mkEmptyWord(stype);

  NormalForm& nfni = getNormalForm(ni);
  NormalForm& nfnj = getNormalForm(nj);
  while (index < nfi.size() || index < nfj.size())
  {
    if (index >= nfi.size() || index >= nfj.size())
    {
      // We have reached the end of one of the normal forms. Note that this
      // function only deals with two normal forms that have the same length,
      // so the remainder of the longer normal form needs to be empty. This
      // will lead to a conflict.
      //
      // E.g. px ++ x ++ ... != py ^
      //        len(px ++ x ++ ...) = len(py) --->
      //      x = "" ^ ...
      Trace("strings-solve-debug")
          << "Disequality normalize empty" << std::endl;
      // the antecedant
      std::vector<Node> ant;
      // Get the length explanation, where we do not minimize the explanation.
      // Minimizing the explanation here may return a pair of length terms
      // that are not equal in the current context, which can lead to duplicate
      // lemmas below.
      Node niLenTerm = d_state.getLengthExp(ni, ant, nfni.d_base, false);
      Node njLenTerm = d_state.getLengthExp(nj, ant, nfnj.d_base, false);
      // length is not guaranteed to hold
      Node leq = niLenTerm.eqNode(njLenTerm);
      ant.push_back(leq);
      ant.insert(ant.end(), nfni.d_exp.begin(), nfni.d_exp.end());
      ant.insert(ant.end(), nfnj.d_exp.begin(), nfnj.d_exp.end());
      std::vector<Node> cc;
      std::vector<Node>& nfk = index >= nfi.size() ? nfj : nfi;
      for (size_t k = index; k < nfk.size(); k++)
      {
        cc.push_back(nfk[k].eqNode(emp));
      }
      Node conc = NodeManager::currentNM()->mkAnd(cc);
      Assert(d_state.areEqual(niLenTerm, njLenTerm))
          << "Lengths not equal " << niLenTerm << " " << njLenTerm;
      d_im.sendInference(
          ant, {}, conc, InferenceId::STRINGS_DEQ_NORM_EMP, isRev, true);
      return true;
    }

    // We have inferred that the normal forms up to position `index` are
    // equivalent. Below, we refer to the components at the current position of
    // the normal form as `x` and `y`.
    //
    // E.g. x ++ ... = y ++ ...
    Node x = nfi[index];
    Node y = nfj[index];
    Trace("strings-solve-debug")
        << "...Processing(QED) " << x << " " << y << std::endl;
    if (d_state.areEqual(x, y))
    {
      // The normal forms have an equivalent term at `index` in the current
      // context. We move to the next `index`.
      //
      // E.g. x ++ x' ++ ... != z ++ y' ++ ... ^ x = z
      index++;
      continue;
    }

    if (!x.isConst() || !y.isConst())
    {
      std::vector<Node> lenExp;
      Node xLenTerm = d_state.getLength(x, lenExp);
      Node yLenTerm = d_state.getLength(y, lenExp);
      if (d_state.areEqual(xLenTerm, yLenTerm) && d_state.areDisequal(x, y))
      {
        // Either `x` or `y` is non-constant, the lengths are equal, and `x`
        // and `y` are disequal in the current context. The disequality is
        // satisfied and there is nothing else to do.
        //
        // E.g. x ++ x' ++ ... != y ++ y' ++ ... ^ len(x) = len(y) ^ x != y
        Trace("strings-solve")
            << "Simple Case 2 : found equal length disequal sub strings " << x
            << " " << y << std::endl;
        return true;
      }
      else
      {
        // Either `x` or `y` is non-constant but it is not known whether they
        // have the same length or are disequal. We bail out.
        //
        // E.g. x ++ x' ++ ... != y ++ y' ++ ...
        return false;
      }
    }

    // Below, we deal with the cases where both `x` and `y` are constant.
    Assert(x.isConst() && y.isConst());
    size_t xLen = Word::getLength(x);
    size_t yLen = Word::getLength(y);
    size_t shortLen = std::min(xLen, yLen);
    bool isSameFix =
        isRev ? Word::rstrncmp(x, y, shortLen) : Word::strncmp(x, y, shortLen);
    if (!isSameFix)
    {
      // `x` and `y` are constants but do not share a prefix/suffix, thus
      // satisfying the disequality. There is nothing else to do.
      //
      // E.g. "abc" ++ x' ++ ... != "d" ++ y' ++ ...
      return true;
    }

    // `x` and `y` are constants and share a prefix/suffix. We move the common
    // prefix/suffix to a separate component in the normal form.
    //
    // E.g. "abc" ++ x' ++ ... != "ab" ++ y' ++ ... --->
    //      "ab" ++ "c" ++ x' ++ ... != "ab" ++ y' ++ ...
    Node nk = xLen < yLen ? x : y;
    Node nl = xLen < yLen ? y : x;
    Node remainderStr;
    if (isRev)
    {
      remainderStr = Word::substr(nl, 0, Word::getLength(nl) - shortLen);
      Trace("strings-solve-debug-test")
          << "Rev. Break normal form of " << nl << " into " << nk << ", "
          << remainderStr << std::endl;
    }
    else
    {
      remainderStr = Word::substr(nl, shortLen);
      Trace("strings-solve-debug-test")
          << "Break normal form of " << nl << " into " << nk << ", "
          << remainderStr << std::endl;
    }
    if (xLen < yLen)
    {
      nfj.insert(nfj.begin() + index + 1, remainderStr);
      nfj[index] = nfi[index];
    }
    else
    {
      nfi.insert(nfi.begin() + index + 1, remainderStr);
      nfi[index] = nfj[index];
    }

    index++;
  }
  return false;
}

void CoreSolver::processDeqExtensionality(Node n1, Node n2)
{
  Trace("strings-deq-ext") << "Processing " << n1 << " != " << n2 << std::endl;
  // hash based on equality
  Node eq = n1 < n2 ? n1.eqNode(n2) : n2.eqNode(n1);
  NodeSet::const_iterator it = d_extDeq.find(eq);
  if (it != d_extDeq.end())
  {
    // already processed
    Trace("strings-deq-ext") << "- already processed" << std::endl;
    return;
  }
  d_extDeq.insert(eq);

  NodeManager* nm = NodeManager::currentNM();
  SkolemCache* sc = d_termReg.getSkolemCache();
  TypeNode intType = nm->integerType();
  Node k = sc->mkSkolemFun(SkolemFunId::STRINGS_DEQ_DIFF, intType, n1, n2);
  Node deq = eq.negate();
  // we could use seq.nth instead of substr
  Node ss1, ss2;
  if (n1.getType().isString())
  {
    // substring of length 1
    ss1 = nm->mkNode(STRING_SUBSTR, n1, k, d_one);
    ss2 = nm->mkNode(STRING_SUBSTR, n2, k, d_one);
  }
  else
  {
    // as an optimization, for sequences, use seq.nth
    ss1 = nm->mkNode(SEQ_NTH, n1, k);
    ss2 = nm->mkNode(SEQ_NTH, n2, k);
  }

  // disequality between nth/substr
  Node conc1 = ss1.eqNode(ss2).negate();

  // The skolem k is in the bounds of at least
  // one string/sequence
  Node len1 = nm->mkNode(STRING_LENGTH, n1);
  Node len2 = nm->mkNode(STRING_LENGTH, n2);
  Node conc2 = nm->mkNode(LEQ, d_zero, k);
  Node conc3 = nm->mkNode(LT, k, len1);
  Node lenDeq = nm->mkNode(EQUAL, len1, len2).negate();

  std::vector<Node> concs = {conc1, conc2, conc3};
  Node conc = nm->mkNode(OR, lenDeq, nm->mkAnd(concs));
  // A != B => ( seq.len(A) != seq.len(B) or
  //             ( seq.nth(A, d) != seq.nth(B, d) ^ 0 <= d < seq.len(A) ) )
  // Note that we take A != B verbatim, and do not explain it.
  d_im.sendInference(
      {deq}, {deq}, conc, InferenceId::STRINGS_DEQ_EXTENSIONALITY, false, true);
}

void CoreSolver::addNormalFormPair( Node n1, Node n2 ){
  if (n1>n2)
  {
    addNormalFormPair(n2,n1);
    return;
  }
  if( !isNormalFormPair( n1, n2 ) ){
    int index = 0;
    NodeIntMap::const_iterator it = d_nfPairs.find(n1);
    if (it != d_nfPairs.end())
    {
      index = (*it).second;
    }
    d_nfPairs[n1] = index + 1;
    if( index<(int)d_nf_pairs_data[n1].size() ){
      d_nf_pairs_data[n1][index] = n2;
    }else{
      d_nf_pairs_data[n1].push_back( n2 );
    }
    Assert(isNormalFormPair(n1, n2));
  } else {
    Trace("strings-nf-debug") << "Already a normal form pair " << n1 << " " << n2 << std::endl;
  }
}

bool CoreSolver::isNormalFormPair( Node n1, Node n2 ) {
  if (n1>n2)
  {
    return isNormalFormPair(n2,n1);
  }
  //Trace("strings-debug") << "is normal form pair. " << n1 << " " << n2 << std::endl;
  NodeIntMap::const_iterator it = d_nfPairs.find(n1);
  if (it != d_nfPairs.end())
  {
    Assert(d_nf_pairs_data.find(n1) != d_nf_pairs_data.end());
    for( int i=0; i<(*it).second; i++ ){
      Assert(i < (int)d_nf_pairs_data[n1].size());
      if( d_nf_pairs_data[n1][i]==n2 ){
        return true;
      }
    }
  }
  return false;
}

void CoreSolver::checkNormalFormsDeq()
{
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  std::map< Node, std::map< Node, bool > > processed;

  const context::CDList<Node>& deqs = d_state.getDisequalityList();

  Trace("str-deq") << "Process disequalites..." << std::endl;
  d_rlvDeq.clear();
  // for each pair of disequal strings, must determine whether their lengths
  // are equal or disequal
  for (const Node& eq : deqs)
  {
    Trace("str-deq") << "- disequality " << eq << std::endl;
    Node n[2];
    for( unsigned i=0; i<2; i++ ){
      n[i] = ee->getRepresentative( eq[i] );
    }
    if( processed[n[0]].find( n[1] )==processed[n[0]].end() ){
      processed[n[0]][n[1]] = true;
      Node lt[2];
      for (size_t i = 0; i < 2; i++)
      {
        std::vector<Node> exp;
        lt[i] = d_state.getLength(n[i], exp, false);
      }
      if (d_state.areEqual(lt[0], lt[1]))
      {
        // if they have equal lengths, we must process the disequality below
        d_rlvDeq.push_back(eq);
        Trace("str-deq") << "...relevant, lengths equal (" << lt[0] << " "
                         << lt[1] << ")" << std::endl;
      }
      else if (!d_state.areDisequal(lt[0], lt[1]))
      {
        d_im.sendSplit(lt[0], lt[1], InferenceId::STRINGS_DEQ_LENGTH_SP);
        Trace("str-deq") << "...split" << std::endl;
      }
      else
      {
        Trace("str-deq") << "...disequal length" << std::endl;
      }
    }
    else
    {
      Trace("str-deq") << "...congruent" << std::endl;
    }
  }

  if (d_im.hasProcessed())
  {
    // added splitting lemma above
    return;
  }
  for (const Node& eq : d_rlvDeq)
  {
    Assert(!d_state.isInConflict());
    // If using the sequence update solver, we always apply extensionality.
    // This is required for model soundness currently, although we could
    // investigate determining cases where the disequality is already
    // satisfied (for optimization).
    if (options().strings.stringsDeqExt
        || options().strings.seqArray != options::SeqArrayMode::NONE)
    {
      processDeqExtensionality(eq[0], eq[1]);
      continue;
    }
    // the method below requires representatives
    Node n[2];
    for (size_t i = 0; i < 2; i++)
    {
      n[i] = ee->getRepresentative(eq[i]);
    }
    if (TraceIsOn("strings-solve"))
    {
      Trace("strings-solve") << "- Compare " << n[0] << ", nf ";
      utils::printConcatTrace(getNormalForm(n[0]).d_nf, "strings-solve");
      Trace("strings-solve") << " against " << n[1] << ", nf ";
      utils::printConcatTrace(getNormalForm(n[1]).d_nf, "strings-solve");
      Trace("strings-solve") << "..." << std::endl;
    }
    processDeq(n[0], n[1]);
    if (d_im.hasProcessed())
    {
      return;
    }
  }
}

void CoreSolver::checkLengthsEqc()
{
  for (unsigned i = 0; i < d_strings_eqc.size(); i++)
  {
    TypeNode stype = d_strings_eqc[i].getType();
    NormalForm& nfi = getNormalForm(d_strings_eqc[i]);
    Trace("strings-process-debug")
        << "Process length constraints for " << d_strings_eqc[i] << std::endl;
    // check if there is a length term for this equivalence class
    EqcInfo* ei = d_state.getOrMakeEqcInfo(d_strings_eqc[i], false);
    Node llt = ei ? ei->d_lengthTerm : Node::null();
    if (llt.isNull())
    {
      Trace("strings-process-debug")
          << "No length term for eqc " << d_strings_eqc[i] << std::endl;
      continue;
    }
    // now, check if length normalization has occurred
    if (ei->d_normalizedLength.get().isNull())
    {
      Node nf = d_termReg.mkNConcat(nfi.d_nf, stype);
      if (TraceIsOn("strings-process-debug"))
      {
        Trace("strings-process-debug")
            << "  normal form is " << nf << " from base " << nfi.d_base
            << std::endl;
        Trace("strings-process-debug") << "  normal form exp is: " << std::endl;
        for (const Node& exp : nfi.d_exp)
        {
          Trace("strings-process-debug") << "   " << exp << std::endl;
        }
      }

      // if not, add the lemma
      std::vector<Node> ant;
      ant.insert(ant.end(), nfi.d_exp.begin(), nfi.d_exp.end());
      ant.push_back(llt[0].eqNode(nfi.d_base));
      Node lc = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, nf);
      Node lcr = rewrite(lc);
      Trace("strings-process-debug")
          << "Rewrote length " << lc << " to " << lcr << std::endl;
      if (!d_state.areEqual(llt, lcr))
      {
        Node eq = llt.eqNode(lc);
        ei->d_normalizedLength.set(eq);
        d_im.sendInference(ant, eq, InferenceId::STRINGS_LEN_NORM, false, true);
      }
    }
  }
}

void CoreSolver::checkRegisterTermsNormalForms()
{
  const std::vector<Node>& seqc = d_bsolver.getStringLikeEqc();
  for (const Node& eqc : seqc)
  {
    NormalForm& nfi = getNormalForm(eqc);
    // check if there is a length term for this equivalence class
    EqcInfo* ei = d_state.getOrMakeEqcInfo(eqc, false);
    Node lt = ei ? ei->d_lengthTerm : Node::null();
    if (lt.isNull())
    {
      Node c = d_termReg.mkNConcat(nfi.d_nf, eqc.getType());
      d_termReg.registerTerm(c);
    }
  }
}

size_t CoreSolver::pickInferInfo(const std::vector<CoreInferInfo>& pinfer)
{
  // now, determine which of the possible inferences we want to add
  unsigned use_index = 0;
  bool set_use_index = false;
  Trace("strings-solve") << "Possible inferences (" << pinfer.size()
                         << ") : " << std::endl;
  InferenceId min_id = InferenceId::UNKNOWN;
  unsigned max_index = 0;
  for (unsigned i = 0, psize = pinfer.size(); i < psize; i++)
  {
    const CoreInferInfo& ipii = pinfer[i];
    const InferInfo& ii = ipii.d_infer;
    Trace("strings-solve") << "#" << i << ": From " << ipii.d_i << " / "
                           << ipii.d_j << " (rev=" << ipii.d_rev << ") : ";
    Trace("strings-solve") << ii.d_conc << " by " << ii.getId() << std::endl;
    if (!set_use_index || ii.getId() < min_id
        || (ii.getId() == min_id && ipii.d_index > max_index))
    {
      min_id = ii.getId();
      max_index = ipii.d_index;
      use_index = i;
      set_use_index = true;
    }
  }
  return use_index;
}

void CoreSolver::checkNormalFormsEq()
{
  // we've computed the possible inferences above
  if (!d_pinfers.empty())
  {
    // add one inference from our list of possible inferences
    size_t use_index = pickInferInfo(d_pinfers);
    InferInfo& ii = d_pinfers[use_index].d_infer;
    // process the state change to this solver
    if (!ii.d_nfPair[0].isNull())
    {
      Assert(!ii.d_nfPair[1].isNull());
      addNormalFormPair(ii.d_nfPair[0], ii.d_nfPair[1]);
    }
    d_im.sendInference(ii, true);
    return;
  }
  //  process incompleteness
  if (d_modelUnsoundId != IncompleteId::NONE)
  {
    d_im.setModelUnsound(d_modelUnsoundId);
    d_modelUnsoundId = IncompleteId::NONE;
  }
  if (TraceIsOn("strings-nf"))
  {
    Trace("strings-nf") << "**** Normal forms are : " << std::endl;
    for (const Node& eqc : d_strings_eqc)
    {
      NormalForm& nf = getNormalForm(eqc);
      Trace("strings-nf") << "  N[" << eqc << "] (base " << nf.d_base
                          << ") = " << nf.d_nf << std::endl;
      Trace("strings-nf") << "     exp: " << nf.d_exp << std::endl;
    }
    Trace("strings-nf") << std::endl;
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
