/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus_unif_io.
 */

#include "theory/quantifiers/sygus/sygus_unif_io.h"

#include "options/quantifiers_options.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/example_infer.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/strings/word.h"
#include "util/random.h"

#include <math.h>

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

UnifContextIo::UnifContextIo() : d_curr_role(role_invalid)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

NodeRole UnifContextIo::getCurrentRole() { return d_curr_role; }

bool UnifContextIo::updateContext(SygusUnifIo* sui,
                                  std::vector<Node>& vals,
                                  bool pol)
{
  Assert(d_vals.size() == vals.size());
  bool changed = false;
  Node poln = pol ? d_true : d_false;
  for (size_t i = 0, vsize = vals.size(); i < vsize; i++)
  {
    Node v = vals[i];
    if (v.isNull())
    {
      // nothing can be inferred if the evaluation is unknown, e.g. if using
      // partial functions.
      continue;
    }
    if (v != poln)
    {
      if (d_vals[i] == d_true)
      {
        d_vals[i] = d_false;
        changed = true;
      }
    }
  }
  if (changed)
  {
    d_visit_role.clear();
  }
  return changed;
}

bool UnifContextIo::updateStringPosition(SygusUnifIo* sui,
                                         std::vector<size_t>& pos,
                                         NodeRole nrole)
{
  Assert(pos.size() == d_str_pos.size());
  bool changed = false;
  for (unsigned i = 0; i < pos.size(); i++)
  {
    if (pos[i] > 0)
    {
      d_str_pos[i] += pos[i];
      changed = true;
    }
  }
  if (changed)
  {
    d_visit_role.clear();
  }
  d_curr_role = nrole;
  return changed;
}

void UnifContextIo::initialize(SygusUnifIo* sui)
{
  // clear previous data
  d_vals.clear();
  d_str_pos.clear();
  d_curr_role = role_equal;
  d_visit_role.clear();

  // initialize with #examples
  unsigned sz = sui->d_examples.size();
  for (unsigned i = 0; i < sz; i++)
  {
    d_vals.push_back(d_true);
  }

  if (!sui->d_examples_out.empty())
  {
    // output type of the examples
    TypeNode exotn = sui->d_examples_out[0].getType();

    if (exotn.isStringLike())
    {
      for (unsigned i = 0; i < sz; i++)
      {
        d_str_pos.push_back(0);
      }
    }
  }
  d_visit_role.clear();
}

void UnifContextIo::getCurrentStrings(SygusUnifIo* sui,
                                      const std::vector<Node>& vals,
                                      std::vector<Node>& ex_vals)
{
  bool isPrefix = d_curr_role == role_string_prefix;
  Node dummy;
  for (unsigned i = 0; i < vals.size(); i++)
  {
    if (d_vals[i] == sui->d_true)
    {
      Assert(vals[i].isConst());
      unsigned pos_value = d_str_pos[i];
      if (pos_value > 0)
      {
        Assert(d_curr_role != role_invalid);
        Node s = vals[i];
        size_t sSize = strings::Word::getLength(s);
        Assert(pos_value <= sSize);
        ex_vals.push_back(isPrefix
                              ? strings::Word::suffix(s, sSize - pos_value)
                              : strings::Word::prefix(s, sSize - pos_value));
      }
      else
      {
        ex_vals.push_back(vals[i]);
      }
    }
    else
    {
      // irrelevant, add dummy
      ex_vals.push_back(dummy);
    }
  }
}

bool UnifContextIo::getStringIncrement(SygusUnifIo* sui,
                                       bool isPrefix,
                                       const std::vector<Node>& ex_vals,
                                       const std::vector<Node>& vals,
                                       std::vector<size_t>& inc,
                                       size_t& tot)
{
  for (unsigned j = 0; j < vals.size(); j++)
  {
    size_t ival = 0;
    if (d_vals[j] == sui->d_true)
    {
      // example is active in this context
      if (!vals[j].isConst())
      {
        // the value is unknown, thus we cannot use it to increment the strings
        // position
        return false;
      }
      ival = strings::Word::getLength(vals[j]);
      size_t exjLen = strings::Word::getLength(ex_vals[j]);
      if (ival <= exjLen)
      {
        if (!(isPrefix ? strings::Word::strncmp(ex_vals[j], vals[j], ival)
                       : strings::Word::rstrncmp(ex_vals[j], vals[j], ival)))
        {
          Trace("sygus-sui-dt-debug") << "X";
          return false;
        }
      }
      else
      {
        Trace("sygus-sui-dt-debug") << "X";
        return false;
      }
      Trace("sygus-sui-dt-debug") << ival;
      tot += ival;
    }
    else
    {
      // inactive in this context
      Trace("sygus-sui-dt-debug") << "-";
    }
    inc.push_back(ival);
  }
  return true;
}
bool UnifContextIo::isStringSolved(SygusUnifIo* sui,
                                   const std::vector<Node>& ex_vals,
                                   const std::vector<Node>& vals)
{
  for (unsigned j = 0; j < vals.size(); j++)
  {
    if (d_vals[j] == sui->d_true)
    {
      // example is active in this context
      if (!vals[j].isConst())
      {
        // value is unknown, thus it does not solve
        return false;
      }
      if (ex_vals[j] != vals[j])
      {
        return false;
      }
    }
  }
  return true;
}

// status : 0 : exact, -1 : vals is subset, 1 : vals is superset
Node SubsumeTrie::addTermInternal(Node t,
                                  const std::vector<Node>& vals,
                                  bool pol,
                                  std::vector<Node>& subsumed,
                                  bool spol,
                                  unsigned index,
                                  int status,
                                  bool checkExistsOnly,
                                  bool checkSubsume)
{
  if (index == vals.size())
  {
    if (status == 0)
    {
      // set the term if checkExistsOnly = false
      if (d_term.isNull() && !checkExistsOnly)
      {
        d_term = t;
      }
    }
    else if (status == 1)
    {
      Assert(checkSubsume);
      // found a subsumed term
      if (!d_term.isNull())
      {
        subsumed.push_back(d_term);
        // If we are only interested in feasibility, we could set d_term to null
        // here. However, d_term still could be useful, since it may be
        // smaller than t and suffice as a solution under some condition.
        // As a simple example, consider predicate synthesis and a case where we
        // enumerate a C that is correct for all I/O points whose output is
        // true. Then, C subsumes true. However, true may be preferred, e.g.
        // to generate a solution ite( C, true, D ) instead of ite( C, C, D ),
        // since true is conditionally correct under C, and is smaller than C.
      }
    }
    else
    {
      Assert(!checkExistsOnly && checkSubsume);
    }
    return d_term;
  }
  NodeManager* nm = NodeManager::currentNM();
  // the current value
  Assert(pol || (vals[index].isConst() && vals[index].getType().isBoolean()));
  Node cv = pol ? vals[index] : nm->mkConst(!vals[index].getConst<bool>());
  // if checkExistsOnly = false, check if the current value is subsumed if
  // checkSubsume = true, if so, don't add
  if (!checkExistsOnly && checkSubsume)
  {
    Assert(cv.isConst() && cv.getType().isBoolean());
    std::vector<bool> check_subsumed_by;
    if (status == 0)
    {
      if (!cv.getConst<bool>())
      {
        check_subsumed_by.push_back(spol);
      }
    }
    else if (status == -1)
    {
      check_subsumed_by.push_back(spol);
      if (!cv.getConst<bool>())
      {
        check_subsumed_by.push_back(!spol);
      }
    }
    // check for subsumed nodes
    for (unsigned i = 0, size = check_subsumed_by.size(); i < size; i++)
    {
      bool csbi = check_subsumed_by[i];
      Node csval = nm->mkConst(csbi);
      // check if subsumed
      std::map<Node, SubsumeTrie>::iterator itc = d_children.find(csval);
      if (itc != d_children.end())
      {
        Node ret = itc->second.addTermInternal(t,
                                               vals,
                                               pol,
                                               subsumed,
                                               spol,
                                               index + 1,
                                               -1,
                                               checkExistsOnly,
                                               checkSubsume);
        // ret subsumes t
        if (!ret.isNull())
        {
          return ret;
        }
      }
    }
  }
  Node ret;
  std::vector<bool> check_subsume;
  if (status == 0)
  {
    if (checkExistsOnly)
    {
      std::map<Node, SubsumeTrie>::iterator itc = d_children.find(cv);
      if (itc != d_children.end())
      {
        ret = itc->second.addTermInternal(t,
                                          vals,
                                          pol,
                                          subsumed,
                                          spol,
                                          index + 1,
                                          0,
                                          checkExistsOnly,
                                          checkSubsume);
      }
    }
    else
    {
      Assert(spol);
      ret = d_children[cv].addTermInternal(t,
                                           vals,
                                           pol,
                                           subsumed,
                                           spol,
                                           index + 1,
                                           0,
                                           checkExistsOnly,
                                           checkSubsume);
      if (ret != t)
      {
        // we were subsumed by ret, return
        return ret;
      }
    }
    if (checkSubsume)
    {
      Assert(cv.isConst() && cv.getType().isBoolean());
      // check for subsuming
      if (cv.getConst<bool>())
      {
        check_subsume.push_back(!spol);
      }
    }
  }
  else if (status == 1)
  {
    Assert(checkSubsume);
    Assert(cv.isConst() && cv.getType().isBoolean());
    check_subsume.push_back(!spol);
    if (cv.getConst<bool>())
    {
      check_subsume.push_back(spol);
    }
  }
  if (checkSubsume)
  {
    // check for subsumed terms
    for (unsigned i = 0, size = check_subsume.size(); i < size; i++)
    {
      Node csval = nm->mkConst<bool>(check_subsume[i]);
      std::map<Node, SubsumeTrie>::iterator itc = d_children.find(csval);
      if (itc != d_children.end())
      {
        itc->second.addTermInternal(t,
                                    vals,
                                    pol,
                                    subsumed,
                                    spol,
                                    index + 1,
                                    1,
                                    checkExistsOnly,
                                    checkSubsume);
        // clean up
        if (itc->second.isEmpty())
        {
          Assert(!checkExistsOnly);
          d_children.erase(csval);
        }
      }
    }
  }
  return ret;
}

Node SubsumeTrie::addTerm(Node t,
                          const std::vector<Node>& vals,
                          bool pol,
                          std::vector<Node>& subsumed)
{
  return addTermInternal(t, vals, pol, subsumed, true, 0, 0, false, true);
}

Node SubsumeTrie::addCond(Node c, const std::vector<Node>& vals, bool pol)
{
  std::vector<Node> subsumed;
  return addTermInternal(c, vals, pol, subsumed, true, 0, 0, false, false);
}

void SubsumeTrie::getSubsumed(const std::vector<Node>& vals,
                              bool pol,
                              std::vector<Node>& subsumed)
{
  addTermInternal(Node::null(), vals, pol, subsumed, true, 0, 1, true, true);
}

void SubsumeTrie::getSubsumedBy(const std::vector<Node>& vals,
                                bool pol,
                                std::vector<Node>& subsumed_by)
{
  // flip polarities
  addTermInternal(
      Node::null(), vals, !pol, subsumed_by, false, 0, 1, true, true);
}

void SubsumeTrie::getLeavesInternal(const std::vector<Node>& vals,
                                    bool pol,
                                    std::map<int, std::vector<Node> >& v,
                                    unsigned index,
                                    int status)
{
  if (index == vals.size())
  {
    // by convention, if we did not test any points, then we consider the
    // evaluation along the current path to be always false.
    int rstatus = status == -2 ? -1 : status;
    Assert(!d_term.isNull());
    Assert(std::find(v[rstatus].begin(), v[rstatus].end(), d_term)
           == v[rstatus].end());
    v[rstatus].push_back(d_term);
  }
  else
  {
    Assert(vals[index].isConst() && vals[index].getType().isBoolean());
    bool curr_val_true = vals[index].getConst<bool>() == pol;
    for (std::map<Node, SubsumeTrie>::iterator it = d_children.begin();
         it != d_children.end();
         ++it)
    {
      int new_status = status;
      bool success = true;
      // If the current value is true, then this is a relevant point.
      // We must consider the value of this child.
      if (curr_val_true)
      {
        if (it->first.isNull())
        {
          // The value of this child is unknown on this point, hence we
          // do not recurse
          success = false;
        }
        else if (status != 0)
        {
          // if the status is not zero (indicating that we have a mix of T/F),
          // then we must compute the new status.
          Assert(it->first.getType().isBoolean());
          Assert(it->first.isConst());
          new_status = (it->first.getConst<bool>() ? 1 : -1);
          if (status != -2 && new_status != status)
          {
            new_status = 0;
          }
        }
      }
      if (success)
      {
        it->second.getLeavesInternal(vals, pol, v, index + 1, new_status);
      }
    }
  }
}

void SubsumeTrie::getLeaves(const std::vector<Node>& vals,
                            bool pol,
                            std::map<int, std::vector<Node> >& v)
{
  getLeavesInternal(vals, pol, v, 0, -2);
}

SygusUnifIo::SygusUnifIo(Env& env, SynthConjecture* p)
    : SygusUnif(env),
      d_parent(p),
      d_check_sol(false),
      d_cond_count(0),
      d_sol_term_size(0),
      d_sol_cons_nondet(false),
      d_solConsUsingInfoGain(false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

SygusUnifIo::~SygusUnifIo() {}

void SygusUnifIo::initializeCandidate(
    TermDbSygus* tds,
    Node f,
    std::vector<Node>& enums,
    std::map<Node, std::vector<Node>>& strategy_lemmas)
{
  d_candidate = f;
  // copy the examples from the parent
  ExampleInfer* ei = d_parent->getExampleInfer();
  d_examples.clear();
  d_examples_out.clear();
  // copy the examples
  if (ei->hasExamples(f))
  {
    for (unsigned i = 0, nex = ei->getNumExamples(f); i < nex; i++)
    {
      std::vector<Node> input;
      ei->getExample(f, i, input);
      Node output = ei->getExampleOut(f, i);
      d_examples.push_back(input);
      d_examples_out.push_back(output);
    }
  }
  d_ecache.clear();
  SygusUnif::initializeCandidate(tds, f, enums, strategy_lemmas);
  // learn redundant operators based on the strategy
  d_strategy.at(f).staticLearnRedundantOps(strategy_lemmas);
}

void SygusUnifIo::notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas)
{
  Trace("sygus-sui-enum") << "Notify enumeration for " << e << " : " << v
                          << std::endl;
  Node c = d_candidate;
  Assert(!d_examples.empty());
  Assert(d_examples.size() == d_examples_out.size());

  EnumInfo& ei = d_strategy.at(c).getEnumInfo(e);
  // The explanation for why the current value should be excluded in future
  // iterations.
  Node exp_exc;

  std::vector<Node> base_results;
  TypeNode xtn = e.getType();
  Node bv = d_tds->sygusToBuiltin(v, xtn);
  bv = extendedRewrite(bv);
  Trace("sygus-sui-enum") << "PBE Compute Examples for " << bv << std::endl;
  // compte the results (should be cached)
  ExampleEvalCache* eec = d_parent->getExampleEvalCache(e);
  Assert(eec != nullptr);
  // Evaluate, which should be cached (assuming we have performed example-based
  // symmetry breaking on bv). Moreover don't cache the result in the case it
  // is not there already, since we won't need this evaluation anywhere outside
  // of this class.
  eec->evaluateVec(bv, base_results);
  // get the results for each slave enumerator
  std::map<Node, std::vector<Node>> srmap;
  for (const Node& xs : ei.d_enum_slave)
  {
    Assert(srmap.find(xs) == srmap.end());
    EnumInfo& eiv = d_strategy.at(c).getEnumInfo(xs);
    Node templ = eiv.d_template;
    if (!templ.isNull())
    {
      // Substitute and evaluate, notice that the template skeleton may
      // involve the sygus variables e.g. (>= x _) where x is a sygus
      // variable, hence we must compute the substituted template before
      // calling the evaluator.
      TNode targ = eiv.d_template_arg;
      TNode tbv = bv;
      Node stempl = templ.substitute(targ, tbv);
      std::vector<Node> sresults;
      eec->evaluateVec(stempl, sresults);
      srmap[xs] = sresults;
    }
    else
    {
      srmap[xs] = base_results;
    }
  }

  // is it excluded for domain-specific reason?
  std::vector<Node> exp_exc_vec;
  Assert(d_tds->isEnumerator(e));
  bool isPassive = d_tds->isPassiveEnumerator(e);
  if (getExplanationForEnumeratorExclude(e, v, base_results, exp_exc_vec))
  {
    if (isPassive)
    {
      Assert(!exp_exc_vec.empty());
      exp_exc = exp_exc_vec.size() == 1
                    ? exp_exc_vec[0]
                    : NodeManager::currentNM()->mkNode(AND, exp_exc_vec);
    }
    Trace("sygus-sui-enum")
        << "  ...fail : term is excluded (domain-specific)" << std::endl;
  }
  else
  {
    // notify all slaves
    Assert(!ei.d_enum_slave.empty());
    // explanation for why this value should be excluded
    for (unsigned s = 0; s < ei.d_enum_slave.size(); s++)
    {
      Node xs = ei.d_enum_slave[s];
      EnumInfo& eiv = d_strategy.at(c).getEnumInfo(xs);
      EnumCache& ecv = d_ecache[xs];
      Trace("sygus-sui-enum") << "Process " << xs << " from " << s << std::endl;
      // bool prevIsCover = false;
      if (eiv.getRole() == enum_io)
      {
        Trace("sygus-sui-enum") << "   IO-Eval of ";
        // prevIsCover = eiv.isFeasible();
      }
      else
      {
        Trace("sygus-sui-enum") << "Evaluation of ";
      }
      Trace("sygus-sui-enum") << xs << " : ";
      // evaluate all input/output examples
      std::vector<Node> results;
      std::map<Node, bool> cond_vals;
      std::map<Node, std::vector<Node>>::iterator itsr = srmap.find(xs);
      Trace("sygus-sui-debug") << " {" << itsr->second << "} ";
      Assert(itsr != srmap.end());
      for (unsigned j = 0, size = itsr->second.size(); j < size; j++)
      {
        Node res = itsr->second[j];
        // The value of this term for this example, or the truth value of
        // the I/O pair if the role of this enumerator is enum_io.
        Node resb;
        if (eiv.getRole() == enum_io)
        {
          Node out = d_examples_out[j];
          Assert(out.isConst());
          // If the result is not constant, then we assume that it does
          // not satisfy the example. This is a safe underapproximation
          // of the good behavior of the current term, that is, we only
          // produce solutions whose values are fully evaluatable on all input
          // points. Notice that terms may be used as leaves of decision
          // trees that are fully evaluatable on points in that branch, but
          // are not evaluatable on others, e.g. (head x) in the solution:
          //   (ite ((_ is cons) x) (head x) 5)
          resb = (res.isConst() && res == out) ? d_true : d_false;
        }
        else
        {
          // We only set resb if it is constant, otherwise it remains null.
          // This indicates its value cannot be determined.
          if (res.isConst())
          {
            resb = res;
          }
        }
        cond_vals[resb] = true;
        results.push_back(resb);
        if (TraceIsOn("sygus-sui-enum"))
        {
          if (resb.isNull())
          {
            Trace("sygus-sui-enum") << "_";
          }
          else if (resb.getType().isBoolean())
          {
            Trace("sygus-sui-enum") << (resb == d_true ? "1" : "0");
          }
          else
          {
            Trace("sygus-sui-enum") << "?";
          }
        }
      }
      bool keep = false;
      if (eiv.getRole() == enum_io)
      {
        // latter is the degenerate case of no examples
        if (cond_vals.find(d_true) != cond_vals.end() || cond_vals.empty())
        {
          // check subsumbed/subsuming
          std::vector<Node> subsume;
          if (cond_vals.find(d_false) == cond_vals.end())
          {
            Assert(cond_vals.size() == 1);
            // it is the entire solution, we are done
            Trace("sygus-sui-enum")
                << "  ...success, full solution added to PBE pool : "
                << d_tds->sygusToBuiltin(v) << std::endl;
            if (!ecv.isSolved())
            {
              ecv.setSolved(v);
              // it subsumes everything
              ecv.d_term_trie.clear();
              ecv.d_term_trie.addTerm(v, results, true, subsume);
            }
            keep = true;
          }
          else
          {
            Node val = ecv.d_term_trie.addTerm(v, results, true, subsume);
            if (val == v)
            {
              Trace("sygus-sui-enum") << "  ...success";
              if (!subsume.empty())
              {
                ecv.d_enum_subsume.insert(
                    ecv.d_enum_subsume.end(), subsume.begin(), subsume.end());
                Trace("sygus-sui-enum")
                    << " and subsumed " << subsume.size() << " terms";
              }
              Trace("sygus-sui-enum")
                  << "!   add to PBE pool : " << d_tds->sygusToBuiltin(v)
                  << std::endl;
              keep = true;
            }
            else
            {
              Assert(subsume.empty());
              Trace("sygus-sui-enum") << "  ...fail : subsumed" << std::endl;
            }
          }
        }
        else
        {
          Trace("sygus-sui-enum")
              << "  ...fail : it does not satisfy examples." << std::endl;
        }
      }
      else
      {
        // must be unique up to examples
        Node val = ecv.d_term_trie.addCond(v, results, true);
        if (val == v)
        {
          Trace("sygus-sui-enum") << "  ...success!   add to PBE pool : "
                                  << d_tds->sygusToBuiltin(v) << std::endl;
          keep = true;
        }
        else
        {
          Trace("sygus-sui-enum")
              << "  ...fail : term is not unique" << std::endl;
        }
      }
      if (keep)
      {
        // notify to retry the build of solution
        d_check_sol = true;
        d_cond_count++;
        ecv.addEnumValue(v, results);
      }
    }
  }

  if (isPassive)
  {
    // exclude this value on subsequent iterations
    if (exp_exc.isNull())
    {
      Trace("sygus-sui-enum-lemma") << "Use basic exclusion." << std::endl;
      // if we did not already explain why this should be excluded, use default
      exp_exc = d_tds->getExplain()->getExplanationForEquality(e, v);
    }
    exp_exc = exp_exc.negate();
    Trace("sygus-sui-enum-lemma")
        << "SygusUnifIo : enumeration exclude lemma : " << exp_exc << std::endl;
    lemmas.push_back(exp_exc);
  }
}

bool SygusUnifIo::constructSolution(std::vector<Node>& sols,
                                    std::vector<Node>& lemmas)
{
  Node sol = constructSolutionNode(lemmas);
  if (!sol.isNull())
  {
    sols.push_back(sol);
    return true;
  }
  return false;
}

Node SygusUnifIo::constructSolutionNode(std::vector<Node>& lemmas)
{
  Node c = d_candidate;
  if (!d_solution.isNull() && !options().quantifiers.sygusStream)
  {
    // already has a solution
    return d_solution;
  }
  // only check if an enumerator updated
  if (d_check_sol)
  {
    Trace("sygus-pbe") << "Construct solution, #iterations = " << d_cond_count
                       << std::endl;
    d_check_sol = false;
    Node newSolution;
    d_solConsUsingInfoGain = false;
    // try multiple times if we have done multiple conditions, due to
    // non-determinism
    for (unsigned i = 0; i <= d_cond_count; i++)
    {
      Trace("sygus-pbe-dt") << "ConstructPBE for candidate: " << c << std::endl;
      // initialize a call to construct solution
      initializeConstructSol();
      initializeConstructSolFor(c);
      // call the virtual construct solution method
      Node e = d_strategy.at(c).getRootEnumerator();
      Node vcc = constructSol(c, e, role_equal, 1, lemmas);
      // if we constructed the solution, and we either did not previously have
      // a solution, or the new solution is better (smaller).
      if (!vcc.isNull()
          && (d_solution.isNull()
              || (!d_solution.isNull()
                  && datatypes::utils::getSygusTermSize(vcc)
                         < d_sol_term_size)))
      {
        if (TraceIsOn("sygus-pbe"))
        {
          Trace("sygus-pbe") << "**** SygusUnif SOLVED : " << c << " = ";
          TermDbSygus::toStreamSygus("sygus-pbe", vcc);
          Trace("sygus-pbe") << std::endl;
          Trace("sygus-pbe") << "...solved at iteration " << i << std::endl;
        }
        d_solution = vcc;
        newSolution = vcc;
        d_sol_term_size = datatypes::utils::getSygusTermSize(vcc);
        Trace("sygus-pbe-sol")
            << "PBE solution size: " << d_sol_term_size << std::endl;
        // We've determined its feasible, now, enable information gain and
        // retry. We do this since information gain comes with an overhead,
        // and we want testing feasibility to be fast.
        if (!d_solConsUsingInfoGain)
        {
          // we permanently enable information gain and minimality now
          d_solConsUsingInfoGain = true;
          d_enableMinimality = true;
          i = 0;
        }
      }
      else if (!d_sol_cons_nondet)
      {
        break;
      }
    }
    if (!newSolution.isNull())
    {
      return newSolution;
    }
    Trace("sygus-pbe") << "...failed to solve." << std::endl;
  }
  return Node::null();
}

// ------------------------------------ solution construction from enumeration

bool SygusUnifIo::useStrContainsEnumeratorExclude(Node e)
{
  TypeNode xbt = d_tds->sygusToBuiltinType(e.getType());
  if (xbt.isStringLike())
  {
    std::map<Node, bool>::iterator itx = d_use_str_contains_eexc.find(e);
    if (itx != d_use_str_contains_eexc.end())
    {
      return itx->second;
    }
    Trace("sygus-sui-enum-debug")
        << "Is " << e << " is str.contains exclusion?" << std::endl;
    d_use_str_contains_eexc[e] = true;
    Node c = d_candidate;
    EnumInfo& ei = d_strategy.at(c).getEnumInfo(e);
    for (const Node& sn : ei.d_enum_slave)
    {
      EnumInfo& eis = d_strategy.at(c).getEnumInfo(sn);
      EnumRole er = eis.getRole();
      if (er != enum_io && er != enum_concat_term)
      {
        Trace("sygus-sui-enum-debug") << "  incompatible slave : " << sn
                                      << ", role = " << er << std::endl;
        d_use_str_contains_eexc[e] = false;
        return false;
      }
      d_use_str_contains_eexc_conditional[e] = false;
      if (eis.isConditional())
      {
        Trace("sygus-sui-enum-debug")
            << "  conditional slave : " << sn << std::endl;
        d_use_str_contains_eexc_conditional[e] = true;
      }
    }
    Trace("sygus-sui-enum-debug")
        << "...can use str.contains exclusion." << std::endl;
    return d_use_str_contains_eexc[e];
  }
  return false;
}

bool SygusUnifIo::getExplanationForEnumeratorExclude(
    Node e,
    Node v,
    std::vector<Node>& results,
    std::vector<Node>& exp)
{
  NodeManager* nm = NodeManager::currentNM();
  if (useStrContainsEnumeratorExclude(e))
  {
    // This check whether the example evaluates to something that is larger than
    // the output for some input/output pair. If so, then this term is never
    // useful. We generalize its explanation below.

    // if the enumerator is in a conditional context, then we are stricter
    // about when to exclude
    bool isConditional = d_use_str_contains_eexc_conditional[e];
    if (TraceIsOn("sygus-sui-cterm-debug"))
    {
      Trace("sygus-sui-enum") << std::endl;
    }
    // check if all examples had longer length that the output
    Assert(d_examples_out.size() == results.size());
    Trace("sygus-sui-cterm-debug")
        << "Check enumerator exclusion for " << e << " -> "
        << d_tds->sygusToBuiltin(v) << " based on str.contains." << std::endl;
    std::vector<unsigned> cmp_indices;
    for (size_t i = 0, size = results.size(); i < size; i++)
    {
      // If the result is not constant, then it is worthless. It does not
      // impact whether the term is excluded.
      if (results[i].isConst())
      {
        Assert(d_examples_out[i].isConst());
        Trace("sygus-sui-cterm-debug")
            << "  " << results[i] << " <> " << d_examples_out[i];
        Node cont = nm->mkNode(STRING_CONTAINS, d_examples_out[i], results[i]);
        Node contr = rewrite(cont);
        if (contr == d_false)
        {
          cmp_indices.push_back(i);
          Trace("sygus-sui-cterm-debug") << "...not contained." << std::endl;
        }
        else
        {
          Trace("sygus-sui-cterm-debug") << "...contained." << std::endl;
          if (isConditional)
          {
            return false;
          }
        }
      }
    }
    if (!cmp_indices.empty())
    {
      // we check invariance with respect to a negative contains test
      NegContainsSygusInvarianceTest ncset(d_env.getRewriter());
      if (isConditional)
      {
        ncset.setUniversal();
      }
      ncset.init(e, d_examples, d_examples_out, cmp_indices);
      // construct the generalized explanation
      d_tds->getExplain()->getExplanationFor(e, v, exp, ncset);
      Trace("sygus-sui-cterm")
          << "PBE-cterm : enumerator exclude " << d_tds->sygusToBuiltin(v)
          << " due to negative containment." << std::endl;
      return true;
    }
  }
  return false;
}

void SygusUnifIo::EnumCache::addEnumValue(Node v, std::vector<Node>& results)
{
  Trace("sygus-sui-debug") << "Add enum value " << this << " " << v << " : "
                           << results << std::endl;
  // should not have been enumerated before
  Assert(d_enum_val_to_index.find(v) == d_enum_val_to_index.end());
  d_enum_val_to_index[v] = d_enum_vals.size();
  d_enum_vals.push_back(v);
  d_enum_vals_res.push_back(results);
}

void SygusUnifIo::initializeConstructSol()
{
  d_context.initialize(this);
  d_sol_cons_nondet = false;
}

void SygusUnifIo::initializeConstructSolFor(Node f)
{
  Assert(d_candidate == f);
}

Node SygusUnifIo::constructSol(
    Node f, Node e, NodeRole nrole, int ind, std::vector<Node>& lemmas)
{
  Assert(d_candidate == f);
  UnifContextIo& x = d_context;
  TypeNode etn = e.getType();
  if (TraceIsOn("sygus-sui-dt-debug"))
  {
    indent("sygus-sui-dt-debug", ind);
    Trace("sygus-sui-dt-debug") << "ConstructPBE: (" << e << ", " << nrole
                                << ") for type " << etn << " in context ";
    print_val("sygus-sui-dt-debug", x.d_vals);
    NodeRole ctx_role = x.getCurrentRole();
    Trace("sygus-sui-dt-debug") << ", context role [" << ctx_role;
    if (ctx_role == role_string_prefix || ctx_role == role_string_suffix)
    {
      Trace("sygus-sui-dt-debug") << ", string pos : ";
      for (unsigned i = 0, size = x.d_str_pos.size(); i < size; i++)
      {
        Trace("sygus-sui-dt-debug") << " " << x.d_str_pos[i];
      }
    }
    Trace("sygus-sui-dt-debug") << "]";
    Trace("sygus-sui-dt-debug") << std::endl;
  }
  // enumerator type info
  EnumTypeInfo& tinfo = d_strategy.at(f).getEnumTypeInfo(etn);

  // get the enumerator information
  EnumInfo& einfo = d_strategy.at(f).getEnumInfo(e);

  EnumCache& ecache = d_ecache[e];

  bool retValMod = x.isReturnValueModified();

  Node ret_dt;
  Node cached_ret_dt;
  if (nrole == role_equal)
  {
    if (!retValMod)
    {
      if (ecache.isSolved())
      {
        // this type has a complete solution
        ret_dt = ecache.getSolved();
        indent("sygus-sui-dt", ind);
        Trace("sygus-sui-dt") << "return PBE: success : solved "
                              << d_tds->sygusToBuiltin(ret_dt) << std::endl;
        Assert(!ret_dt.isNull());
      }
      else
      {
        // could be conditionally solved
        std::vector<Node> subsumed_by;
        ecache.d_term_trie.getSubsumedBy(x.d_vals, true, subsumed_by);
        if (!subsumed_by.empty())
        {
          ret_dt = constructBestSolvedTerm(e, subsumed_by);
          indent("sygus-sui-dt", ind);
          Trace("sygus-sui-dt") << "return PBE: success : conditionally solved "
                                << d_tds->sygusToBuiltin(ret_dt) << std::endl;
        }
        else
        {
          indent("sygus-sui-dt-debug", ind);
          Trace("sygus-sui-dt-debug")
              << "  ...not currently conditionally solved." << std::endl;
        }
      }
    }
    if (ret_dt.isNull())
    {
      if (d_tds->sygusToBuiltinType(e.getType()).isStringLike())
      {
        // check if a current value that closes all examples
        // get the term enumerator for this type
        std::map<EnumRole, Node>::iterator itnt =
            tinfo.d_enum.find(enum_concat_term);
        if (itnt != tinfo.d_enum.end())
        {
          Node et = itnt->second;

          EnumCache& ecachet = d_ecache[et];
          // get the current examples
          std::vector<Node> ex_vals;
          x.getCurrentStrings(this, d_examples_out, ex_vals);
          Assert(ecache.d_enum_vals.size() == ecache.d_enum_vals_res.size());

          // test each example in the term enumerator for the type
          std::vector<Node> str_solved;
          for (unsigned i = 0, size = ecachet.d_enum_vals.size(); i < size; i++)
          {
            if (x.isStringSolved(this, ex_vals, ecachet.d_enum_vals_res[i]))
            {
              str_solved.push_back(ecachet.d_enum_vals[i]);
            }
          }
          if (!str_solved.empty())
          {
            ret_dt = constructBestSolvedTerm(e, str_solved);
            indent("sygus-sui-dt", ind);
            Trace("sygus-sui-dt") << "return PBE: success : string solved "
                                  << d_tds->sygusToBuiltin(ret_dt) << std::endl;
          }
          else
          {
            indent("sygus-sui-dt-debug", ind);
            Trace("sygus-sui-dt-debug")
                << "  ...not currently string solved." << std::endl;
          }
        }
      }
    }
    // maybe we can find one in the cache
    if (ret_dt.isNull() && !retValMod)
    {
      bool firstTime = true;
      std::unordered_set<Node> intersection;
      std::map<TypeNode, std::unordered_set<Node>>::iterator pit;
      for (size_t i = 0, nvals = x.d_vals.size(); i < nvals; i++)
      {
        if (x.d_vals[i].getConst<bool>())
        {
          pit = d_psolutions[i].find(etn);
          if (pit == d_psolutions[i].end())
          {
            // no cached solution
            intersection.clear();
            break;
          }
          if (firstTime)
          {
            intersection = pit->second;
            firstTime = false;
          }
          else
          {
            std::vector<Node> rm;
            for (const Node& a : intersection)
            {
              if (pit->second.find(a) == pit->second.end())
              {
                rm.push_back(a);
              }
            }
            for (const Node& a : rm)
            {
              intersection.erase(a);
            }
            if (intersection.empty())
            {
              break;
            }
          }
        }
      }
      if (!intersection.empty())
      {
        if (d_enableMinimality)
        {
          // if we are enabling minimality, the minimal cached solution may
          // still not be the best solution, thus we remember it and keep it if
          // we don't construct a better one below
          std::vector<Node> intervec;
          intervec.insert(
              intervec.begin(), intersection.begin(), intersection.end());
          cached_ret_dt = getMinimalTerm(intervec);
        }
        else
        {
          ret_dt = *intersection.begin();
        }
        if (TraceIsOn("sygus-sui-dt"))
        {
          indent("sygus-sui-dt", ind);
          Trace("sygus-sui-dt") << "ConstructPBE: found in cache: ";
          Node csol = ret_dt;
          if (d_enableMinimality)
          {
            csol = cached_ret_dt;
            Trace("sygus-sui-dt") << "(minimal) ";
          }
          TermDbSygus::toStreamSygus("sygus-sui-dt", csol);
          Trace("sygus-sui-dt") << std::endl;
        }
      }
    }
  }
  else if (nrole == role_string_prefix || nrole == role_string_suffix)
  {
    // check if each return value is a prefix/suffix of all open examples
    if (!retValMod || x.getCurrentRole() == nrole)
    {
      std::map<Node, std::vector<size_t>> incr;
      bool isPrefix = nrole == role_string_prefix;
      std::map<Node, size_t> total_inc;
      std::vector<Node> inc_strs;
      // make the value of the examples
      std::vector<Node> ex_vals;
      x.getCurrentStrings(this, d_examples_out, ex_vals);
      if (TraceIsOn("sygus-sui-dt-debug"))
      {
        indent("sygus-sui-dt-debug", ind);
        Trace("sygus-sui-dt-debug") << "current strings : " << std::endl;
        for (unsigned i = 0, size = ex_vals.size(); i < size; i++)
        {
          indent("sygus-sui-dt-debug", ind + 1);
          Trace("sygus-sui-dt-debug") << ex_vals[i] << std::endl;
        }
      }

      // check if there is a value for which is a prefix/suffix of all active
      // examples
      Assert(ecache.d_enum_vals.size() == ecache.d_enum_vals_res.size());

      for (unsigned i = 0, size = ecache.d_enum_vals.size(); i < size; i++)
      {
        Node val_t = ecache.d_enum_vals[i];
        Assert(incr.find(val_t) == incr.end());
        indent("sygus-sui-dt-debug", ind);
        Trace("sygus-sui-dt-debug") << "increment string values : ";
        TermDbSygus::toStreamSygus("sygus-sui-dt-debug", val_t);
        Trace("sygus-sui-dt-debug") << " : ";
        Assert(ecache.d_enum_vals_res[i].size() == d_examples_out.size());
        size_t tot = 0;
        bool exsuccess = x.getStringIncrement(this,
                                              isPrefix,
                                              ex_vals,
                                              ecache.d_enum_vals_res[i],
                                              incr[val_t],
                                              tot);
        if (!exsuccess)
        {
          incr.erase(val_t);
          Trace("sygus-sui-dt-debug") << "...fail" << std::endl;
        }
        else
        {
          total_inc[val_t] = tot;
          inc_strs.push_back(val_t);
          Trace("sygus-sui-dt-debug")
              << "...success, total increment = " << tot << std::endl;
        }
      }

      if (!incr.empty())
      {
        // solution construction for strings concatenation is non-deterministic
        // with respect to failure/success.
        d_sol_cons_nondet = true;
        ret_dt = constructBestStringToConcat(inc_strs, total_inc, incr);
        Assert(!ret_dt.isNull());
        indent("sygus-sui-dt", ind);
        Trace("sygus-sui-dt")
            << "PBE: CONCAT strategy : choose " << (isPrefix ? "pre" : "suf")
            << "fix value " << d_tds->sygusToBuiltin(ret_dt) << std::endl;
        // update the context
        bool ret = x.updateStringPosition(this, incr[ret_dt], nrole);
        AlwaysAssert(ret == (total_inc[ret_dt] > 0));
      }
      else
      {
        indent("sygus-sui-dt", ind);
        Trace("sygus-sui-dt") << "PBE: failed CONCAT strategy, no values are "
                              << (isPrefix ? "pre" : "suf")
                              << "fix of all examples." << std::endl;
      }
    }
    else
    {
      indent("sygus-sui-dt", ind);
      Trace("sygus-sui-dt")
          << "PBE: failed CONCAT strategy, prefix/suffix mismatch."
          << std::endl;
    }
  }
  if (!ret_dt.isNull() || einfo.isTemplated())
  {
    Assert(ret_dt.isNull() || ret_dt.getType() == e.getType());
    indent("sygus-sui-dt", ind);
    Trace("sygus-sui-dt") << "ConstructPBE: returned (pre-strategy) " << ret_dt
                          << std::endl;
    return ret_dt;
  }
  // we will try a single strategy
  EnumTypeInfoStrat* etis = nullptr;
  std::map<NodeRole, StrategyNode>::iterator itsn = tinfo.d_snodes.find(nrole);
  if (itsn == tinfo.d_snodes.end())
  {
    indent("sygus-sui-dt", ind);
    Trace("sygus-sui-dt") << "ConstructPBE: returned (no-strategy) " << ret_dt
                          << std::endl;
    return ret_dt;
  }
  // strategy info
  StrategyNode& snode = itsn->second;
  if (x.d_visit_role[e].find(nrole) != x.d_visit_role[e].end())
  {
    // already visited and context not changed (notice d_visit_role is cleared
    // when the context changes).
    indent("sygus-sui-dt", ind);
    Trace("sygus-sui-dt") << "ConstructPBE: returned (already visited) "
                          << ret_dt << std::endl;
    return ret_dt;
  }
  x.d_visit_role[e][nrole] = true;
  // try a random strategy
  if (snode.d_strats.size() > 1)
  {
    std::shuffle(
        snode.d_strats.begin(), snode.d_strats.end(), Random::getRandom());
  }
  // ITE always first if we have not yet solved
  // the reasoning is that splitting on conditions only subdivides the problem
  // and cannot be the source of failure, whereas the wrong choice for a
  // concatenation term may lead to failure
  if (d_solution.isNull())
  {
    for (unsigned i = 0; i < snode.d_strats.size(); i++)
    {
      if (snode.d_strats[i]->d_this == strat_ITE)
      {
        // flip the two
        EnumTypeInfoStrat* etis_i = snode.d_strats[i];
        snode.d_strats[i] = snode.d_strats[0];
        snode.d_strats[0] = etis_i;
        break;
      }
    }
  }

  // iterate over the strategies
  unsigned sindex = 0;
  bool did_recurse = false;
  while (ret_dt.isNull() && !did_recurse && sindex < snode.d_strats.size())
  {
    if (snode.d_strats[sindex]->isValid(x))
    {
      etis = snode.d_strats[sindex];
      Assert(etis != nullptr);
      StrategyType strat = etis->d_this;
      indent("sygus-sui-dt", ind + 1);
      Trace("sygus-sui-dt")
          << "...try STRATEGY " << strat << "..." << std::endl;

      std::vector<Node> dt_children_cons;
      bool success = true;

      // for ITE
      Node split_cond_enum;
      unsigned split_cond_res_index = 0;
      CVC5_UNUSED bool set_split_cond_res_index = false;

      for (unsigned sc = 0, size = etis->d_cenum.size(); sc < size; sc++)
      {
        indent("sygus-sui-dt", ind + 1);
        Trace("sygus-sui-dt")
            << "construct PBE child #" << sc << "..." << std::endl;
        Node rec_c;

        std::pair<Node, NodeRole>& cenum = etis->d_cenum[sc];

        // update the context
        std::vector<Node> prev;
        if (strat == strat_ITE && sc > 0)
        {
          EnumCache& ecache_cond = d_ecache[split_cond_enum];
          Assert(set_split_cond_res_index);
          Assert(split_cond_res_index < ecache_cond.d_enum_vals_res.size());
          prev = x.d_vals;
          x.updateContext(this,
                          ecache_cond.d_enum_vals_res[split_cond_res_index],
                          sc == 1);
          // return value of above call may be false in corner cases where we
          // must choose a non-separating condition to traverse to another
          // strategy node
        }

        // recurse
        if (strat == strat_ITE && sc == 0)
        {
          Node ce = cenum.first;

          EnumCache& ecache_child = d_ecache[ce];

          // get the conditionals in the current context : they must be
          // distinguishable
          std::map<int, std::vector<Node> > possible_cond;
          std::map<Node, int> solved_cond;  // stores branch
          ecache_child.d_term_trie.getLeaves(x.d_vals, true, possible_cond);

          std::map<int, std::vector<Node>>::iterator itpc =
              possible_cond.find(0);
          if (itpc != possible_cond.end())
          {
            if (TraceIsOn("sygus-sui-dt-debug"))
            {
              indent("sygus-sui-dt-debug", ind + 1);
              Trace("sygus-sui-dt-debug")
                  << "PBE : We have " << itpc->second.size()
                  << " distinguishable conditionals:" << std::endl;
              for (Node& cond : itpc->second)
              {
                indent("sygus-sui-dt-debug", ind + 2);
                Trace("sygus-sui-dt-debug")
                    << d_tds->sygusToBuiltin(cond) << std::endl;
              }
            }
            if (rec_c.isNull())
            {
              rec_c = constructBestConditional(ce, itpc->second);
              Assert(!rec_c.isNull());
              indent("sygus-sui-dt", ind);
              Trace("sygus-sui-dt")
                  << "PBE: ITE strategy : choose best conditional "
                  << d_tds->sygusToBuiltin(rec_c) << std::endl;
            }
          }
          else
          {
            // if the branch types are different, it could still make a
            // difference to recurse, for instance see issue #4790. We do this
            // if either branch is a different type from the current type.
            TypeNode branchType1 = etis->d_cenum[1].first.getType();
            TypeNode branchType2 = etis->d_cenum[2].first.getType();
            bool childTypesEqual = branchType1 == etn && branchType2 == etn;
            if (!childTypesEqual)
            {
              if (!ecache_child.d_enum_vals.empty())
              {
                // take arbitrary
                rec_c = constructBestConditional(ce, ecache_child.d_enum_vals);
                indent("sygus-sui-dt", ind);
                Trace("sygus-sui-dt")
                    << "PBE: ITE strategy : choose arbitrary conditional due "
                       "to disequal child types "
                    << d_tds->sygusToBuiltin(rec_c) << std::endl;
              }
            }
            if (rec_c.isNull())
            {
              indent("sygus-sui-dt", ind);
              Trace("sygus-sui-dt")
                  << "return PBE: failed ITE strategy, "
                     "cannot find a distinguishable condition, childTypesEqual="
                  << childTypesEqual << std::endl;
            }
          }
          if (!rec_c.isNull())
          {
            Assert(ecache_child.d_enum_val_to_index.find(rec_c)
                   != ecache_child.d_enum_val_to_index.end());
            split_cond_res_index = ecache_child.d_enum_val_to_index[rec_c];
            set_split_cond_res_index = true;
            split_cond_enum = ce;
            Assert(split_cond_res_index < ecache_child.d_enum_vals_res.size());
          }
        }
        else
        {
          did_recurse = true;
          rec_c = constructSol(f, cenum.first, cenum.second, ind + 2, lemmas);
        }
        // undo update the context
        if (strat == strat_ITE && sc > 0)
        {
          x.d_vals = prev;
        }
        if (!rec_c.isNull())
        {
          dt_children_cons.push_back(rec_c);
        }
        else
        {
          success = false;
          break;
        }
      }
      if (success)
      {
        Assert(dt_children_cons.size() == etis->d_sol_templ_args.size());
        // ret_dt = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR,
        // dt_children );
        ret_dt = etis->d_sol_templ;
        ret_dt = ret_dt.substitute(etis->d_sol_templ_args.begin(),
                                   etis->d_sol_templ_args.end(),
                                   dt_children_cons.begin(),
                                   dt_children_cons.end());
        indent("sygus-sui-dt-debug", ind);
        Trace("sygus-sui-dt-debug")
            << "PBE: success : constructed for strategy " << strat << std::endl;
      }
      else
      {
        indent("sygus-sui-dt-debug", ind);
        Trace("sygus-sui-dt-debug")
            << "PBE: failed for strategy " << strat << std::endl;
      }
    }
    // increment
    sindex++;
  }

  // if there was a cached solution, process it now
  if (!cached_ret_dt.isNull() && cached_ret_dt != ret_dt)
  {
    if (ret_dt.isNull())
    {
      // take the cached one if it is the only one
      ret_dt = cached_ret_dt;
    }
    else if (d_enableMinimality)
    {
      Assert(ret_dt.getType() == cached_ret_dt.getType());
      // take the cached one if it is smaller
      std::vector<Node> retDts;
      retDts.push_back(cached_ret_dt);
      retDts.push_back(ret_dt);
      ret_dt = getMinimalTerm(retDts);
    }
  }
  Assert(ret_dt.isNull() || ret_dt.getType() == e.getType());
  if (TraceIsOn("sygus-sui-dt"))
  {
    indent("sygus-sui-dt", ind);
    Trace("sygus-sui-dt") << "ConstructPBE: returned ";
    TermDbSygus::toStreamSygus("sygus-sui-dt", ret_dt);
    Trace("sygus-sui-dt") << std::endl;
  }
  // remember the solution
  if (nrole == role_equal)
  {
    if (!retValMod && !ret_dt.isNull())
    {
      for (size_t i = 0, nvals = x.d_vals.size(); i < nvals; i++)
      {
        if (x.d_vals[i].getConst<bool>())
        {
          if (TraceIsOn("sygus-sui-cache"))
          {
            indent("sygus-sui-cache", ind);
            Trace("sygus-sui-cache") << "Cache solution (#" << i << ") : ";
            TermDbSygus::toStreamSygus("sygus-sui-cache", ret_dt);
            Trace("sygus-sui-cache") << std::endl;
          }
          d_psolutions[i][etn].insert(ret_dt);
        }
      }
    }
  }

  return ret_dt;
}

Node SygusUnifIo::constructBestConditional(Node ce,
                                           const std::vector<Node>& conds)
{
  if (!d_solConsUsingInfoGain)
  {
    return SygusUnif::constructBestConditional(ce, conds);
  }
  UnifContextIo& x = d_context;
  // use information gain heuristic
  Trace("sygus-sui-dt-igain") << "Best information gain in context ";
  print_val("sygus-sui-dt-igain", x.d_vals);
  Trace("sygus-sui-dt-igain") << std::endl;
  // set of indices that are active in this branch, i.e. x.d_vals[i] is true
  std::vector<unsigned> activeIndices;
  // map (j,t,s) -> n, such that the j^th condition in the vector conds
  // evaluates to t (typically true/false) on n active I/O pairs with output s.
  std::map<unsigned, std::map<Node, std::map<Node, unsigned>>> eval;
  // map (j,t) -> m, such that the j^th condition in the vector conds
  // evaluates to t (typically true/false) for m active I/O pairs.
  std::map<unsigned, std::map<Node, unsigned>> evalCount;
  unsigned nconds = conds.size();
  EnumCache& ecache = d_ecache[ce];
  // Get the index of conds[j] in the enumerator cache, this is to look up
  // its evaluation on each point.
  std::vector<unsigned> eindex;
  for (unsigned j = 0; j < nconds; j++)
  {
    eindex.push_back(ecache.d_enum_val_to_index[conds[j]]);
  }
  unsigned activePoints = 0;
  for (unsigned i = 0, npoints = x.d_vals.size(); i < npoints; i++)
  {
    if (x.d_vals[i].getConst<bool>())
    {
      activePoints++;
      Node eo = d_examples_out[i];
      for (unsigned j = 0; j < nconds; j++)
      {
        Node resn = ecache.d_enum_vals_res[eindex[j]][i];
        Assert(resn.isConst());
        eval[j][resn][eo]++;
        evalCount[j][resn]++;
      }
    }
  }
  AlwaysAssert(activePoints > 0);
  // find the condition that leads to the lowest entropy
  // initially set minEntropy to > 1.0.
  double minEntropy = 2.0;
  unsigned bestIndex = 0;
  int numEqual = 1;
  for (unsigned j = 0; j < nconds; j++)
  {
    // To compute the entropy for a condition C, for pair of terms (s, t), let
    //   prob(t) be the probability C evaluates to t on an active point,
    //   prob(s|t) be the probability that an active point on which C
    //     evaluates to t has output s.
    // Then, the entropy of C is:
    //   sum{t}. prob(t)*( sum{s}. -prob(s|t)*log2(prob(s|t)) )
    // where notice this is always between 0 and 1.
    double entropySum = 0.0;
    Trace("sygus-sui-dt-igain") << j << " : ";
    for (std::pair<const Node, std::map<Node, unsigned>>& ej : eval[j])
    {
      unsigned ecount = evalCount[j][ej.first];
      if (ecount > 0)
      {
        double probBranch = double(ecount) / double(activePoints);
        Trace("sygus-sui-dt-igain") << ej.first << " -> ( ";
        for (std::pair<const Node, unsigned>& eej : ej.second)
        {
          if (eej.second > 0)
          {
            double probVal = double(eej.second) / double(ecount);
            Trace("sygus-sui-dt-igain")
                << eej.first << ":" << eej.second << " ";
            double factor = -probVal * log2(probVal);
            entropySum += probBranch * factor;
          }
        }
        Trace("sygus-sui-dt-igain") << ") ";
      }
    }
    Trace("sygus-sui-dt-igain") << "..." << entropySum << std::endl;
    // either less, or equal and coin flip passes
    bool doSet = false;
    if (entropySum == minEntropy)
    {
      numEqual++;
      if (Random::getRandom().pickWithProb(double(1) / double(numEqual)))
      {
        doSet = true;
      }
    }
    else if (entropySum < minEntropy)
    {
      doSet = true;
      numEqual = 1;
    }
    if (doSet)
    {
      minEntropy = entropySum;
      bestIndex = j;
    }
  }

  Assert(!conds.empty());
  return conds[bestIndex];
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
