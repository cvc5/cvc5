/*********************                                                        */
/*! \file sygus_unif_io.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_unif_io
 **/

#include "theory/quantifiers/sygus/sygus_unif_io.h"

#include "options/quantifiers_options.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/evaluator.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "util/random.h"

using namespace CVC4::kind;

namespace CVC4 {
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
  for (unsigned i = 0; i < vals.size(); i++)
  {
    if (vals[i] != poln)
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
                                         std::vector<unsigned>& pos,
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
  d_uinfo.clear();

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

    if (exotn.isString())
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
                                      std::vector<String>& ex_vals)
{
  bool isPrefix = d_curr_role == role_string_prefix;
  String dummy;
  for (unsigned i = 0; i < vals.size(); i++)
  {
    if (d_vals[i] == sui->d_true)
    {
      Assert(vals[i].isConst());
      unsigned pos_value = d_str_pos[i];
      if (pos_value > 0)
      {
        Assert(d_curr_role != role_invalid);
        String s = vals[i].getConst<String>();
        Assert(pos_value <= s.size());
        ex_vals.push_back(isPrefix ? s.suffix(s.size() - pos_value)
                                   : s.prefix(s.size() - pos_value));
      }
      else
      {
        ex_vals.push_back(vals[i].getConst<String>());
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
                                       const std::vector<String>& ex_vals,
                                       const std::vector<Node>& vals,
                                       std::vector<unsigned>& inc,
                                       unsigned& tot)
{
  for (unsigned j = 0; j < vals.size(); j++)
  {
    unsigned ival = 0;
    if (d_vals[j] == sui->d_true)
    {
      // example is active in this context
      Assert(vals[j].isConst());
      String mystr = vals[j].getConst<String>();
      ival = mystr.size();
      if (mystr.size() <= ex_vals[j].size())
      {
        if (!(isPrefix ? ex_vals[j].strncmp(mystr, ival)
                       : ex_vals[j].rstrncmp(mystr, ival)))
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
                                   const std::vector<String>& ex_vals,
                                   const std::vector<Node>& vals)
{
  for (unsigned j = 0; j < vals.size(); j++)
  {
    if (d_vals[j] == sui->d_true)
    {
      // example is active in this context
      Assert(vals[j].isConst());
      String mystr = vals[j].getConst<String>();
      if (ex_vals[j] != mystr)
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
        if (!checkExistsOnly)
        {
          // remove it if checkExistsOnly = false
          d_term = Node::null();
        }
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
    Assert(!d_term.isNull());
    Assert(std::find(v[status].begin(), v[status].end(), d_term)
           == v[status].end());
    v[status].push_back(d_term);
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
      // if the current value is true
      if (curr_val_true)
      {
        if (status != 0)
        {
          Assert(it->first.isConst() && it->first.getType().isBoolean());
          new_status = (it->first.getConst<bool>() ? 1 : -1);
          if (status != -2 && new_status != status)
          {
            new_status = 0;
          }
        }
      }
      it->second.getLeavesInternal(vals, pol, v, index + 1, new_status);
    }
  }
}

void SubsumeTrie::getLeaves(const std::vector<Node>& vals,
                            bool pol,
                            std::map<int, std::vector<Node> >& v)
{
  getLeavesInternal(vals, pol, v, 0, -2);
}

SygusUnifIo::SygusUnifIo()
    : d_check_sol(false), d_cond_count(0), d_sol_cons_nondet(false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

SygusUnifIo::~SygusUnifIo() {}
void SygusUnifIo::initializeCandidate(
    QuantifiersEngine* qe,
    Node f,
    std::vector<Node>& enums,
    std::map<Node, std::vector<Node>>& strategy_lemmas)
{
  d_examples.clear();
  d_examples_out.clear();
  d_ecache.clear();
  d_candidate = f;
  SygusUnif::initializeCandidate(qe, f, enums, strategy_lemmas);
  // learn redundant operators based on the strategy
  d_strategy[f].staticLearnRedundantOps(strategy_lemmas);
}

void SygusUnifIo::addExample(const std::vector<Node>& input, Node output)
{
  d_examples.push_back(input);
  d_examples_out.push_back(output);
}

void SygusUnifIo::notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas)
{
  Trace("sygus-sui-enum") << "Notify enumeration for " << e << " : " << v
                          << std::endl;
  Node c = d_candidate;
  Assert(!d_examples.empty());
  Assert(d_examples.size() == d_examples_out.size());

  EnumInfo& ei = d_strategy[c].getEnumInfo(e);
  // The explanation for why the current value should be excluded in future
  // iterations.
  Node exp_exc;

  TypeNode xtn = e.getType();
  Node bv = d_tds->sygusToBuiltin(v, xtn);
  std::vector<Node> base_results;
  // compte the results
  for (unsigned j = 0, size = d_examples.size(); j < size; j++)
  {
    Node res = d_tds->evaluateBuiltin(xtn, bv, d_examples[j]);
    Trace("sygus-sui-enum-debug")
        << "...got res = " << res << " from " << bv << std::endl;
    base_results.push_back(res);
  }
  // get the results for each slave enumerator
  std::map<Node, std::vector<Node>> srmap;
  Evaluator* ev = d_tds->getEvaluator();
  bool tryEval = options::sygusEvalOpt();
  for (const Node& xs : ei.d_enum_slave)
  {
    Assert(srmap.find(xs) == srmap.end());
    EnumInfo& eiv = d_strategy[c].getEnumInfo(xs);
    Node templ = eiv.d_template;
    if (!templ.isNull())
    {
      TNode templ_var = eiv.d_template_arg;
      std::vector<Node> args;
      args.push_back(templ_var);
      std::vector<Node> sresults;
      for (const Node& res : base_results)
      {
        TNode tres = res;
        std::vector<Node> vals;
        vals.push_back(tres);
        Node sres;
        if (tryEval)
        {
          sres = ev->eval(templ, args, vals);
        }
        if (sres.isNull())
        {
          // fall back on rewriter
          sres = templ.substitute(templ_var, tres);
          sres = Rewriter::rewrite(sres);
        }
        sresults.push_back(sres);
      }
      srmap[xs] = sresults;
    }
    else
    {
      srmap[xs] = base_results;
    }
  }

  // is it excluded for domain-specific reason?
  std::vector<Node> exp_exc_vec;
  if (getExplanationForEnumeratorExclude(e, v, base_results, exp_exc_vec))
  {
    Assert(!exp_exc_vec.empty());
    exp_exc = exp_exc_vec.size() == 1
                  ? exp_exc_vec[0]
                  : NodeManager::currentNM()->mkNode(AND, exp_exc_vec);
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
      EnumInfo& eiv = d_strategy[c].getEnumInfo(xs);
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
      Assert(itsr != srmap.end());
      for (unsigned j = 0, size = itsr->second.size(); j < size; j++)
      {
        Node res = itsr->second[j];
        Assert(res.isConst());
        Node resb;
        if (eiv.getRole() == enum_io)
        {
          Node out = d_examples_out[j];
          Assert(out.isConst());
          resb = res == out ? d_true : d_false;
        }
        else
        {
          resb = res;
        }
        cond_vals[resb] = true;
        results.push_back(resb);
        if (Trace.isOn("sygus-sui-enum"))
        {
          if (resb.getType().isBoolean())
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
        d_cond_count++;
      }
      if (keep)
      {
        // notify to retry the build of solution
        d_check_sol = true;
        ecv.addEnumValue(v, results);
      }
    }
  }

  // exclude this value on subsequent iterations
  if (exp_exc.isNull())
  {
    // if we did not already explain why this should be excluded, use default
    exp_exc = d_tds->getExplain()->getExplanationForEquality(e, v);
  }
  exp_exc = exp_exc.negate();
  Trace("sygus-sui-enum-lemma")
      << "SygusUnifIo : enumeration exclude lemma : " << exp_exc << std::endl;
  lemmas.push_back(exp_exc);
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
  if (!d_solution.isNull())
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
    // try multiple times if we have done multiple conditions, due to
    // non-determinism
    unsigned sol_term_size = 0;
    for (unsigned i = 0; i <= d_cond_count; i++)
    {
      Trace("sygus-pbe-dt") << "ConstructPBE for candidate: " << c << std::endl;
      // initialize a call to construct solution
      initializeConstructSol();
      initializeConstructSolFor(c);
      // call the virtual construct solution method
      Node e = d_strategy[c].getRootEnumerator();
      Node vcc = constructSol(c, e, role_equal, 1, lemmas);
      // if we constructed the solution, and we either did not previously have
      // a solution, or the new solution is better (smaller).
      if (!vcc.isNull()
          && (d_solution.isNull()
              || (!d_solution.isNull()
                  && d_tds->getSygusTermSize(vcc) < sol_term_size)))
      {
        Trace("sygus-pbe") << "**** SygusUnif SOLVED : " << c << " = " << vcc
                           << std::endl;
        Trace("sygus-pbe") << "...solved at iteration " << i << std::endl;
        d_solution = vcc;
        sol_term_size = d_tds->getSygusTermSize(vcc);
      }
      else if (!d_sol_cons_nondet)
      {
        break;
      }
    }
    if (!d_solution.isNull())
    {
      return d_solution;
    }
    Trace("sygus-pbe") << "...failed to solve." << std::endl;
  }
  return Node::null();
}

// ------------------------------------ solution construction from enumeration

bool SygusUnifIo::useStrContainsEnumeratorExclude(Node e)
{
  TypeNode xbt = d_tds->sygusToBuiltinType(e.getType());
  if (xbt.isString())
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
    EnumInfo& ei = d_strategy[c].getEnumInfo(e);
    for (const Node& sn : ei.d_enum_slave)
    {
      EnumInfo& eis = d_strategy[c].getEnumInfo(sn);
      EnumRole er = eis.getRole();
      if (er != enum_io && er != enum_concat_term)
      {
        Trace("sygus-sui-enum-debug") << "  incompatible slave : " << sn
                                      << ", role = " << er << std::endl;
        d_use_str_contains_eexc[e] = false;
        return false;
      }
      if (eis.isConditional())
      {
        Trace("sygus-sui-enum-debug")
            << "  conditional slave : " << sn << std::endl;
        d_use_str_contains_eexc[e] = false;
        return false;
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

    if (Trace.isOn("sygus-sui-cterm-debug"))
    {
      Trace("sygus-sui-enum") << std::endl;
    }
    // check if all examples had longer length that the output
    Assert(d_examples_out.size() == results.size());
    Trace("sygus-sui-cterm-debug")
        << "Check enumerator exclusion for " << e << " -> "
        << d_tds->sygusToBuiltin(v) << " based on str.contains." << std::endl;
    std::vector<unsigned> cmp_indices;
    for (unsigned i = 0, size = results.size(); i < size; i++)
    {
      Assert(results[i].isConst());
      Assert(d_examples_out[i].isConst());
      Trace("sygus-sui-cterm-debug")
          << "  " << results[i] << " <> " << d_examples_out[i];
      Node cont = nm->mkNode(STRING_STRCTN, d_examples_out[i], results[i]);
      Node contr = Rewriter::rewrite(cont);
      if (contr == d_false)
      {
        cmp_indices.push_back(i);
        Trace("sygus-sui-cterm-debug") << "...not contained." << std::endl;
      }
      else
      {
        Trace("sygus-sui-cterm-debug") << "...contained." << std::endl;
      }
    }
    if (!cmp_indices.empty())
    {
      // we check invariance with respect to a negative contains test
      NegContainsSygusInvarianceTest ncset;
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
  if (Trace.isOn("sygus-sui-dt-debug"))
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
  EnumTypeInfo& tinfo = d_strategy[f].getEnumTypeInfo(etn);

  // get the enumerator information
  EnumInfo& einfo = d_strategy[f].getEnumInfo(e);

  EnumCache& ecache = d_ecache[e];

  Node ret_dt;
  if (nrole == role_equal)
  {
    if (!x.isReturnValueModified())
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
          ret_dt = constructBestSolvedTerm(subsumed_by);
          indent("sygus-sui-dt", ind);
          Trace("sygus-sui-dt") << "return PBE: success : conditionally solved"
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
      if (d_tds->sygusToBuiltinType(e.getType()).isString())
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
          std::vector<String> ex_vals;
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
            ret_dt = constructBestStringSolvedTerm(str_solved);
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
  }
  else if (nrole == role_string_prefix || nrole == role_string_suffix)
  {
    // check if each return value is a prefix/suffix of all open examples
    if (!x.isReturnValueModified() || x.getCurrentRole() == nrole)
    {
      std::map<Node, std::vector<unsigned> > incr;
      bool isPrefix = nrole == role_string_prefix;
      std::map<Node, unsigned> total_inc;
      std::vector<Node> inc_strs;
      // make the value of the examples
      std::vector<String> ex_vals;
      x.getCurrentStrings(this, d_examples_out, ex_vals);
      if (Trace.isOn("sygus-sui-dt-debug"))
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
        unsigned tot = 0;
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
    std::random_shuffle(snode.d_strats.begin(), snode.d_strats.end());
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
        EnumTypeInfoStrat* etis = snode.d_strats[i];
        snode.d_strats[i] = snode.d_strats[0];
        snode.d_strats[0] = etis;
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

      std::map<unsigned, Node> look_ahead_solved_children;
      std::vector<Node> dt_children_cons;
      bool success = true;

      // for ITE
      Node split_cond_enum;
      int split_cond_res_index = -1;

      for (unsigned sc = 0, size = etis->d_cenum.size(); sc < size; sc++)
      {
        indent("sygus-sui-dt", ind + 1);
        Trace("sygus-sui-dt")
            << "construct PBE child #" << sc << "..." << std::endl;
        Node rec_c;
        std::map<unsigned, Node>::iterator itla =
            look_ahead_solved_children.find(sc);
        if (itla != look_ahead_solved_children.end())
        {
          rec_c = itla->second;
          indent("sygus-sui-dt-debug", ind + 1);
          Trace("sygus-sui-dt-debug")
              << "ConstructPBE: look ahead solved : "
              << d_tds->sygusToBuiltin(rec_c) << std::endl;
        }
        else
        {
          std::pair<Node, NodeRole>& cenum = etis->d_cenum[sc];

          // update the context
          std::vector<Node> prev;
          if (strat == strat_ITE && sc > 0)
          {
            EnumCache& ecache_cond = d_ecache[split_cond_enum];
            Assert(split_cond_res_index >= 0);
            Assert(split_cond_res_index
                   < (int)ecache_cond.d_enum_vals_res.size());
            prev = x.d_vals;
            bool ret = x.updateContext(
                this,
                ecache_cond.d_enum_vals_res[split_cond_res_index],
                sc == 1);
            AlwaysAssert(ret);
          }

          // recurse
          if (strat == strat_ITE && sc == 0)
          {
            Node ce = cenum.first;

            EnumCache& ecache_child = d_ecache[ce];

            // only used if the return value is not modified
            if (!x.isReturnValueModified())
            {
              if (x.d_uinfo.find(ce) == x.d_uinfo.end())
              {
                x.d_uinfo[ce].clear();
                Trace("sygus-sui-dt-debug2")
                    << "  reg : PBE: Look for direct solutions for conditional "
                       "enumerator "
                    << ce << " ... " << std::endl;
                Assert(ecache_child.d_enum_vals.size()
                       == ecache_child.d_enum_vals_res.size());
                for (unsigned i = 1; i <= 2; i++)
                {
                  std::pair<Node, NodeRole>& te_pair = etis->d_cenum[i];
                  Node te = te_pair.first;
                  EnumCache& ecache_te = d_ecache[te];
                  bool branch_pol = (i == 1);
                  // for each condition, get terms that satisfy it in this
                  // branch
                  for (unsigned k = 0, size = ecache_child.d_enum_vals.size();
                       k < size;
                       k++)
                  {
                    Node cond = ecache_child.d_enum_vals[k];
                    std::vector<Node> solved;
                    ecache_te.d_term_trie.getSubsumedBy(
                        ecache_child.d_enum_vals_res[k], branch_pol, solved);
                    Trace("sygus-sui-dt-debug2")
                        << "  reg : PBE: " << d_tds->sygusToBuiltin(cond)
                        << " has " << solved.size() << " solutions in branch "
                        << i << std::endl;
                    if (!solved.empty())
                    {
                      Node slv = constructBestSolvedTerm(solved);
                      Trace("sygus-sui-dt-debug2")
                          << "  reg : PBE: ..." << d_tds->sygusToBuiltin(slv)
                          << " is a solution under branch " << i;
                      Trace("sygus-sui-dt-debug2")
                          << " of condition " << d_tds->sygusToBuiltin(cond)
                          << std::endl;
                      x.d_uinfo[ce].d_look_ahead_sols[cond][i] = slv;
                    }
                  }
                }
              }
            }

            // get the conditionals in the current context : they must be
            // distinguishable
            std::map<int, std::vector<Node> > possible_cond;
            std::map<Node, int> solved_cond;  // stores branch
            ecache_child.d_term_trie.getLeaves(x.d_vals, true, possible_cond);

            std::map<int, std::vector<Node> >::iterator itpc =
                possible_cond.find(0);
            if (itpc != possible_cond.end())
            {
              if (Trace.isOn("sygus-sui-dt-debug"))
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

              // static look ahead conditional : choose conditionals that have
              // solved terms in at least one branch
              //    only applicable if we have not modified the return value
              std::map<int, std::vector<Node> > solved_cond;
              if (!x.isReturnValueModified() && !x.d_uinfo[ce].empty())
              {
                int solve_max = 0;
                for (Node& cond : itpc->second)
                {
                  std::map<Node, std::map<unsigned, Node> >::iterator itla =
                      x.d_uinfo[ce].d_look_ahead_sols.find(cond);
                  if (itla != x.d_uinfo[ce].d_look_ahead_sols.end())
                  {
                    int nsolved = itla->second.size();
                    solve_max = nsolved > solve_max ? nsolved : solve_max;
                    solved_cond[nsolved].push_back(cond);
                  }
                }
                int n = solve_max;
                while (n > 0)
                {
                  if (!solved_cond[n].empty())
                  {
                    rec_c = constructBestSolvedConditional(solved_cond[n]);
                    indent("sygus-sui-dt", ind + 1);
                    Trace("sygus-sui-dt")
                        << "PBE: ITE strategy : choose solved conditional "
                        << d_tds->sygusToBuiltin(rec_c) << " with " << n
                        << " solved children..." << std::endl;
                    std::map<Node, std::map<unsigned, Node> >::iterator itla =
                        x.d_uinfo[ce].d_look_ahead_sols.find(rec_c);
                    Assert(itla != x.d_uinfo[ce].d_look_ahead_sols.end());
                    for (std::pair<const unsigned, Node>& las : itla->second)
                    {
                      look_ahead_solved_children[las.first] = las.second;
                    }
                    break;
                  }
                  n--;
                }
              }

              // otherwise, guess a conditional
              if (rec_c.isNull())
              {
                rec_c = constructBestConditional(itpc->second);
                Assert(!rec_c.isNull());
                indent("sygus-sui-dt", ind);
                Trace("sygus-sui-dt")
                    << "PBE: ITE strategy : choose random conditional "
                    << d_tds->sygusToBuiltin(rec_c) << std::endl;
              }
            }
            else
            {
              // TODO (#1250) : degenerate case where children have different
              // types?
              indent("sygus-sui-dt", ind);
              Trace("sygus-sui-dt") << "return PBE: failed ITE strategy, "
                                       "cannot find a distinguishable condition"
                                    << std::endl;
            }
            if (!rec_c.isNull())
            {
              Assert(ecache_child.d_enum_val_to_index.find(rec_c)
                     != ecache_child.d_enum_val_to_index.end());
              split_cond_res_index = ecache_child.d_enum_val_to_index[rec_c];
              split_cond_enum = ce;
              Assert(split_cond_res_index >= 0);
              Assert(split_cond_res_index
                     < (int)ecache_child.d_enum_vals_res.size());
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

  Assert(ret_dt.isNull() || ret_dt.getType() == e.getType());
  indent("sygus-sui-dt", ind);
  Trace("sygus-sui-dt") << "ConstructPBE: returned " << ret_dt << std::endl;
  return ret_dt;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
