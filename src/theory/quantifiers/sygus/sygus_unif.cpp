/*********************                                                        */
/*! \file sygus_unif.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_unif
 **/

#include "theory/quantifiers/sygus/sygus_unif.h"

#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "util/random.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

UnifContext::UnifContext() : d_has_string_pos(role_invalid)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

bool UnifContext::updateContext(SygusUnif* pbe,
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

bool UnifContext::updateStringPosition(SygusUnif* pbe,
                                       std::vector<unsigned>& pos)
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
  return changed;
}

bool UnifContext::isReturnValueModified()
{
  if (d_has_string_pos != role_invalid)
  {
    return true;
  }
  return false;
}

void UnifContext::initialize(SygusUnif* pbe)
{
  Assert(d_vals.empty());
  Assert(d_str_pos.empty());

  // initialize with #examples
  unsigned sz = pbe->d_examples.size();
  for (unsigned i = 0; i < sz; i++)
  {
    d_vals.push_back(d_true);
  }

  if (!pbe->d_examples_out.empty())
  {
    // output type of the examples
    TypeNode exotn = pbe->d_examples_out[0].getType();

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

void UnifContext::getCurrentStrings(SygusUnif* pbe,
                                    const std::vector<Node>& vals,
                                    std::vector<String>& ex_vals)
{
  bool isPrefix = d_has_string_pos == role_string_prefix;
  String dummy;
  for (unsigned i = 0; i < vals.size(); i++)
  {
    if (d_vals[i] == pbe->d_true)
    {
      Assert(vals[i].isConst());
      unsigned pos_value = d_str_pos[i];
      if (pos_value > 0)
      {
        Assert(d_has_string_pos != role_invalid);
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

bool UnifContext::getStringIncrement(SygusUnif* pbe,
                                     bool isPrefix,
                                     const std::vector<String>& ex_vals,
                                     const std::vector<Node>& vals,
                                     std::vector<unsigned>& inc,
                                     unsigned& tot)
{
  for (unsigned j = 0; j < vals.size(); j++)
  {
    unsigned ival = 0;
    if (d_vals[j] == pbe->d_true)
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
          Trace("sygus-pbe-dt-debug") << "X";
          return false;
        }
      }
      else
      {
        Trace("sygus-pbe-dt-debug") << "X";
        return false;
      }
    }
    Trace("sygus-pbe-dt-debug") << ival;
    tot += ival;
    inc.push_back(ival);
  }
  return true;
}
bool UnifContext::isStringSolved(SygusUnif* pbe,
                                 const std::vector<String>& ex_vals,
                                 const std::vector<Node>& vals)
{
  for (unsigned j = 0; j < vals.size(); j++)
  {
    if (d_vals[j] == pbe->d_true)
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

SygusUnif::SygusUnif()
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

SygusUnif::~SygusUnif() {}

void SygusUnif::initialize(QuantifiersEngine* qe,
                           Node f,
                           std::vector<Node>& enums,
                           std::vector<Node>& lemmas)
{
  Assert(d_candidate.isNull());
  d_candidate = f;
  d_qe = qe;
  d_tds = qe->getTermDatabaseSygus();

  d_strategy.initialize(qe, f, enums, lemmas);
}

void SygusUnif::resetExamples()
{
  d_examples.clear();
  d_examples_out.clear();
  // also clear information in strategy tree
  // TODO
}

void SygusUnif::addExample(const std::vector<Node>& input, Node output)
{
  d_examples.push_back(input);
  d_examples_out.push_back(output);
}

void SygusUnif::notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas)
{
  Node c = d_candidate;
  Assert(!d_examples.empty());
  Assert(d_examples.size() == d_examples_out.size());
  std::map<Node, EnumInfo>::iterator it = d_strategy.d_einfo.find(e);
  Assert(it != d_einfo.end());
  Assert(
      std::find(it->second.d_enum_vals.begin(), it->second.d_enum_vals.end(), v)
      == it->second.d_enum_vals.end());
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
    Trace("sygus-pbe-enum-debug")
        << "...got res = " << res << " from " << bv << std::endl;
    base_results.push_back(res);
  }
  // is it excluded for domain-specific reason?
  std::vector<Node> exp_exc_vec;
  if (getExplanationForEnumeratorExclude(e, v, base_results, exp_exc_vec))
  {
    Assert(!exp_exc_vec.empty());
    exp_exc = exp_exc_vec.size() == 1
                  ? exp_exc_vec[0]
                  : NodeManager::currentNM()->mkNode(AND, exp_exc_vec);
    Trace("sygus-pbe-enum")
        << "  ...fail : term is excluded (domain-specific)" << std::endl;
  }
  else
  {
    // notify all slaves
    Assert(!it->second.d_enum_slave.empty());
    // explanation for why this value should be excluded
    for (unsigned s = 0; s < it->second.d_enum_slave.size(); s++)
    {
      Node xs = it->second.d_enum_slave[s];

      std::map<Node, EnumInfo>::iterator itiv = d_strategy.d_einfo.find(xs);
      Assert(itiv != d_strategy.d_einfo.end());
      EnumInfo& eiv = itiv->second;

      std::map<Node, EnumCache>::iterator itcv = d_ecache.find(xs);
      Assert(itcv != d_ecache.end());
      EnumCache& ecv = itcv->second;

      Trace("sygus-pbe-enum") << "Process " << xs << " from " << s << std::endl;
      // bool prevIsCover = false;
      if (eiv.getRole() == enum_io)
      {
        Trace("sygus-pbe-enum") << "   IO-Eval of ";
        // prevIsCover = eiv.isFeasible();
      }
      else
      {
        Trace("sygus-pbe-enum") << "Evaluation of ";
      }
      Trace("sygus-pbe-enum") << xs << " : ";
      // evaluate all input/output examples
      std::vector<Node> results;
      Node templ = eiv.d_template;
      TNode templ_var = eiv.d_template_arg;
      std::map<Node, bool> cond_vals;
      for (unsigned j = 0, size = base_results.size(); j < size; j++)
      {
        Node res = base_results[j];
        Assert(res.isConst());
        if (!templ.isNull())
        {
          TNode tres = res;
          res = templ.substitute(templ_var, res);
          res = Rewriter::rewrite(res);
          Assert(res.isConst());
        }
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
        if (Trace.isOn("sygus-pbe-enum"))
        {
          if (resb.getType().isBoolean())
          {
            Trace("sygus-pbe-enum") << (resb == d_true ? "1" : "0");
          }
          else
          {
            Trace("sygus-pbe-enum") << "?";
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
            Trace("sygus-pbe-enum")
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
              Trace("sygus-pbe-enum") << "  ...success";
              if (!subsume.empty())
              {
                ecv.d_enum_subsume.insert(
                    ecv.d_enum_subsume.end(), subsume.begin(), subsume.end());
                Trace("sygus-pbe-enum")
                    << " and subsumed " << subsume.size() << " terms";
              }
              Trace("sygus-pbe-enum")
                  << "!   add to PBE pool : " << d_tds->sygusToBuiltin(v)
                  << std::endl;
              keep = true;
            }
            else
            {
              Assert(subsume.empty());
              Trace("sygus-pbe-enum") << "  ...fail : subsumed" << std::endl;
            }
          }
        }
        else
        {
          Trace("sygus-pbe-enum")
              << "  ...fail : it does not satisfy examples." << std::endl;
        }
      }
      else
      {
        // must be unique up to examples
        Node val = ecv.d_term_trie.addCond(v, results, true);
        if (val == v)
        {
          Trace("sygus-pbe-enum") << "  ...success!   add to PBE pool : "
                                  << d_tds->sygusToBuiltin(v) << std::endl;
          keep = true;
        }
        else
        {
          Trace("sygus-pbe-enum")
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
  Trace("sygus-pbe-enum-lemma")
      << "SygusUnif : enumeration exclude lemma : " << exp_exc << std::endl;
  lemmas.push_back(exp_exc);
}

Node SygusUnif::constructSolution()
{
  Node c = d_candidate;
  if (!d_solution.isNull())
  {
    // already has a solution
    return d_solution;
  }
  else
  {
    // only check if an enumerator updated
    if (d_check_sol)
    {
      Trace("sygus-pbe") << "Construct solution, #iterations = " << d_cond_count
                         << std::endl;
      d_check_sol = false;
      // try multiple times if we have done multiple conditions, due to
      // non-determinism
      Node vc;
      for (unsigned i = 0; i <= d_cond_count; i++)
      {
        Trace("sygus-pbe-dt")
            << "ConstructPBE for candidate: " << c << std::endl;
        Node e = d_strategy.getRootEnumerator();
        UnifContext x;
        x.initialize(this);
        Node vcc = constructSolution(e, role_equal, x, 1);
        if (!vcc.isNull())
        {
          if (vc.isNull() || (!vc.isNull()
                              && d_tds->getSygusTermSize(vcc)
                                     < d_tds->getSygusTermSize(vc)))
          {
            Trace("sygus-pbe")
                << "**** PBE SOLVED : " << c << " = " << vcc << std::endl;
            Trace("sygus-pbe") << "...solved at iteration " << i << std::endl;
            vc = vcc;
          }
        }
      }
      if (!vc.isNull())
      {
        d_solution = vc;
        return vc;
      }
      Trace("sygus-pbe") << "...failed to solve." << std::endl;
    }
    return Node::null();
  }
}

// ------------------------------------ solution construction from enumeration

bool SygusUnif::useStrContainsEnumeratorExclude(Node e)
{
  TypeNode xbt = d_tds->sygusToBuiltinType(e.getType());
  if (xbt.isString())
  {
    std::map<Node, bool>::iterator itx = d_use_str_contains_eexc.find(e);
    if (itx != d_use_str_contains_eexc.end())
    {
      return itx->second;
    }
    Trace("sygus-pbe-enum-debug") << "Is " << e << " is str.contains exclusion?"
                                  << std::endl;
    d_use_str_contains_eexc[e] = true;
    std::map<Node, EnumInfo>::iterator itei = d_strategy.d_einfo.find(e);
    Assert(itei != d_strategy.d_einfo.end());
    EnumInfo& ei = itei->second;
    for (const Node& sn : ei.d_enum_slave)
    {
      std::map<Node, EnumInfo>::iterator itv = d_strategy.d_einfo.find(sn);
      EnumRole er = itv->second.getRole();
      if (er != enum_io && er != enum_concat_term)
      {
        Trace("sygus-pbe-enum-debug") << "  incompatible slave : " << sn
                                      << ", role = " << er << std::endl;
        d_use_str_contains_eexc[e] = false;
        return false;
      }
      if (itv->second.isConditional())
      {
        Trace("sygus-pbe-enum-debug")
            << "  conditional slave : " << sn << std::endl;
        d_use_str_contains_eexc[e] = false;
        return false;
      }
    }
    Trace("sygus-pbe-enum-debug")
        << "...can use str.contains exclusion." << std::endl;
    return d_use_str_contains_eexc[e];
  }
  return false;
}

bool SygusUnif::getExplanationForEnumeratorExclude(Node e,
                                                   Node v,
                                                   std::vector<Node>& results,
                                                   std::vector<Node>& exp)
{
  if (useStrContainsEnumeratorExclude(e))
  {
    NodeManager* nm = NodeManager::currentNM();
    // This check whether the example evaluates to something that is larger than
    // the output for some input/output pair. If so, then this term is never
    // useful. We generalize its explanation below.

    if (Trace.isOn("sygus-pbe-cterm-debug"))
    {
      Trace("sygus-pbe-enum") << std::endl;
    }
    // check if all examples had longer length that the output
    Assert(d_examples_out.size() == results.size());
    Trace("sygus-pbe-cterm-debug") << "Check enumerator exclusion for " << e
                                   << " -> " << d_tds->sygusToBuiltin(v)
                                   << " based on str.contains." << std::endl;
    std::vector<unsigned> cmp_indices;
    for (unsigned i = 0, size = results.size(); i < size; i++)
    {
      Assert(results[i].isConst());
      Assert(d_examples_out[i].isConst());
      Trace("sygus-pbe-cterm-debug") << "  " << results[i] << " <> "
                                     << d_examples_out[i];
      Node cont = nm->mkNode(STRING_STRCTN, d_examples_out[i], results[i]);
      Node contr = Rewriter::rewrite(cont);
      if (contr == d_false)
      {
        cmp_indices.push_back(i);
        Trace("sygus-pbe-cterm-debug") << "...not contained." << std::endl;
      }
      else
      {
        Trace("sygus-pbe-cterm-debug") << "...contained." << std::endl;
      }
    }
    if (!cmp_indices.empty())
    {
      // we check invariance with respect to a negative contains test
      NegContainsSygusInvarianceTest ncset;
      ncset.init(e, d_examples, d_examples_out, cmp_indices);
      // construct the generalized explanation
      d_tds->getExplain()->getExplanationFor(e, v, exp, ncset);
      Trace("sygus-pbe-cterm")
          << "PBE-cterm : enumerator exclude " << d_tds->sygusToBuiltin(v)
          << " due to negative containment." << std::endl;
      return true;
    }
  }
  return false;
}

void SygusUnif::EnumCache::addEnumValue(Node v, std::vector<Node>& results)
{
  // should not have been enumerated before
  Assert(d_enum_val_to_index.find(v) == d_enum_val_to_index.end());
  d_enum_val_to_index[v] = d_enum_vals.size();
  d_enum_vals.push_back(v);
  d_enum_vals_res.push_back(results);
}

Node SygusUnif::constructBestSolvedTerm(std::vector<Node>& solved,
                                        UnifContext& x)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestStringSolvedTerm(std::vector<Node>& solved,
                                              UnifContext& x)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestSolvedConditional(std::vector<Node>& solved,
                                               UnifContext& x)
{
  Assert(!solved.empty());
  return solved[0];
}

Node SygusUnif::constructBestConditional(std::vector<Node>& conds,
                                         UnifContext& x)
{
  Assert(!conds.empty());
  double r = Random::getRandom().pickDouble(0.0, 1.0);
  unsigned cindex = r * conds.size();
  if (cindex > conds.size())
  {
    cindex = conds.size() - 1;
  }
  return conds[cindex];
}

Node SygusUnif::constructBestStringToConcat(
    std::vector<Node> strs,
    std::map<Node, unsigned> total_inc,
    std::map<Node, std::vector<unsigned> > incr,
    UnifContext& x)
{
  Assert(!strs.empty());
  std::random_shuffle(strs.begin(), strs.end());
  // prefer one that has incremented by more than 0
  for (const Node& ns : strs)
  {
    if (total_inc[ns] > 0)
    {
      return ns;
    }
  }
  return strs[0];
}

Node SygusUnif::constructSolution(Node e,
                                  NodeRole nrole,
                                  UnifContext& x,
                                  int ind)
{
  TypeNode etn = e.getType();
  if (Trace.isOn("sygus-pbe-dt-debug"))
  {
    indent("sygus-pbe-dt-debug", ind);
    Trace("sygus-pbe-dt-debug") << "ConstructPBE: (" << e << ", " << nrole
                                << ") for type " << etn << " in context ";
    print_val("sygus-pbe-dt-debug", x.d_vals);
    if (x.d_has_string_pos != role_invalid)
    {
      Trace("sygus-pbe-dt-debug") << ", string context [" << x.d_has_string_pos;
      for (unsigned i = 0, size = x.d_str_pos.size(); i < size; i++)
      {
        Trace("sygus-pbe-dt-debug") << " " << x.d_str_pos[i];
      }
      Trace("sygus-pbe-dt-debug") << "]";
    }
    Trace("sygus-pbe-dt-debug") << std::endl;
  }
  // enumerator type info
  std::map<TypeNode, EnumTypeInfo>::iterator itt = d_strategy.d_tinfo.find(etn);
  Assert(itt != d_strategy.d_tinfo.end());
  EnumTypeInfo& tinfo = itt->second;

  // get the enumerator information
  std::map<Node, EnumInfo>::iterator itn = d_strategy.d_einfo.find(e);
  Assert(itn != d_strategy.d_einfo.end());
  EnumInfo& einfo = itn->second;

  std::map<Node, EnumCache>::iterator itc = d_ecache.find(e);
  Assert(itc != d_ecache.end());
  EnumCache& ecache = itc->second;

  Node ret_dt;
  if (nrole == role_equal)
  {
    if (!x.isReturnValueModified())
    {
      if (ecache.isSolved())
      {
        // this type has a complete solution
        ret_dt = ecache.getSolved();
        indent("sygus-pbe-dt", ind);
        Trace("sygus-pbe-dt") << "return PBE: success : solved "
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
          ret_dt = constructBestSolvedTerm(subsumed_by, x);
          indent("sygus-pbe-dt", ind);
          Trace("sygus-pbe-dt") << "return PBE: success : conditionally solved"
                                << d_tds->sygusToBuiltin(ret_dt) << std::endl;
        }
        else
        {
          indent("sygus-pbe-dt-debug", ind);
          Trace("sygus-pbe-dt-debug")
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
        bool success = true;
        std::map<Node, EnumCache>::iterator itet;
        std::map<EnumRole, Node>::iterator itnt =
            tinfo.d_enum.find(enum_concat_term);
        if (itnt != itt->second.d_enum.end())
        {
          Node et = itnt->second;
          itet = d_ecache.find(et);
          Assert(itet != d_ecache.end());
        }
        else
        {
          success = false;
        }
        if (success)
        {
          EnumCache& ecache = itet->second;
          // get the current examples
          std::vector<String> ex_vals;
          x.getCurrentStrings(this, d_examples_out, ex_vals);
          Assert(itn->second.d_enum_vals.size()
                 == itn->second.d_enum_vals_res.size());

          // test each example in the term enumerator for the type
          std::vector<Node> str_solved;
          for (unsigned i = 0, size = ecache.d_enum_vals.size(); i < size; i++)
          {
            if (x.isStringSolved(this, ex_vals, ecache.d_enum_vals_res[i]))
            {
              str_solved.push_back(ecache.d_enum_vals[i]);
            }
          }
          if (!str_solved.empty())
          {
            ret_dt = constructBestStringSolvedTerm(str_solved, x);
            indent("sygus-pbe-dt", ind);
            Trace("sygus-pbe-dt") << "return PBE: success : string solved "
                                  << d_tds->sygusToBuiltin(ret_dt) << std::endl;
          }
          else
          {
            indent("sygus-pbe-dt-debug", ind);
            Trace("sygus-pbe-dt-debug")
                << "  ...not currently string solved." << std::endl;
          }
        }
      }
    }
  }
  else if (nrole == role_string_prefix || nrole == role_string_suffix)
  {
    // check if each return value is a prefix/suffix of all open examples
    if (!x.isReturnValueModified() || x.d_has_string_pos == nrole)
    {
      std::map<Node, std::vector<unsigned> > incr;
      bool isPrefix = nrole == role_string_prefix;
      std::map<Node, unsigned> total_inc;
      std::vector<Node> inc_strs;
      // make the value of the examples
      std::vector<String> ex_vals;
      x.getCurrentStrings(this, d_examples_out, ex_vals);
      if (Trace.isOn("sygus-pbe-dt-debug"))
      {
        indent("sygus-pbe-dt-debug", ind);
        Trace("sygus-pbe-dt-debug") << "current strings : " << std::endl;
        for (unsigned i = 0, size = ex_vals.size(); i < size; i++)
        {
          indent("sygus-pbe-dt-debug", ind + 1);
          Trace("sygus-pbe-dt-debug") << ex_vals[i] << std::endl;
        }
      }

      // check if there is a value for which is a prefix/suffix of all active
      // examples
      Assert(ecache.d_enum_vals.size() == ecache.d_enum_vals_res.size());

      for (unsigned i = 0, size = ecache.d_enum_vals.size(); i < size; i++)
      {
        Node val_t = ecache.d_enum_vals[i];
        Assert(incr.find(val_t) == incr.end());
        indent("sygus-pbe-dt-debug", ind);
        Trace("sygus-pbe-dt-debug")
            << "increment string values : " << val_t << " : ";
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
          Trace("sygus-pbe-dt-debug") << "...fail" << std::endl;
        }
        else
        {
          total_inc[val_t] = tot;
          inc_strs.push_back(val_t);
          Trace("sygus-pbe-dt-debug")
              << "...success, total increment = " << tot << std::endl;
        }
      }

      if (!incr.empty())
      {
        ret_dt = constructBestStringToConcat(inc_strs, total_inc, incr, x);
        Assert(!ret_dt.isNull());
        indent("sygus-pbe-dt", ind);
        Trace("sygus-pbe-dt")
            << "PBE: CONCAT strategy : choose " << (isPrefix ? "pre" : "suf")
            << "fix value " << d_tds->sygusToBuiltin(ret_dt) << std::endl;
        // update the context
        bool ret = x.updateStringPosition(this, incr[ret_dt]);
        AlwaysAssert(ret == (total_inc[ret_dt] > 0));
        x.d_has_string_pos = nrole;
      }
      else
      {
        indent("sygus-pbe-dt", ind);
        Trace("sygus-pbe-dt") << "PBE: failed CONCAT strategy, no values are "
                              << (isPrefix ? "pre" : "suf")
                              << "fix of all examples." << std::endl;
      }
    }
    else
    {
      indent("sygus-pbe-dt", ind);
      Trace("sygus-pbe-dt")
          << "PBE: failed CONCAT strategy, prefix/suffix mismatch."
          << std::endl;
    }
  }
  if (ret_dt.isNull() && !einfo.isTemplated())
  {
    // we will try a single strategy
    EnumTypeInfoStrat* etis = nullptr;
    std::map<NodeRole, StrategyNode>::iterator itsn =
        tinfo.d_snodes.find(nrole);
    if (itsn != tinfo.d_snodes.end())
    {
      // strategy info
      StrategyNode& snode = itsn->second;
      if (x.d_visit_role[e].find(nrole) == x.d_visit_role[e].end())
      {
        x.d_visit_role[e][nrole] = true;
        // try a random strategy
        if (snode.d_strats.size() > 1)
        {
          std::random_shuffle(snode.d_strats.begin(), snode.d_strats.end());
        }
        // get an eligible strategy index
        unsigned sindex = 0;
        while (sindex < snode.d_strats.size()
               && !snode.d_strats[sindex]->isValid(&x))
        {
          sindex++;
        }
        // if we found a eligible strategy
        if (sindex < snode.d_strats.size())
        {
          etis = snode.d_strats[sindex];
        }
      }
    }
    if (etis != nullptr)
    {
      StrategyType strat = etis->d_this;
      indent("sygus-pbe-dt", ind + 1);
      Trace("sygus-pbe-dt")
          << "...try STRATEGY " << strat << "..." << std::endl;

      std::map<unsigned, Node> look_ahead_solved_children;
      std::vector<Node> dt_children_cons;
      bool success = true;

      // for ITE
      Node split_cond_enum;
      int split_cond_res_index = -1;

      for (unsigned sc = 0, size = etis->d_cenum.size(); sc < size; sc++)
      {
        indent("sygus-pbe-dt", ind + 1);
        Trace("sygus-pbe-dt")
            << "construct PBE child #" << sc << "..." << std::endl;
        Node rec_c;
        std::map<unsigned, Node>::iterator itla =
            look_ahead_solved_children.find(sc);
        if (itla != look_ahead_solved_children.end())
        {
          rec_c = itla->second;
          indent("sygus-pbe-dt-debug", ind + 1);
          Trace("sygus-pbe-dt-debug")
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
            std::map<Node, EnumCache>::iterator itnc =
                d_ecache.find(split_cond_enum);
            Assert(itnc != d_einfo.end());
            Assert(split_cond_res_index >= 0);
            Assert(split_cond_res_index
                   < (int)itnc->second.d_enum_vals_res.size());
            prev = x.d_vals;
            bool ret = x.updateContext(
                this,
                itnc->second.d_enum_vals_res[split_cond_res_index],
                sc == 1);
            AlwaysAssert(ret);
          }

          // recurse
          if (strat == strat_ITE && sc == 0)
          {
            Node ce = cenum.first;

            // register the condition enumerator
            // std::map<Node, EnumInfo>::iterator itnc =
            // d_strategy.d_einfo.find(ce);
            // Assert(itnc != d_strategy.d_einfo.end());
            // EnumInfo& einfo_child = itnc->second;

            std::map<Node, EnumCache>::iterator itcc = d_ecache.find(ce);
            Assert(itnc != d_ecache.end());
            EnumCache& ecache_child = itcc->second;

            // only used if the return value is not modified
            if (!x.isReturnValueModified())
            {
              if (x.d_uinfo.find(ce) == x.d_uinfo.end())
              {
                Trace("sygus-pbe-dt-debug2")
                    << "  reg : PBE: Look for direct solutions for conditional "
                       "enumerator "
                    << ce << " ... " << std::endl;
                Assert(ecache_child.d_enum_vals.size()
                       == ecache_child.d_enum_vals_res.size());
                for (unsigned i = 1; i <= 2; i++)
                {
                  std::pair<Node, NodeRole>& te_pair = etis->d_cenum[i];
                  Node te = te_pair.first;
                  std::map<Node, EnumCache>::iterator itnt = d_ecache.find(te);
                  Assert(itnt != d_ecache.end());
                  bool branch_pol = (i == 1);
                  // for each condition, get terms that satisfy it in this
                  // branch
                  for (unsigned k = 0, size = ecache_child.d_enum_vals.size();
                       k < size;
                       k++)
                  {
                    Node cond = ecache_child.d_enum_vals[k];
                    std::vector<Node> solved;
                    itnt->second.d_term_trie.getSubsumedBy(
                        ecache_child.d_enum_vals_res[k], branch_pol, solved);
                    Trace("sygus-pbe-dt-debug2")
                        << "  reg : PBE: " << d_tds->sygusToBuiltin(cond)
                        << " has " << solved.size() << " solutions in branch "
                        << i << std::endl;
                    if (!solved.empty())
                    {
                      Node slv = constructBestSolvedTerm(solved, x);
                      Trace("sygus-pbe-dt-debug2")
                          << "  reg : PBE: ..." << d_tds->sygusToBuiltin(slv)
                          << " is a solution under branch " << i;
                      Trace("sygus-pbe-dt-debug2")
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
              if (Trace.isOn("sygus-pbe-dt-debug"))
              {
                indent("sygus-pbe-dt-debug", ind + 1);
                Trace("sygus-pbe-dt-debug")
                    << "PBE : We have " << itpc->second.size()
                    << " distinguishable conditionals:" << std::endl;
                for (Node& cond : itpc->second)
                {
                  indent("sygus-pbe-dt-debug", ind + 2);
                  Trace("sygus-pbe-dt-debug")
                      << d_tds->sygusToBuiltin(cond) << std::endl;
                }
              }

              // static look ahead conditional : choose conditionals that have
              // solved terms in at least one branch
              //    only applicable if we have not modified the return value
              std::map<int, std::vector<Node> > solved_cond;
              if (!x.isReturnValueModified())
              {
                Assert(x.d_uinfo.find(ce) != x.d_uinfo.end());
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
                    rec_c = constructBestSolvedConditional(solved_cond[n], x);
                    indent("sygus-pbe-dt", ind + 1);
                    Trace("sygus-pbe-dt")
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
                rec_c = constructBestConditional(itpc->second, x);
                Assert(!rec_c.isNull());
                indent("sygus-pbe-dt", ind);
                Trace("sygus-pbe-dt")
                    << "PBE: ITE strategy : choose random conditional "
                    << d_tds->sygusToBuiltin(rec_c) << std::endl;
              }
            }
            else
            {
              // TODO (#1250) : degenerate case where children have different
              // types?
              indent("sygus-pbe-dt", ind);
              Trace("sygus-pbe-dt") << "return PBE: failed ITE strategy, "
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
            rec_c = constructSolution(cenum.first, cenum.second, x, ind + 2);
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
        indent("sygus-pbe-dt-debug", ind);
        Trace("sygus-pbe-dt-debug")
            << "PBE: success : constructed for strategy " << strat << std::endl;
      }
      else
      {
        indent("sygus-pbe-dt-debug", ind);
        Trace("sygus-pbe-dt-debug")
            << "PBE: failed for strategy " << strat << std::endl;
      }
    }
  }

  if (!ret_dt.isNull())
  {
    Assert(ret_dt.getType() == e.getType());
  }
  indent("sygus-pbe-dt", ind);
  Trace("sygus-pbe-dt") << "ConstructPBE: returned " << ret_dt << std::endl;
  return ret_dt;
}

void SygusUnif::indent(const char* c, int ind)
{
  if (Trace.isOn(c))
  {
    for (int i = 0; i < ind; i++)
    {
      Trace(c) << "  ";
    }
  }
}

void SygusUnif::print_val(const char* c, std::vector<Node>& vals, bool pol)
{
  if (Trace.isOn(c))
  {
    for (unsigned i = 0; i < vals.size(); i++)
    {
      Trace(c) << ((pol ? vals[i].getConst<bool>() : !vals[i].getConst<bool>())
                       ? "1"
                       : "0");
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
