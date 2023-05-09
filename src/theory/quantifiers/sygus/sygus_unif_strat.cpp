/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus_unif_strat.
 */

#include "theory/quantifiers/sygus/sygus_unif_strat.h"

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/skolem_manager.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/sygus/sygus_eval_unfold.h"
#include "theory/quantifiers/sygus/sygus_unif.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

std::ostream& operator<<(std::ostream& os, EnumRole r)
{
  switch (r)
  {
    case enum_invalid: os << "INVALID"; break;
    case enum_io: os << "IO"; break;
    case enum_ite_condition: os << "CONDITION"; break;
    case enum_concat_term: os << "CTERM"; break;
    default: os << "enum_" << static_cast<unsigned>(r); break;
  }
  return os;
}

std::ostream& operator<<(std::ostream& os, NodeRole r)
{
  switch (r)
  {
    case role_equal: os << "equal"; break;
    case role_string_prefix: os << "string_prefix"; break;
    case role_string_suffix: os << "string_suffix"; break;
    case role_ite_condition: os << "ite_condition"; break;
    default: os << "role_" << static_cast<unsigned>(r); break;
  }
  return os;
}

EnumRole getEnumeratorRoleForNodeRole(NodeRole r)
{
  switch (r)
  {
    case role_equal: return enum_io; break;
    case role_string_prefix: return enum_concat_term; break;
    case role_string_suffix: return enum_concat_term; break;
    case role_ite_condition: return enum_ite_condition; break;
    default: break;
  }
  return enum_invalid;
}

std::ostream& operator<<(std::ostream& os, StrategyType st)
{
  switch (st)
  {
    case strat_ITE: os << "ITE"; break;
    case strat_CONCAT_PREFIX: os << "CONCAT_PREFIX"; break;
    case strat_CONCAT_SUFFIX: os << "CONCAT_SUFFIX"; break;
    case strat_ID: os << "ID"; break;
    default: os << "strat_" << static_cast<unsigned>(st); break;
  }
  return os;
}

void SygusUnifStrategy::initialize(TermDbSygus* tds,
                                   Node f,
                                   std::vector<Node>& enums)
{
  Assert(d_candidate.isNull());
  d_candidate = f;
  d_root = f.getType();
  d_tds = tds;

  // collect the enumerator types and form the strategy
  buildStrategyGraph(d_root, role_equal);
  // add the enumerators
  enums.insert(enums.end(), d_esym_list.begin(), d_esym_list.end());
  // finish the initialization of the strategy
  // this computes if each node is conditional
  std::map<Node, std::map<NodeRole, bool> > visited;
  finishInit(getRootEnumerator(), role_equal, visited, false);
}

void SygusUnifStrategy::initializeType(TypeNode tn)
{
  Trace("sygus-unif") << "SygusUnifStrategy: initialize : " << tn << " for "
                      << d_candidate << std::endl;
  d_tinfo[tn].d_this_type = tn;
}

Node SygusUnifStrategy::getRootEnumerator() const
{
  std::map<TypeNode, EnumTypeInfo>::const_iterator itt = d_tinfo.find(d_root);
  Assert(itt != d_tinfo.end());
  std::map<EnumRole, Node>::const_iterator it =
      itt->second.d_enum.find(enum_io);
  Assert(it != itt->second.d_enum.end());
  return it->second;
}

EnumInfo& SygusUnifStrategy::getEnumInfo(Node e)
{
  std::map<Node, EnumInfo>::iterator it = d_einfo.find(e);
  Assert(it != d_einfo.end());
  return it->second;
}

EnumTypeInfo& SygusUnifStrategy::getEnumTypeInfo(TypeNode tn)
{
  Trace("sygus-unif") << "SygusUnifStrategy: get : " << tn << " for "
                      << d_candidate << std::endl;
  std::map<TypeNode, EnumTypeInfo>::iterator it = d_tinfo.find(tn);
  Assert(it != d_tinfo.end());
  return it->second;
}
// ----------------------------- establishing enumeration types

void SygusUnifStrategy::registerStrategyPoint(Node et,
                                           TypeNode tn,
                                           EnumRole enum_role,
                                           bool inSearch)
{
  if (d_einfo.find(et) == d_einfo.end())
  {
    Trace("sygus-unif-debug")
        << "...register " << et << " for " << tn.getDType().getName();
    Trace("sygus-unif-debug") << ", role = " << enum_role
                              << ", in search = " << inSearch << std::endl;
    d_einfo[et].initialize(enum_role);
    // if we are actually enumerating this (could be a compound node in the
    // strategy)
    if (inSearch)
    {
      std::map<TypeNode, Node>::iterator itn = d_master_enum.find(tn);
      if (itn == d_master_enum.end())
      {
        // use this for the search
        d_master_enum[tn] = et;
        d_esym_list.push_back(et);
        d_einfo[et].d_enum_slave.push_back(et);
      }
      else
      {
        Trace("sygus-unif-debug") << "Make " << et << " a slave of "
                                  << itn->second << std::endl;
        d_einfo[itn->second].d_enum_slave.push_back(et);
      }
    }
  }
}

void SygusUnifStrategy::buildStrategyGraph(TypeNode tn, NodeRole nrole)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  if (d_tinfo.find(tn) == d_tinfo.end())
  {
    // register type
    Trace("sygus-unif") << "Register enumerating type : " << tn << std::endl;
    initializeType(tn);
  }
  EnumTypeInfo& eti = d_tinfo[tn];
  std::map<NodeRole, StrategyNode>::iterator itsn = eti.d_snodes.find(nrole);
  if (itsn != eti.d_snodes.end())
  {
    // already initialized
    return;
  }
  StrategyNode& snode = eti.d_snodes[nrole];

  // get the enumerator for this
  EnumRole erole = getEnumeratorRoleForNodeRole(nrole);

  Node ee;
  std::map<EnumRole, Node>::iterator iten = eti.d_enum.find(erole);
  if (iten == eti.d_enum.end())
  {
    ee = sm->mkDummySkolem("ee", tn);
    eti.d_enum[erole] = ee;
    Trace("sygus-unif-debug")
        << "...enumerator " << ee << " for " << tn.getDType().getName()
        << ", role = " << erole << std::endl;
  }
  else
  {
    ee = iten->second;
  }

  // roles that we do not recurse on
  if (nrole == role_ite_condition)
  {
    Trace("sygus-unif-debug") << "...this register (non-io)" << std::endl;
    registerStrategyPoint(ee, tn, erole, true);
    return;
  }

  // look at information on how we will construct solutions for this type
  // we know this is a sygus datatype since it is either the top-level type
  // in the strategy graph, or was recursed by a strategy we inferred.
  Assert(tn.isDatatype());
  const DType& dt = tn.getDType();
  Assert(dt.isSygus());

  std::map<Node, std::vector<StrategyType> > cop_to_strat;
  std::map<Node, unsigned> cop_to_cindex;
  std::map<Node, std::map<unsigned, Node> > cop_to_child_templ;
  std::map<Node, std::map<unsigned, Node> > cop_to_child_templ_arg;
  std::map<Node, std::vector<unsigned> > cop_to_carg_list;
  std::map<Node, std::vector<TypeNode> > cop_to_child_types;
  std::map<Node, std::vector<Node> > cop_to_sks;

  // whether we will enumerate the current type
  bool search_this = false;
  for (unsigned j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
  {
    Node cop = dt[j].getConstructor();
    Node op = dt[j].getSygusOp();
    Trace("sygus-unif-debug") << "--- Infer strategy from " << cop
                              << " with sygus op " << op << "..." << std::endl;

    // expand the evaluation to see if this constuctor induces a strategy
    std::vector<Node> utchildren;
    utchildren.push_back(cop);
    std::vector<Node> sks;
    std::vector<TypeNode> sktns;
    for (unsigned k = 0, nargs = dt[j].getNumArgs(); k < nargs; k++)
    {
      TypeNode ttn = dt[j][k].getRangeType();
      Node kv = sm->mkDummySkolem("ut", ttn);
      sks.push_back(kv);
      cop_to_sks[cop].push_back(kv);
      sktns.push_back(ttn);
      utchildren.push_back(kv);
    }
    Node ut = nm->mkNode(APPLY_CONSTRUCTOR, utchildren);
    std::vector<Node> echildren;
    echildren.push_back(ut);
    Node sbvl = dt.getSygusVarList();
    for (const Node& sbv : sbvl)
    {
      echildren.push_back(sbv);
    }
    Node eut = nm->mkNode(DT_SYGUS_EVAL, echildren);
    Trace("sygus-unif-debug2") << "  Test evaluation of " << eut << "..."
                               << std::endl;
    eut = d_tds->rewriteNode(eut);
    Trace("sygus-unif-debug2") << "  ...got " << eut;
    Trace("sygus-unif-debug2") << ", type : " << eut.getType() << std::endl;

    // candidate strategy
    if (eut.getKind() == ITE)
    {
      cop_to_strat[cop].push_back(strat_ITE);
    }
    else if (eut.getKind() == STRING_CONCAT)
    {
      if (nrole != role_string_suffix)
      {
        cop_to_strat[cop].push_back(strat_CONCAT_PREFIX);
      }
      if (nrole != role_string_prefix)
      {
        cop_to_strat[cop].push_back(strat_CONCAT_SUFFIX);
      }
    }
    else if (dt[j].isSygusIdFunc())
    {
      cop_to_strat[cop].push_back(strat_ID);
    }

    // the kinds for which there is a strategy
    if (cop_to_strat.find(cop) != cop_to_strat.end())
    {
      // infer an injection from the arguments of the datatype
      std::map<unsigned, unsigned> templ_injection;
      std::vector<Node> vs;
      std::vector<Node> ss;
      std::map<Node, unsigned> templ_var_index;
      for (unsigned k = 0, sksize = sks.size(); k < sksize; k++)
      {
        Assert(sks[k].getType().isDatatype());
        echildren[0] = sks[k];
        Trace("sygus-unif-debug2") << "...set eval dt to " << sks[k]
                                   << std::endl;
        Node esk = nm->mkNode(DT_SYGUS_EVAL, echildren);
        vs.push_back(esk);
        Node tvar = sm->mkDummySkolem("templ", esk.getType());
        templ_var_index[tvar] = k;
        Trace("sygus-unif-debug2") << "* template inference : looking for "
                                   << tvar << " for arg " << k << std::endl;
        ss.push_back(tvar);
        Trace("sygus-unif-debug2") << "* substitute : " << esk << " -> " << tvar
                                   << std::endl;
      }
      eut = eut.substitute(vs.begin(), vs.end(), ss.begin(), ss.end());
      Trace("sygus-unif-debug2") << "Constructor " << j << ", base term is "
                                 << eut << std::endl;
      std::map<unsigned, Node> test_args;
      if (dt[j].isSygusIdFunc())
      {
        test_args[0] = eut;
      }
      else
      {
        for (unsigned k = 0, size = eut.getNumChildren(); k < size; k++)
        {
          test_args[k] = eut[k];
        }
      }

      // TODO : prefix grouping prefix/suffix
      bool isAssoc = TermUtil::isAssoc(eut.getKind());
      Trace("sygus-unif-debug2") << eut.getKind() << " isAssoc = " << isAssoc
                                 << std::endl;
      std::map<unsigned, std::vector<unsigned> > assoc_combine;
      std::vector<unsigned> assoc_waiting;
      int assoc_last_valid_index = -1;
      for (std::pair<const unsigned, Node>& ta : test_args)
      {
        unsigned k = ta.first;
        Node eut_c = ta.second;
        // success if we can find a injection from args to sygus args
        if (!inferTemplate(k, eut_c, templ_var_index, templ_injection))
        {
          Trace("sygus-unif-debug")
              << "...fail: could not find injection (range)." << std::endl;
          cop_to_strat.erase(cop);
          break;
        }
        std::map<unsigned, unsigned>::iterator itti = templ_injection.find(k);
        if (itti != templ_injection.end())
        {
          // if associative, combine arguments if it is the same variable
          if (isAssoc && assoc_last_valid_index >= 0
              && itti->second == templ_injection[assoc_last_valid_index])
          {
            templ_injection.erase(k);
            assoc_combine[assoc_last_valid_index].push_back(k);
          }
          else
          {
            assoc_last_valid_index = (int)k;
            if (!assoc_waiting.empty())
            {
              assoc_combine[k].insert(assoc_combine[k].end(),
                                      assoc_waiting.begin(),
                                      assoc_waiting.end());
              assoc_waiting.clear();
            }
            assoc_combine[k].push_back(k);
          }
        }
        else
        {
          // a ground argument
          if (!isAssoc)
          {
            Trace("sygus-unif-debug")
                << "...fail: could not find injection (functional)."
                << std::endl;
            cop_to_strat.erase(cop);
            break;
          }
          else
          {
            if (assoc_last_valid_index >= 0)
            {
              assoc_combine[assoc_last_valid_index].push_back(k);
            }
            else
            {
              assoc_waiting.push_back(k);
            }
          }
        }
      }
      if (cop_to_strat.find(cop) != cop_to_strat.end())
      {
        // construct the templates
        if (!assoc_waiting.empty())
        {
          // could not find a way to fit some arguments into injection
          cop_to_strat.erase(cop);
        }
        else
        {
          for (std::pair<const unsigned, Node>& ta : test_args)
          {
            unsigned k = ta.first;
            Trace("sygus-unif-debug2") << "- processing argument " << k << "..."
                                       << std::endl;
            if (templ_injection.find(k) != templ_injection.end())
            {
              unsigned sk_index = templ_injection[k];
              if (std::find(cop_to_carg_list[cop].begin(),
                            cop_to_carg_list[cop].end(),
                            sk_index)
                  == cop_to_carg_list[cop].end())
              {
                cop_to_carg_list[cop].push_back(sk_index);
              }
              else
              {
                Trace("sygus-unif-debug") << "...fail: duplicate argument used"
                                          << std::endl;
                cop_to_strat.erase(cop);
                break;
              }
              // also store the template information, if necessary
              Node teut;
              if (isAssoc)
              {
                std::vector<unsigned>& ac = assoc_combine[k];
                Assert(!ac.empty());
                std::vector<Node> children;
                for (unsigned ack = 0, size_ac = ac.size(); ack < size_ac;
                     ack++)
                {
                  children.push_back(eut[ac[ack]]);
                }
                teut = children.size() == 1
                           ? children[0]
                           : nm->mkNode(eut.getKind(), children);
                teut = rewrite(teut);
              }
              else
              {
                teut = ta.second;
              }

              if (!teut.isVar())
              {
                cop_to_child_templ[cop][k] = teut;
                cop_to_child_templ_arg[cop][k] = ss[sk_index];
                Trace("sygus-unif-debug")
                    << "  Arg " << k << " (template : " << teut << " arg "
                    << ss[sk_index] << "), index " << sk_index << std::endl;
              }
              else
              {
                Trace("sygus-unif-debug") << "  Arg " << k << ", index "
                                          << sk_index << std::endl;
                Assert(teut == ss[sk_index]);
              }
            }
            else
            {
              Assert(isAssoc);
            }
          }
        }
      }
    }
    
    std::map<Node, std::vector<StrategyType> >::iterator itcs = cop_to_strat.find(cop);
    if (itcs != cop_to_strat.end())
    {
      Trace("sygus-unif") << "-> constructor " << cop
                          << " matches strategy for " << eut.getKind() << "..."
                          << std::endl;
      // collect children types
      for (unsigned k = 0, size = cop_to_carg_list[cop].size(); k < size; k++)
      {
        TypeNode ctn = sktns[cop_to_carg_list[cop][k]];
        Trace("sygus-unif-debug") << "   Child type " << k << " : "
                                  << ctn.getDType().getName() << std::endl;
        cop_to_child_types[cop].push_back(ctn);
      }
      // if there are checks on the consistency of child types wrt strategies,
      // these should be enforced here. We currently have none.
    }
    if (cop_to_strat.find(cop) == cop_to_strat.end())
    {
      Trace("sygus-unif") << "...constructor " << cop
                          << " does not correspond to a strategy." << std::endl;
      search_this = true;
    }
  }

  // check whether we should also enumerate the current type
  Trace("sygus-unif-debug2") << "  register this strategy ..." << std::endl;
  registerStrategyPoint(ee, tn, erole, search_this);

  if (cop_to_strat.empty())
  {
    Trace("sygus-unif") << "...consider " << dt.getName() << " a basic type"
                        << std::endl;
  }
  else
  {
    for (std::pair<const Node, std::vector<StrategyType> >& cstr : cop_to_strat)
    {
      Node cop = cstr.first;
      Trace("sygus-unif-debug") << "Constructor " << cop << " has "
                                << cstr.second.size() << " strategies..."
                                << std::endl;
      for (unsigned s = 0, ssize = cstr.second.size(); s < ssize; s++)
      {
        EnumTypeInfoStrat* cons_strat = new EnumTypeInfoStrat;
        StrategyType strat = cstr.second[s];

        cons_strat->d_this = strat;
        cons_strat->d_cons = cop;
        Trace("sygus-unif-debug") << "Process strategy #" << s
                                  << " for operator : " << cop << " : " << strat
                                  << std::endl;
        Assert(cop_to_child_types.find(cop) != cop_to_child_types.end());
        std::vector<TypeNode>& childTypes = cop_to_child_types[cop];
        Assert(cop_to_carg_list.find(cop) != cop_to_carg_list.end());
        std::vector<unsigned>& cargList = cop_to_carg_list[cop];

        std::vector<Node> sol_templ_children;
        sol_templ_children.resize(cop_to_sks[cop].size());

        for (unsigned j = 0, csize = childTypes.size(); j < csize; j++)
        {
          // calculate if we should allocate a new enumerator : should be true
          // if we have a new role
          NodeRole nrole_c = nrole;
          if (strat == strat_ITE)
          {
            if (j == 0)
            {
              nrole_c = role_ite_condition;
            }
          }
          else if (strat == strat_CONCAT_PREFIX)
          {
            if ((j + 1) < childTypes.size())
            {
              nrole_c = role_string_prefix;
            }
          }
          else if (strat == strat_CONCAT_SUFFIX)
          {
            if (j > 0)
            {
              nrole_c = role_string_suffix;
            }
          }
          // in all other cases, role is same as parent

          // register the child type
          TypeNode ct = childTypes[j];
          Node csk = cop_to_sks[cop][cargList[j]];
          cons_strat->d_sol_templ_args.push_back(csk);
          sol_templ_children[cargList[j]] = csk;

          EnumRole erole_c = getEnumeratorRoleForNodeRole(nrole_c);
          // make the enumerator
          Node et;
          // Build the strategy recursively, regardless of whether the
          // enumerator is templated.
          buildStrategyGraph(ct, nrole_c);
          if (cop_to_child_templ[cop].find(j) != cop_to_child_templ[cop].end())
          {
            // it is templated, allocate a fresh variable
            et = sm->mkDummySkolem("et", ct);
            Trace("sygus-unif-debug") << "...enumerate " << et << " of type "
                                      << ct.getDType().getName();
            Trace("sygus-unif-debug") << " for arg " << j << " of "
                                      << tn.getDType().getName() << std::endl;
            registerStrategyPoint(et, ct, erole_c, true);
            d_einfo[et].d_template = cop_to_child_templ[cop][j];
            d_einfo[et].d_template_arg = cop_to_child_templ_arg[cop][j];
            Assert(!d_einfo[et].d_template.isNull());
            Assert(!d_einfo[et].d_template_arg.isNull());
          }
          else
          {
            Trace("sygus-unif-debug")
                << "...child type enumerate " << ct.getDType().getName()
                << ", node role = " << nrole_c << std::endl;
            // otherwise use the previous
            Assert(d_tinfo[ct].d_enum.find(erole_c)
                   != d_tinfo[ct].d_enum.end());
            et = d_tinfo[ct].d_enum[erole_c];
          }
          Trace("sygus-unif-debug") << "Register child enumerator " << et
                                    << ", arg " << j << " of " << cop
                                    << ", role = " << erole_c << std::endl;
          Assert(!et.isNull());
          cons_strat->d_cenum.push_back(std::pair<Node, NodeRole>(et, nrole_c));
        }
        // children that are unused in the strategy can be arbitrary
        for (unsigned j = 0, stsize = sol_templ_children.size(); j < stsize;
             j++)
        {
          if (sol_templ_children[j].isNull())
          {
            sol_templ_children[j] =
                nm->mkGroundTerm(cop_to_sks[cop][j].getType());
          }
        }
        sol_templ_children.insert(sol_templ_children.begin(), cop);
        cons_strat->d_sol_templ =
            nm->mkNode(APPLY_CONSTRUCTOR, sol_templ_children);
        if (strat == strat_CONCAT_SUFFIX)
        {
          std::reverse(cons_strat->d_cenum.begin(), cons_strat->d_cenum.end());
          std::reverse(cons_strat->d_sol_templ_args.begin(),
                       cons_strat->d_sol_templ_args.end());
        }
        if (TraceIsOn("sygus-unif"))
        {
          Trace("sygus-unif") << "Initialized strategy " << strat;
          Trace("sygus-unif")
              << " for " << tn.getDType().getName() << ", operator " << cop;
          Trace("sygus-unif") << ", #children = " << cons_strat->d_cenum.size()
                              << ", solution template = (lambda ( ";
          for (const Node& targ : cons_strat->d_sol_templ_args)
          {
            Trace("sygus-unif") << targ << " ";
          }
          Trace("sygus-unif") << ") " << cons_strat->d_sol_templ << ")";
          Trace("sygus-unif") << std::endl;
        }
        // make the strategy
        snode.d_strats.push_back(cons_strat);
      }
    }
  }
}

bool SygusUnifStrategy::inferTemplate(
    unsigned k,
    Node n,
    std::map<Node, unsigned>& templ_var_index,
    std::map<unsigned, unsigned>& templ_injection)
{
  if (n.getNumChildren() == 0)
  {
    std::map<Node, unsigned>::iterator itt = templ_var_index.find(n);
    if (itt != templ_var_index.end())
    {
      unsigned kk = itt->second;
      std::map<unsigned, unsigned>::iterator itti = templ_injection.find(k);
      if (itti == templ_injection.end())
      {
        Trace("sygus-unif-debug") << "...set template injection " << k << " -> "
                                  << kk << std::endl;
        templ_injection[k] = kk;
      }
      else if (itti->second != kk)
      {
        // two distinct variables in this term, we fail
        return false;
      }
    }
    return true;
  }
  else
  {
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      if (!inferTemplate(k, n[i], templ_var_index, templ_injection))
      {
        return false;
      }
    }
  }
  return true;
}

void SygusUnifStrategy::staticLearnRedundantOps(
    std::map<Node, std::vector<Node>>& strategy_lemmas)
{
  StrategyRestrictions restrictions;
  staticLearnRedundantOps(strategy_lemmas, restrictions);
}

void SygusUnifStrategy::staticLearnRedundantOps(
    std::map<Node, std::vector<Node>>& strategy_lemmas,
    StrategyRestrictions& restrictions)
{
  for (unsigned i = 0; i < d_esym_list.size(); i++)
  {
    Node e = d_esym_list[i];
    std::map<Node, EnumInfo>::iterator itn = d_einfo.find(e);
    Assert(itn != d_einfo.end());
    // see if there is anything we can eliminate
    Trace("sygus-unif") << "* Search enumerator #" << i << " : type "
                        << e.getType().getDType().getName() << " : ";
    Trace("sygus-unif") << e << " has " << itn->second.d_enum_slave.size()
                        << " slaves:" << std::endl;
    for (unsigned j = 0; j < itn->second.d_enum_slave.size(); j++)
    {
      Node es = itn->second.d_enum_slave[j];
      std::map<Node, EnumInfo>::iterator itns = d_einfo.find(es);
      Assert(itns != d_einfo.end());
      Trace("sygus-unif") << "  " << es << ", role = " << itns->second.getRole()
                          << std::endl;
    }
  }
  Trace("sygus-unif") << std::endl;
  Trace("sygus-unif") << "Strategy for candidate " << d_candidate
                      << " is : " << std::endl;
  debugPrint("sygus-unif");
  std::map<Node, std::map<NodeRole, bool> > visited;
  std::map<Node, std::map<unsigned, bool> > needs_cons;
  staticLearnRedundantOps(
      getRootEnumerator(), role_equal, visited, needs_cons, restrictions);
  // now, check the needs_cons map
  for (std::pair<const Node, std::map<unsigned, bool> >& nce : needs_cons)
  {
    Node em = nce.first;
    const DType& dt = em.getType().getDType();
    std::vector<Node> lemmas;
    for (std::pair<const unsigned, bool>& nc : nce.second)
    {
      Assert(nc.first < dt.getNumConstructors());
      if (!nc.second)
      {
        Node tst = datatypes::utils::mkTester(em, nc.first, dt).negate();

        if (std::find(lemmas.begin(), lemmas.end(), tst) == lemmas.end())
        {
          Trace("sygus-unif") << "...can exclude based on  : " << tst
                              << std::endl;
          lemmas.push_back(tst);
        }
      }
    }
    if (!lemmas.empty())
    {
      strategy_lemmas[em] = lemmas;
    }
  }
}

void SygusUnifStrategy::debugPrint(const char* c)
{
  if (TraceIsOn(c))
  {
    std::map<Node, std::map<NodeRole, bool> > visited;
    debugPrint(c, getRootEnumerator(), role_equal, visited, 0);
  }
}

void SygusUnifStrategy::staticLearnRedundantOps(
    Node e,
    NodeRole nrole,
    std::map<Node, std::map<NodeRole, bool>>& visited,
    std::map<Node, std::map<unsigned, bool>>& needs_cons,
    StrategyRestrictions& restrictions)
{
  if (visited[e].find(nrole) != visited[e].end())
  {
    return;
  }
  Trace("sygus-strat-slearn") << "Learn redundant operators " << e << " "
                              << nrole << "..." << std::endl;
  visited[e][nrole] = true;
  EnumInfo& ei = getEnumInfo(e);
  if (ei.isTemplated())
  {
    return;
  }
  TypeNode etn = e.getType();
  EnumTypeInfo& tinfo = getEnumTypeInfo(etn);
  StrategyNode& snode = tinfo.getStrategyNode(nrole);
  // the constructors of the current strategy point we need
  std::map<unsigned, bool> needs_cons_curr;
  // get the unused strategies
  std::map<Node, std::unordered_set<unsigned>>::iterator itus =
      restrictions.d_unused_strategies.find(e);
  std::unordered_set<unsigned> unused_strats;
  if (itus != restrictions.d_unused_strategies.end())
  {
    unused_strats.insert(itus->second.begin(), itus->second.end());
  }
  for (unsigned j = 0, size = snode.d_strats.size(); j < size; j++)
  {
    // if we are not using this strategy, there is nothing to do
    if (unused_strats.find(j) != unused_strats.end())
    {
      continue;
    }
    EnumTypeInfoStrat* etis = snode.d_strats[j];
    unsigned cindex = datatypes::utils::indexOf(etis->d_cons);
    // constructors that correspond to strategies are not needed
    // the intuition is that the strategy itself is responsible for constructing
    // all terms that use the given constructor
    Trace("sygus-strat-slearn") << "...by strategy, can exclude operator "
                                << etis->d_cons << std::endl;
    needs_cons_curr[cindex] = false;
    // try to eliminate from etn's datatype all operators except TRUE/FALSE if
    // arguments of ITE are the same BOOL type
    if (restrictions.d_iteReturnBoolConst)
    {
      const DType& dt = etn.getDType();
      Node op = dt[cindex].getSygusOp();
      TypeNode sygus_tn = dt.getSygusType();
      if (op.getKind() == kind::BUILTIN
          && NodeManager::operatorToKind(op) == ITE && sygus_tn.isBoolean()
          && (dt[cindex].getArgType(1) == dt[cindex].getArgType(2)))
      {
        unsigned ncons = dt.getNumConstructors(), indexT = ncons,
                 indexF = ncons;
        for (unsigned k = 0; k < ncons; ++k)
        {
          Node op_arg = dt[k].getSygusOp();
          if (dt[k].getNumArgs() > 0 || !op_arg.isConst())
          {
            continue;
          }
          if (op_arg.getConst<bool>())
          {
            indexT = k;
          }
          else
          {
            indexF = k;
          }
        }
        if (indexT < ncons && indexF < ncons)
        {
          Trace("sygus-strat-slearn")
              << "...for ite boolean arg, can exclude all operators but T/F\n";
          for (unsigned k = 0; k < ncons; ++k)
          {
            needs_cons_curr[k] = false;
          }
          needs_cons_curr[indexT] = true;
          needs_cons_curr[indexF] = true;
        }
      }
    }
    for (std::pair<Node, NodeRole>& cec : etis->d_cenum)
    {
      staticLearnRedundantOps(
          cec.first, cec.second, visited, needs_cons, restrictions);
    }
  }
  // get the current datatype
  const DType& dt = etn.getDType();
  // do not use recursive Boolean connectives for conditions of ITEs
  if (nrole == role_ite_condition && restrictions.d_iteCondOnlyAtoms)
  {
    TypeNode sygus_tn = dt.getSygusType();
    for (unsigned j = 0, size = dt.getNumConstructors(); j < size; j++)
    {
      Node op = dt[j].getSygusOp();
      Trace("sygus-strat-slearn")
          << "...for ite condition, look at operator : " << op << std::endl;
      if (op.isConst() && dt[j].getNumArgs() == 0)
      {
        Trace("sygus-strat-slearn")
            << "...for ite condition, can exclude Boolean constant " << op
            << std::endl;
        needs_cons_curr[j] = false;
        continue;
      }
      if (op.getKind() == kind::BUILTIN)
      {
        Kind kind = NodeManager::operatorToKind(op);
        if (kind == NOT || kind == OR || kind == AND || kind == ITE)
        {
          // can eliminate if their argument types are simple loops to this type
          bool type_ok = true;
          for (unsigned k = 0, nargs = dt[j].getNumArgs(); k < nargs; k++)
          {
            TypeNode tn = dt[j].getArgType(k);
            if (tn != etn)
            {
              type_ok = false;
              break;
            }
          }
          if (type_ok)
          {
            Trace("sygus-strat-slearn")
                << "...for ite condition, can exclude Boolean connective : "
                << op << std::endl;
            needs_cons_curr[j] = false;
          }
        }
      }
    }
  }
  // all other constructors are needed
  for (unsigned j = 0, size = dt.getNumConstructors(); j < size; j++)
  {
    if (needs_cons_curr.find(j) == needs_cons_curr.end())
    {
      needs_cons_curr[j] = true;
    }
  }
  // update the constructors that the master enumerator needs
  if (needs_cons.find(e) == needs_cons.end())
  {
    needs_cons[e] = needs_cons_curr;
  }
  else
  {
    for (unsigned j = 0, size = dt.getNumConstructors(); j < size; j++)
    {
      needs_cons[e][j] = needs_cons[e][j] || needs_cons_curr[j];
    }
  }
}

void SygusUnifStrategy::finishInit(
    Node e,
    NodeRole nrole,
    std::map<Node, std::map<NodeRole, bool> >& visited,
    bool isCond)
{
  EnumInfo& ei = getEnumInfo(e);
  if (visited[e].find(nrole) != visited[e].end()
      && (!isCond || ei.isConditional()))
  {
    return;
  }
  visited[e][nrole] = true;
  // set conditional
  if (isCond)
  {
    ei.setConditional();
  }
  if (ei.isTemplated())
  {
    return;
  }
  TypeNode etn = e.getType();
  EnumTypeInfo& tinfo = getEnumTypeInfo(etn);
  StrategyNode& snode = tinfo.getStrategyNode(nrole);
  for (unsigned j = 0, size = snode.d_strats.size(); j < size; j++)
  {
    EnumTypeInfoStrat* etis = snode.d_strats[j];
    StrategyType strat = etis->d_this;
    bool newIsCond = isCond || strat == strat_ITE;
    for (std::pair<Node, NodeRole>& cec : etis->d_cenum)
    {
      finishInit(cec.first, cec.second, visited, newIsCond);
    }
  }
}

void SygusUnifStrategy::debugPrint(
    const char* c,
    Node e,
    NodeRole nrole,
    std::map<Node, std::map<NodeRole, bool> >& visited,
    int ind)
{
  if (visited[e].find(nrole) != visited[e].end())
  {
    indent(c, ind);
    Trace(c) << e << " :: node role : " << nrole << std::endl;
    return;
  }
  visited[e][nrole] = true;
  EnumInfo& ei = getEnumInfo(e);

  TypeNode etn = e.getType();

  indent(c, ind);
  Trace(c) << e << " :: node role : " << nrole;
  Trace(c) << ", type : " << etn.getDType().getName();
  if (ei.isConditional())
  {
    Trace(c) << ", conditional";
  }
  Trace(c) << ", enum role : " << ei.getRole();

  if (ei.isTemplated())
  {
    Trace(c) << ", templated : (lambda " << ei.d_template_arg << " "
             << ei.d_template << ")" << std::endl;
    return;
  }
  Trace(c) << std::endl;

  EnumTypeInfo& tinfo = getEnumTypeInfo(etn);
  StrategyNode& snode = tinfo.getStrategyNode(nrole);
  for (unsigned j = 0, size = snode.d_strats.size(); j < size; j++)
  {
    EnumTypeInfoStrat* etis = snode.d_strats[j];
    StrategyType strat = etis->d_this;
    indent(c, ind + 1);
    Trace(c) << "Strategy : " << strat << ", from cons : " << etis->d_cons
             << std::endl;
    for (std::pair<Node, NodeRole>& cec : etis->d_cenum)
    {
      // recurse
      debugPrint(c, cec.first, cec.second, visited, ind + 2);
    }
  }
}

void EnumInfo::initialize(EnumRole role) { d_role = role; }

StrategyNode& EnumTypeInfo::getStrategyNode(NodeRole nrole)
{
  std::map<NodeRole, StrategyNode>::iterator it = d_snodes.find(nrole);
  Assert(it != d_snodes.end());
  return it->second;
}

bool EnumTypeInfoStrat::isValid(UnifContext& x)
{
  if ((x.getCurrentRole() == role_string_prefix
       && d_this == strat_CONCAT_SUFFIX)
      || (x.getCurrentRole() == role_string_suffix
          && d_this == strat_CONCAT_PREFIX))
  {
    return false;
  }
  return true;
}

StrategyNode::~StrategyNode()
{
  for (unsigned j = 0, size = d_strats.size(); j < size; j++)
  {
    delete d_strats[j];
  }
  d_strats.clear();
}

void SygusUnifStrategy::indent(const char* c, int ind)
{
  if (TraceIsOn(c))
  {
    for (int i = 0; i < ind; i++)
    {
      Trace(c) << "  ";
    }
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
