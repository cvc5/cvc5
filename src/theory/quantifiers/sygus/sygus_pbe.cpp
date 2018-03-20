/*********************                                                        */
/*! \file ce_guided_pbe.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing programming by examples synthesis conjectures
 **
 **/
#include "theory/quantifiers/sygus/sygus_pbe.h"

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "util/random.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void indent( const char * c, int ind ) {
  if( Trace.isOn(c) ){
    for( int i=0; i<ind; i++ ){ 
      Trace(c) << "  "; 
    }
  } 
}

void print_val( const char * c, std::vector< Node >& vals, bool pol = true ){
  if( Trace.isOn(c) ){
    for( unsigned i=0; i<vals.size(); i++ ){
      //Trace(c) << ( pol ? vals[i] : !vals[i] );
      Trace(c) << ( ( pol ? vals[i].getConst<bool>() : !vals[i].getConst<bool>() ) ? "1" : "0" );
    }
  }
}

std::ostream& operator<<(std::ostream& os, EnumRole r)
{
  switch(r){
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

CegConjecturePbe::CegConjecturePbe(QuantifiersEngine* qe, CegConjecture* p)
    : SygusModule(qe, p)
{
  d_tds = d_qe->getTermDatabaseSygus();
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_is_pbe = false;
}

CegConjecturePbe::~CegConjecturePbe() {

}

//--------------------------------- collecting finite input/output domain information

void CegConjecturePbe::collectExamples( Node n, std::map< Node, bool >& visited, bool hasPol, bool pol ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    Node neval;
    Node n_output;
    if( n.getKind()==APPLY_UF && n.getNumChildren()>0 ){
      neval = n;
      if( hasPol ){
        n_output = !pol ? d_true : d_false;
      }
    }else if( n.getKind()==EQUAL && hasPol && !pol ){
      for( unsigned r=0; r<2; r++ ){
        if( n[r].getKind()==APPLY_UF && n[r].getNumChildren()>0 ){
          neval = n[r];
          if( n[1-r].isConst() ){
            n_output = n[1-r];
          }
        }
      }
    }
    if( !neval.isNull() ){
      if( neval.getKind()==APPLY_UF && neval.getNumChildren()>0 ){
        // is it an evaluation function?
        if( d_examples.find( neval[0] )!=d_examples.end() ){
          std::map< Node, bool >::iterator itx = d_examples_invalid.find( neval[0] );
          if( itx==d_examples_invalid.end() ){
            //collect example
            bool success = true;
            std::vector< Node > ex;
            for( unsigned j=1; j<neval.getNumChildren(); j++ ){
              if( !neval[j].isConst() ){
                success = false;
                break;
              }else{
                ex.push_back( neval[j] );
              }
            }
            if( success ){
              d_examples[neval[0]].push_back( ex );
              d_examples_out[neval[0]].push_back( n_output );
              d_examples_term[neval[0]].push_back( neval );
              if( n_output.isNull() ){
                d_examples_out_invalid[neval[0]] = true;
              }else{
                Assert( n_output.isConst() );
              }
              //finished processing this node
              return;
            }else{
              d_examples_invalid[neval[0]] = true;
              d_examples_out_invalid[neval[0]] = true;
            }
          }
        }
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getPolarity( n, i, hasPol, pol, newHasPol, newPol );
      collectExamples( n[i], visited, newHasPol, newPol );
    }
  }
}

bool CegConjecturePbe::initialize(Node n,
                                  const std::vector<Node>& candidates,
                                  std::vector<Node>& lemmas)
{
  Trace("sygus-pbe") << "Initialize PBE : " << n << std::endl;
  
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node v = candidates[i];
    d_examples[v].clear();
    d_examples_out[v].clear();
    d_examples_term[v].clear();
  }
  
  std::map< Node, bool > visited;
  collectExamples( n, visited, true, true );
  
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node v = candidates[i];
    Trace("sygus-pbe") << "  examples for " << v << " : ";
    if( d_examples_invalid.find( v )!=d_examples_invalid.end() ){
      Trace("sygus-pbe") << "INVALID" << std::endl;
    }else{
      Trace("sygus-pbe") << std::endl;
      for( unsigned j=0; j<d_examples[v].size(); j++ ){
        Trace("sygus-pbe") << "    ";
        for( unsigned k=0; k<d_examples[v][j].size(); k++ ){
          Trace("sygus-pbe") << d_examples[v][j][k] << " ";
        }
        if( !d_examples_out[v][j].isNull() ){
          Trace("sygus-pbe") << " -> " << d_examples_out[v][j];
        }
        Trace("sygus-pbe") << std::endl;
      }
    }
  }
  
  //register candidates
  if( options::sygusUnifCondSol() ){
    if( candidates.size()==1 ){// conditional solutions for multiple function conjectures TODO?
      // collect a pool of types over which we will enumerate terms 
      Node c = candidates[0];
      //the candidate must be input/output examples
      if( d_examples_out_invalid.find( c )==d_examples_out_invalid.end() ){
        Assert( d_examples.find( c )!=d_examples.end() );
        Trace("sygus-unif") << "It is input/output examples..." << std::endl;
        TypeNode ctn = c.getType();
        d_cinfo[c].initialize( c );
        // collect the enumerator types / form the strategy
        collectEnumeratorTypes(c, ctn, role_equal);
        // if we have non-trivial strategies, then use pbe
        if( d_cinfo[c].isNonTrivial() ){
          // static learning of redundant constructors
          staticLearnRedundantOps( c, lemmas );
          d_is_pbe = true;
        }
      }
    }
  }
  return d_is_pbe;
}

Node CegConjecturePbe::PbeTrie::addPbeExample(TypeNode etn, Node e, Node b,
                                              CegConjecturePbe* cpbe,
                                              unsigned index, unsigned ntotal) {
  if (index == ntotal) {
    // lazy child holds the leaf data
    if (d_lazy_child.isNull()) {
      d_lazy_child = b;
    }
    return d_lazy_child;
  } else {
    std::vector<Node> ex;
    if (d_children.empty()) {
      if (d_lazy_child.isNull()) {
        d_lazy_child = b;
        return d_lazy_child;
      } else {
        // evaluate the lazy child
        Assert(cpbe->d_examples.find(e) != cpbe->d_examples.end());
        Assert(index < cpbe->d_examples[e].size());
        ex = cpbe->d_examples[e][index];
        addPbeExampleEval(etn, e, d_lazy_child, ex, cpbe, index, ntotal);
        Assert(!d_children.empty());
        d_lazy_child = Node::null();
      }
    } else {
      Assert(cpbe->d_examples.find(e) != cpbe->d_examples.end());
      Assert(index < cpbe->d_examples[e].size());
      ex = cpbe->d_examples[e][index];
    }
    return addPbeExampleEval(etn, e, b, ex, cpbe, index, ntotal);
  }
}

Node CegConjecturePbe::PbeTrie::addPbeExampleEval(TypeNode etn, Node e, Node b,
                                                  std::vector<Node>& ex,
                                                  CegConjecturePbe* cpbe,
                                                  unsigned index,
                                                  unsigned ntotal) {
  Node eb = cpbe->d_tds->evaluateBuiltin(etn, b, ex);
  return d_children[eb].addPbeExample(etn, e, b, cpbe, index + 1, ntotal);
}

bool CegConjecturePbe::hasExamples(Node e) {
  if (isPbe()) {
    e = d_tds->getSynthFunForEnumerator(e);
    Assert(!e.isNull());
    std::map<Node, bool>::iterator itx = d_examples_invalid.find(e);
    if (itx == d_examples_invalid.end()) {
      return d_examples.find(e) != d_examples.end();
    }
  }
  return false;
}

unsigned CegConjecturePbe::getNumExamples(Node e) {
  e = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, std::vector<std::vector<Node> > >::iterator it =
      d_examples.find(e);
  if (it != d_examples.end()) {
    return it->second.size();
  } else {
    return 0;
  }
}

void CegConjecturePbe::getExample(Node e, unsigned i, std::vector<Node>& ex) {
  e = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, std::vector<std::vector<Node> > >::iterator it =
      d_examples.find(e);
  if (it != d_examples.end()) {
    Assert(i < it->second.size());
    ex.insert(ex.end(), it->second[i].begin(), it->second[i].end());
  } else {
    Assert(false);
  }
}

Node CegConjecturePbe::getExampleOut(Node e, unsigned i) {
  e = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, std::vector<Node> >::iterator it = d_examples_out.find(e);
  if (it != d_examples_out.end()) {
    Assert(i < it->second.size());
    return it->second[i];
  } else {
    Assert(false);
    return Node::null();
  }
}

Node CegConjecturePbe::addSearchVal(TypeNode tn, Node e, Node bvr) {
  Assert(isPbe());
  Assert(!e.isNull());
  e = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, bool>::iterator itx = d_examples_invalid.find(e);
  if (itx == d_examples_invalid.end()) {
    unsigned nex = d_examples[e].size();
    Node ret = d_pbe_trie[e][tn].addPbeExample(tn, e, bvr, this, 0, nex);
    Assert(ret.getType() == bvr.getType());
    return ret;
  }
  return Node::null();
}

Node CegConjecturePbe::evaluateBuiltin(TypeNode tn, Node bn, Node e,
                                       unsigned i) {
  e = d_tds->getSynthFunForEnumerator(e);
  Assert(!e.isNull());
  std::map<Node, bool>::iterator itx = d_examples_invalid.find(e);
  if (itx == d_examples_invalid.end()) {
    std::map<Node, std::vector<std::vector<Node> > >::iterator it =
        d_examples.find(e);
    if (it != d_examples.end()) {
      Assert(i < it->second.size());
      return d_tds->evaluateBuiltin(tn, bn, it->second[i]);
    }
  }
  return Rewriter::rewrite(bn);
}

// ----------------------------- establishing enumeration types

void CegConjecturePbe::registerEnumerator(
    Node et, Node c, TypeNode tn, EnumRole enum_role, bool inSearch)
{
  if (d_einfo.find(et) == d_einfo.end())
  {
    Trace("sygus-unif-debug")
        << "...register " << et << " for "
        << ((DatatypeType)tn.toType()).getDatatype().getName();
    Trace("sygus-unif-debug") << ", role = " << enum_role
                              << ", in search = " << inSearch << std::endl;
    d_einfo[et].initialize(c, enum_role);
    // if we are actually enumerating this (could be a compound node in the
    // strategy)
    if (inSearch)
    {
      std::map<TypeNode, Node>::iterator itn =
          d_cinfo[c].d_search_enum.find(tn);
      if (itn == d_cinfo[c].d_search_enum.end())
      {
        // use this for the search
        d_cinfo[c].d_search_enum[tn] = et;
        d_cinfo[c].d_esym_list.push_back(et);
        d_einfo[et].d_enum_slave.push_back(et);
        // register measured term with database
        d_qe->getTermDatabaseSygus()->registerEnumerator(et, c, d_parent, true);
        d_einfo[et].d_active_guard =
            d_qe->getTermDatabaseSygus()->getActiveGuardForEnumerator(et);
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

void CegConjecturePbe::collectEnumeratorTypes(Node e,
                                              TypeNode tn,
                                              NodeRole nrole)
{
  NodeManager* nm = NodeManager::currentNM();
  if (d_cinfo[e].d_tinfo.find(tn) == d_cinfo[e].d_tinfo.end())
  {
    // register type
    Trace("sygus-unif") << "Register enumerating type : " << tn << std::endl;
    d_cinfo[e].initializeType( tn );
  }
  EnumTypeInfo& eti = d_cinfo[e].d_tinfo[tn];
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
    ee = nm->mkSkolem("ee", tn);
    eti.d_enum[erole] = ee;
    Trace("sygus-unif-debug")
        << "...enumerator " << ee << " for "
        << ((DatatypeType)tn.toType()).getDatatype().getName()
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
    registerEnumerator(ee, e, tn, erole, true);
    return;
  }

  // look at information on how we will construct solutions for this type
  Assert(tn.isDatatype());
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
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
    Node cop = Node::fromExpr(dt[j].getConstructor());
    Node op = Node::fromExpr(dt[j].getSygusOp());
    Trace("sygus-unif-debug") << "--- Infer strategy from " << cop
                              << " with sygus op " << op << "..." << std::endl;

    // expand the evaluation to see if this constuctor induces a strategy
    std::vector<Node> utchildren;
    utchildren.push_back(cop);
    std::vector<Node> sks;
    std::vector<TypeNode> sktns;
    for (unsigned k = 0, nargs = dt[j].getNumArgs(); k < nargs; k++)
    {
      Type t = dt[j][k].getRangeType();
      TypeNode ttn = TypeNode::fromType(t);
      Node kv = nm->mkSkolem("ut", ttn);
      sks.push_back(kv);
      cop_to_sks[cop].push_back(kv);
      sktns.push_back(ttn);
      utchildren.push_back(kv);
    }
    Node ut = nm->mkNode(APPLY_CONSTRUCTOR, utchildren);
    std::vector<Node> echildren;
    echildren.push_back(Node::fromExpr(dt.getSygusEvaluationFunc()));
    echildren.push_back(ut);
    Node sbvl = Node::fromExpr(dt.getSygusVarList());
    for (const Node& sbv : sbvl)
    {
      echildren.push_back(sbv);
    }
    Node eut = nm->mkNode(APPLY_UF, echildren);
    Trace("sygus-unif-debug2") << "  Test evaluation of " << eut << "..."
                               << std::endl;
    eut = d_qe->getTermDatabaseSygus()->unfold(eut);
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
        const Datatype& cdt =
            static_cast<DatatypeType>(sks[k].getType().toType()).getDatatype();
        echildren[0] = Node::fromExpr(cdt.getSygusEvaluationFunc());
        echildren[1] = sks[k];
        Trace("sygus-unif-debug2") << "...set eval dt to " << sks[k]
                                   << std::endl;
        Node esk = nm->mkNode(APPLY_UF, echildren);
        vs.push_back(esk);
        Node tvar = nm->mkSkolem("templ", esk.getType());
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
              }else{
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
                teut = Rewriter::rewrite(teut);
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
    if (cop_to_strat.find(cop) == cop_to_strat.end())
    {
      Trace("sygus-unif") << "...constructor " << cop
                          << " does not correspond to a strategy." << std::endl;
      search_this = true;
    }
    else
    {
      Trace("sygus-unif") << "-> constructor " << cop
                          << " matches strategy for " << eut.getKind() << "..."
                          << std::endl;
      // collect children types
      for (unsigned k = 0, size = cop_to_carg_list[cop].size(); k < size; k++)
      {
        TypeNode tn = sktns[cop_to_carg_list[cop][k]];
        Trace("sygus-unif-debug")
            << "   Child type " << k << " : "
            << static_cast<DatatypeType>(tn.toType()).getDatatype().getName()
            << std::endl;
        cop_to_child_types[cop].push_back(tn);
      }
    }
  }

  // check whether we should also enumerate the current type
  Trace("sygus-unif-debug2") << "  register this enumerator..." << std::endl;
  registerEnumerator(ee, e, tn, erole, search_this);

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
          if (cop_to_child_templ[cop].find(j) != cop_to_child_templ[cop].end())
          {
            // it is templated, allocate a fresh variable
            et = nm->mkSkolem("et", ct);
            Trace("sygus-unif-debug")
                << "...enumerate " << et << " of type "
                << ((DatatypeType)ct.toType()).getDatatype().getName();
            Trace("sygus-unif-debug")
                << " for arg " << j << " of "
                << ((DatatypeType)tn.toType()).getDatatype().getName()
                << std::endl;
            registerEnumerator(et, e, ct, erole_c, true);
            d_einfo[et].d_template = cop_to_child_templ[cop][j];
            d_einfo[et].d_template_arg = cop_to_child_templ_arg[cop][j];
            Assert(!d_einfo[et].d_template.isNull());
            Assert(!d_einfo[et].d_template_arg.isNull());
          }
          else
          {
            Trace("sygus-unif-debug")
                << "...child type enumerate "
                << ((DatatypeType)ct.toType()).getDatatype().getName()
                << ", node role = " << nrole_c << std::endl;
            collectEnumeratorTypes(e, ct, nrole_c);
            // otherwise use the previous
            Assert(d_cinfo[e].d_tinfo[ct].d_enum.find(erole_c)
                   != d_cinfo[e].d_tinfo[ct].d_enum.end());
            et = d_cinfo[e].d_tinfo[ct].d_enum[erole_c];
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
            sol_templ_children[j] = cop_to_sks[cop][j].getType().mkGroundTerm();
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
        if (Trace.isOn("sygus-unif"))
        {
          Trace("sygus-unif") << "Initialized strategy " << strat;
          Trace("sygus-unif") << " for " << ((DatatypeType)tn.toType()).getDatatype().getName() << ", operator " << cop;
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

bool CegConjecturePbe::inferTemplate( unsigned k, Node n, std::map< Node, unsigned >& templ_var_index, std::map< unsigned, unsigned >& templ_injection ){
  if( n.getNumChildren()==0 ){
    std::map< Node, unsigned >::iterator itt = templ_var_index.find( n );
    if( itt!=templ_var_index.end() ){
      unsigned kk = itt->second;
      std::map< unsigned, unsigned >::iterator itti = templ_injection.find( k );
      if( itti==templ_injection.end() ){
        Trace("sygus-unif-debug") << "...set template injection " << k <<  " -> " << kk << std::endl;
        templ_injection[k] = kk;
      }else if( itti->second!=kk ){
        // two distinct variables in this term, we fail
        return false;
      }
    }
    return true;
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !inferTemplate( k, n[i], templ_var_index, templ_injection ) ){
        return false;
      }
    }
  }
  return true;
}

void CegConjecturePbe::staticLearnRedundantOps( Node c, std::vector< Node >& lemmas ) {
  for( unsigned i=0; i<d_cinfo[c].d_esym_list.size(); i++ ){
    Node e = d_cinfo[c].d_esym_list[i];
    std::map< Node, EnumInfo >::iterator itn = d_einfo.find( e );
    Assert( itn!=d_einfo.end() );
    // see if there is anything we can eliminate
    Trace("sygus-unif") << "* Search enumerator #" << i << " : type " << ((DatatypeType)e.getType().toType()).getDatatype().getName() << " : ";
    Trace("sygus-unif") << e << " has " << itn->second.d_enum_slave.size() << " slaves:" << std::endl;
    for( unsigned j=0; j<itn->second.d_enum_slave.size(); j++ ){
      Node es = itn->second.d_enum_slave[j];
      std::map< Node, EnumInfo >::iterator itns = d_einfo.find( es );
      Assert( itns!=d_einfo.end() );
      Trace("sygus-unif") << "  " << es << ", role = " << itns->second.getRole()
                          << std::endl;
    }
  }
  Trace("sygus-unif") << std::endl;
  Trace("sygus-unif") << "Strategy for candidate " << c << " is : " << std::endl;
  std::map<Node, std::map<NodeRole, bool> > visited;
  std::map<Node, std::map<unsigned, bool> > needs_cons;
  staticLearnRedundantOps(c,
                          d_cinfo[c].getRootEnumerator(),
                          role_equal,
                          visited,
                          needs_cons,
                          0,
                          false);
  // now, check the needs_cons map
  for (std::pair<const Node, std::map<unsigned, bool> >& nce : needs_cons)
  {
    Node em = nce.first;
    const Datatype& dt =
        static_cast<DatatypeType>(em.getType().toType()).getDatatype();
    for (std::pair<const unsigned, bool>& nc : nce.second)
    {
      Assert(nc.first < dt.getNumConstructors());
      if (!nc.second)
      {
        Node tst =
            datatypes::DatatypesRewriter::mkTester(em, nc.first, dt).negate();
        if (std::find(lemmas.begin(), lemmas.end(), tst) == lemmas.end())
        {
          Trace("sygus-unif") << "...can exclude based on  : " << tst
                              << std::endl;
          lemmas.push_back(tst);
        }
      }
    }
  }
}

void CegConjecturePbe::staticLearnRedundantOps(
    Node c,
    Node e,
    NodeRole nrole,
    std::map<Node, std::map<NodeRole, bool> >& visited,
    std::map<Node, std::map<unsigned, bool> >& needs_cons,
    int ind,
    bool isCond)
{
  std::map< Node, EnumInfo >::iterator itn = d_einfo.find( e );
  Assert( itn!=d_einfo.end() );

  if (visited[e].find(nrole) == visited[e].end()
      || (isCond && !itn->second.isConditional()))
  {
    visited[e][nrole] = true;
    // if conditional
    if (isCond)
    {
      itn->second.setConditional();
    }
    indent("sygus-unif", ind);
    Trace("sygus-unif") << e << " :: node role : " << nrole;
    Trace("sygus-unif")
        << ", type : "
        << ((DatatypeType)e.getType().toType()).getDatatype().getName();
    if (isCond)
    {
      Trace("sygus-unif") << ", conditional";
    }
    Trace("sygus-unif") << ", enum role : " << itn->second.getRole();

    if( itn->second.isTemplated() ){
      Trace("sygus-unif") << ", templated : (lambda "
                          << itn->second.d_template_arg << " "
                          << itn->second.d_template << ")" << std::endl;
    }else{
      Trace("sygus-unif") << std::endl;
      TypeNode etn = e.getType();

      // enumerator type info
      std::map< TypeNode, EnumTypeInfo >::iterator itt = d_cinfo[c].d_tinfo.find( etn );
      Assert( itt!=d_cinfo[c].d_tinfo.end() );
      EnumTypeInfo& tinfo = itt->second;

      // strategy info
      std::map<NodeRole, StrategyNode>::iterator itsn =
          tinfo.d_snodes.find(nrole);
      Assert(itsn != tinfo.d_snodes.end());
      StrategyNode& snode = itsn->second;

      if (snode.d_strats.empty())
      {
        return;
      }
      std::map<unsigned, bool> needs_cons_curr;
      // various strategies
      for (unsigned j = 0, size = snode.d_strats.size(); j < size; j++)
      {
        EnumTypeInfoStrat* etis = snode.d_strats[j];
        StrategyType strat = etis->d_this;
        bool newIsCond = isCond || strat == strat_ITE;
        indent("sygus-unif", ind + 1);
        Trace("sygus-unif") << "Strategy : " << strat
                            << ", from cons : " << etis->d_cons << std::endl;
        int cindex = Datatype::indexOf(etis->d_cons.toExpr());
        Assert(cindex != -1);
        needs_cons_curr[static_cast<unsigned>(cindex)] = false;
        for (std::pair<Node, NodeRole>& cec : etis->d_cenum)
        {
          // recurse
          staticLearnRedundantOps(c,
                                  cec.first,
                                  cec.second,
                                  visited,
                                  needs_cons,
                                  ind + 2,
                                  newIsCond);
        }
      }
      // get the master enumerator for the type of this enumerator
      std::map<TypeNode, Node>::iterator itse =
          d_cinfo[c].d_search_enum.find(etn);
      if (itse == d_cinfo[c].d_search_enum.end())
      {
        return;
      }
      Node em = itse->second;
      Assert(!em.isNull());
      // get the current datatype
      const Datatype& dt =
          static_cast<DatatypeType>(etn.toType()).getDatatype();
      // all constructors that are not a part of a strategy are needed
      for (unsigned j = 0, size = dt.getNumConstructors(); j < size; j++)
      {
        if (needs_cons_curr.find(j) == needs_cons_curr.end())
        {
          needs_cons_curr[j] = true;
        }
      }
      // update the constructors that the master enumerator needs
      if (needs_cons.find(em) == needs_cons.end())
      {
        needs_cons[em] = needs_cons_curr;
      }
      else
      {
        for (unsigned j = 0, size = dt.getNumConstructors(); j < size; j++)
        {
          needs_cons[em][j] = needs_cons[em][j] || needs_cons_curr[j];
        }
      }
    }
  }else{
    indent("sygus-unif", ind);
    Trace("sygus-unif") << e << " :: node role : " << nrole << std::endl;
  }
}

// ------------------------------------------- solution construction from enumeration

void CegConjecturePbe::getTermList(const std::vector<Node>& candidates,
                                   std::vector<Node>& terms)
{
  Valuation& valuation = d_qe->getValuation();
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node v = candidates[i];
    std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( v );
    if( it!=d_cinfo.end() ){
      for( unsigned j=0; j<it->second.d_esym_list.size(); j++ ){
        Node e = it->second.d_esym_list[j];
        std::map< Node, EnumInfo >::iterator it = d_einfo.find( e );
        Assert( it != d_einfo.end() );
        Node gstatus = valuation.getSatValue(it->second.d_active_guard);
        if (!gstatus.isNull() && gstatus.getConst<bool>())
        {
          terms.push_back(e);
        }
      }
    }
  }
}

bool CegConjecturePbe::constructCandidates(const std::vector<Node>& enums,
                                           const std::vector<Node>& enum_values,
                                           const std::vector<Node>& candidates,
                                           std::vector<Node>& candidate_values,
                                           std::vector<Node>& lems)
{
  Assert( enums.size()==enum_values.size() );
  if( !enums.empty() ){
    unsigned min_term_size = 0;
    std::vector< unsigned > enum_consider;
    Trace("sygus-pbe-enum") << "Register new enumerated values : " << std::endl;
    for( unsigned i=0; i<enums.size(); i++ ){
      Trace("sygus-pbe-enum") << "  " << enums[i] << " -> " << enum_values[i] << std::endl;
      unsigned sz = d_tds->getSygusTermSize( enum_values[i] );
      if( i==0 || sz<min_term_size ){
        enum_consider.clear();
        min_term_size = sz;
        enum_consider.push_back( i );
      }else if( sz==min_term_size ){
        enum_consider.push_back( i );
      }
    }
    // only consider the enumerators that are at minimum size (for fairness)
    Trace("sygus-pbe-enum") << "...register " << enum_consider.size() << " / " << enums.size() << std::endl;
    for( unsigned i=0; i<enum_consider.size(); i++ ){
      unsigned j = enum_consider[i];
      addEnumeratedValue( enums[j], enum_values[j], lems );
    }
  }
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node c = candidates[i];
    //build decision tree for candidate
    Node vc = constructSolution( c );
    if( vc.isNull() ){     
      return false;
    }else{
      candidate_values.push_back( vc );
    }
  }
  return true;
}

void CegConjecturePbe::addEnumeratedValue( Node x, Node v, std::vector< Node >& lems ) {
  std::map< Node, EnumInfo >::iterator it = d_einfo.find( x );
  Assert( it != d_einfo.end() );
  Node gstatus = d_qe->getValuation().getSatValue(it->second.d_active_guard);
  if (gstatus.isNull() || !gstatus.getConst<bool>())
  {
    Trace("sygus-pbe-enum-debug") << "  ...guard is inactive." << std::endl;
    return;
  }
  Assert(
      std::find(it->second.d_enum_vals.begin(), it->second.d_enum_vals.end(), v)
      == it->second.d_enum_vals.end());
  Node c = it->second.d_parent_candidate;
  // The explanation for why the current value should be excluded in future
  // iterations.
  Node exp_exc;
  if (d_examples_out_invalid.find(c) == d_examples_out_invalid.end())
  {
    std::map<Node, CandidateInfo>::iterator itc = d_cinfo.find(c);
    Assert(itc != d_cinfo.end());
    TypeNode xtn = x.getType();
    Node bv = d_tds->sygusToBuiltin(v, xtn);
    std::map<Node, std::vector<std::vector<Node> > >::iterator itx =
        d_examples.find(c);
    std::map<Node, std::vector<Node> >::iterator itxo = d_examples_out.find(c);
    Assert(itx != d_examples.end());
    Assert(itxo != d_examples_out.end());
    Assert(itx->second.size() == itxo->second.size());
    std::vector<Node> base_results;
    // compte the results
    for (unsigned j = 0, size = itx->second.size(); j < size; j++)
    {
      Node res = d_tds->evaluateBuiltin(xtn, bv, itx->second[j]);
      Trace("sygus-pbe-enum-debug")
          << "...got res = " << res << " from " << bv << std::endl;
      base_results.push_back(res);
    }
    // is it excluded for domain-specific reason?
    std::vector<Node> exp_exc_vec;
    if (getExplanationForEnumeratorExclude(
            c, x, v, base_results, it->second, exp_exc_vec))
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
      Assert( !it->second.d_enum_slave.empty() );
      //explanation for why this value should be excluded
      for( unsigned s=0; s<it->second.d_enum_slave.size(); s++ ){
        Node xs = it->second.d_enum_slave[s];
        std::map< Node, EnumInfo >::iterator itv = d_einfo.find( xs );
        Assert( itv!=d_einfo.end() );
        Trace("sygus-pbe-enum") << "Process " << xs << " from " << s << std::endl;
        //bool prevIsCover = false;
        if (itv->second.getRole() == enum_io)
        {
          Trace("sygus-pbe-enum") << "   IO-Eval of ";
          //prevIsCover = itv->second.isFeasible();
        }else{
          Trace("sygus-pbe-enum") << "Evaluation of ";
        }
        Trace("sygus-pbe-enum")  << xs <<  " : ";
        //evaluate all input/output examples
        std::vector< Node > results;
        Node templ = itv->second.d_template;
        TNode templ_var = itv->second.d_template_arg;
        std::map< Node, bool > cond_vals;
        for (unsigned j = 0, size = base_results.size(); j < size; j++)
        {
          Node res = base_results[j];
          Assert( res.isConst() );
          if( !templ.isNull() ){
            TNode tres = res;
            res = templ.substitute( templ_var, res );
            res = Rewriter::rewrite( res );
            Assert( res.isConst() );
          }
          Node resb;
          if (itv->second.getRole() == enum_io)
          {
            Node out = itxo->second[j];
            Assert( out.isConst() );
            resb = res==out ? d_true : d_false;
          }else{
            resb = res;
          }
          cond_vals[resb] = true;
          results.push_back( resb );
          if( Trace.isOn("sygus-pbe-enum") ){
            if( resb.getType().isBoolean() ){
              Trace("sygus-pbe-enum") << ( resb==d_true ? "1" : "0" );
            }else{
              Trace("sygus-pbe-enum") << "?";
            }
          }
        }
        bool keep = false;
        if (itv->second.getRole() == enum_io)
        {
          // latter is the degenerate case of no examples
          if (cond_vals.find(d_true) != cond_vals.end() || cond_vals.empty())
          {
            //check subsumbed/subsuming
            std::vector< Node > subsume;
            if( cond_vals.find( d_false )==cond_vals.end() ){
              // it is the entire solution, we are done
              Trace("sygus-pbe-enum") << "  ...success, full solution added to PBE pool : " << d_tds->sygusToBuiltin( v ) << std::endl;
              if( !itv->second.isSolved() ){
                itv->second.setSolved( v );
                // it subsumes everything
                itv->second.d_term_trie.clear();
                itv->second.d_term_trie.addTerm( this, v, results, true, subsume );
              }
              keep = true;
            }else{
              Node val = itv->second.d_term_trie.addTerm( this, v, results, true, subsume );
              if( val==v ){
                Trace("sygus-pbe-enum") << "  ...success"; 
                if( !subsume.empty() ){
                  itv->second.d_enum_subsume.insert( itv->second.d_enum_subsume.end(), subsume.begin(), subsume.end() );
                  Trace("sygus-pbe-enum") << " and subsumed " << subsume.size() << " terms";
                }
                Trace("sygus-pbe-enum") << "!   add to PBE pool : " << d_tds->sygusToBuiltin( v ) << std::endl;
                keep = true;
              }else{
                Assert( subsume.empty() );
                Trace("sygus-pbe-enum") << "  ...fail : subsumed" << std::endl;
              }
            }
          }else{
            Trace("sygus-pbe-enum") << "  ...fail : it does not satisfy examples." << std::endl;
          }
        }else{
          // must be unique up to examples
          Node val = itv->second.d_term_trie.addCond(this, v, results, true);
          if (val == v)
          {
            Trace("sygus-pbe-enum") << "  ...success!   add to PBE pool : "
                                    << d_tds->sygusToBuiltin(v) << std::endl;
            keep = true;
          }else{
            Trace("sygus-pbe-enum")
                << "  ...fail : term is not unique" << std::endl;
          }
          itc->second.d_cond_count++;
        }
        if( keep ){
          // notify the parent to retry the build of PBE
          itc->second.d_check_sol = true;
          itv->second.addEnumValue( this, v, results );
        }
      }
    }
  }else{
    Trace("sygus-pbe-enum-debug")
        << "  ...examples do not have output." << std::endl;
  }
  // exclude this value on subsequent iterations
  Node g = it->second.d_active_guard;
  if (exp_exc.isNull())
  {
    // if we did not already explain why this should be excluded, use default
    exp_exc = d_tds->getExplain()->getExplanationForEquality(x, v);
  }
  Node exlem =
      NodeManager::currentNM()->mkNode(OR, g.negate(), exp_exc.negate());
  Trace("sygus-pbe-enum-lemma")
      << "CegConjecturePbe : enumeration exclude lemma : " << exlem
      << std::endl;
  lems.push_back(exlem);
}

bool CegConjecturePbe::useStrContainsEnumeratorExclude(Node x, EnumInfo& ei)
{
  TypeNode xbt = d_tds->sygusToBuiltinType(x.getType());
  if (xbt.isString())
  {
    std::map<Node, bool>::iterator itx = d_use_str_contains_eexc.find(x);
    if (itx != d_use_str_contains_eexc.end())
    {
      return itx->second;
    }
    Trace("sygus-pbe-enum-debug")
        << "Is " << x << " is str.contains exclusion?" << std::endl;
    d_use_str_contains_eexc[x] = true;
    for (const Node& sn : ei.d_enum_slave)
    {
      std::map<Node, EnumInfo>::iterator itv = d_einfo.find(sn);
      EnumRole er = itv->second.getRole();
      if (er != enum_io && er != enum_concat_term)
      {
        Trace("sygus-pbe-enum-debug") << "  incompatible slave : " << sn
                                      << ", role = " << er << std::endl;
        d_use_str_contains_eexc[x] = false;
        return false;
      }
      if (itv->second.isConditional())
      {
        Trace("sygus-pbe-enum-debug")
            << "  conditional slave : " << sn << std::endl;
        d_use_str_contains_eexc[x] = false;
        return false;
      }
    }
    Trace("sygus-pbe-enum-debug")
        << "...can use str.contains exclusion." << std::endl;
    return d_use_str_contains_eexc[x];
  }
  return false;
}

bool CegConjecturePbe::getExplanationForEnumeratorExclude(
    Node c,
    Node x,
    Node v,
    std::vector<Node>& results,
    EnumInfo& ei,
    std::vector<Node>& exp)
{
  if (useStrContainsEnumeratorExclude(x, ei))
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
    std::map<Node, std::vector<Node> >::iterator itxo = d_examples_out.find(c);
    Assert(itxo != d_examples_out.end());
    Assert(itxo->second.size() == results.size());
    Trace("sygus-pbe-cterm-debug")
        << "Check enumerator exclusion for " << x << " -> "
        << d_tds->sygusToBuiltin(v) << " based on str.contains." << std::endl;
    std::vector<unsigned> cmp_indices;
    for (unsigned i = 0, size = results.size(); i < size; i++)
    {
      Assert(results[i].isConst());
      Assert(itxo->second[i].isConst());
      Trace("sygus-pbe-cterm-debug")
          << "  " << results[i] << " <> " << itxo->second[i];
      Node cont = nm->mkNode(STRING_STRCTN, itxo->second[i], results[i]);
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
      ncset.init(d_parent, x, itxo->second, cmp_indices);
      // construct the generalized explanation
      d_tds->getExplain()->getExplanationFor(x, v, exp, ncset);
      Trace("sygus-pbe-cterm")
          << "PBE-cterm : enumerator exclude " << d_tds->sygusToBuiltin(v)
          << " due to negative containment." << std::endl;
      return true;
    }
  }
  return false;
}



void CegConjecturePbe::EnumInfo::addEnumValue( CegConjecturePbe * pbe, Node v, std::vector< Node >& results ) {
  d_enum_val_to_index[v] = d_enum_vals.size();
  d_enum_vals.push_back( v );
  d_enum_vals_res.push_back( results );
  /*
  if( getRole()==enum_io ){
    // compute
    if( d_enum_total.empty() ){
      d_enum_total = results;
    }else if( !d_enum_total_true ){
      d_enum_total_true = true;
      Assert( d_enum_total.size()==results.size() );
      for( unsigned i=0; i<results.size(); i++ ){
        if( d_enum_total[i]==pbe->d_true || results[i]==pbe->d_true ){
          d_enum_total[i] = pbe->d_true;
        }else{
          d_enum_total[i] = pbe->d_false;
          d_enum_total_true = false;
        }
      }
    }
  }
  */
}

void CegConjecturePbe::EnumInfo::initialize(Node c, EnumRole role)
{
  d_parent_candidate = c;
  d_role = role;
}

void CegConjecturePbe::EnumInfo::setSolved( Node slv ) {
  d_enum_solved = slv;
  //d_enum_total_true = true;
}
    
void CegConjecturePbe::CandidateInfo::initialize( Node c ) {
  d_this_candidate = c;
  d_root = c.getType();
}

void CegConjecturePbe::CandidateInfo::initializeType( TypeNode tn ) {
  d_tinfo[tn].d_this_type = tn;
  d_tinfo[tn].d_parent = this;
}

Node CegConjecturePbe::CandidateInfo::getRootEnumerator() {
  std::map<EnumRole, Node>::iterator it = d_tinfo[d_root].d_enum.find(enum_io);
  Assert( it!=d_tinfo[d_root].d_enum.end() );
  return it->second;
}

bool CegConjecturePbe::CandidateInfo::isNonTrivial() {
  //TODO
  return true;
}

// status : 0 : exact, -1 : vals is subset, 1 : vals is superset
Node CegConjecturePbe::SubsumeTrie::addTermInternal( CegConjecturePbe * pbe, Node t, std::vector< Node >& vals, bool pol, 
                                                     std::vector< Node >& subsumed, bool spol, IndexFilter * f, 
                                                     unsigned index, int status, bool checkExistsOnly, bool checkSubsume ) {
  if( index==vals.size() ){
    if( status==0 ){
      // set the term if checkExistsOnly = false
      if( d_term.isNull() && !checkExistsOnly ){
        d_term = t;
      }
    }else if( status==1 ){
      Assert( checkSubsume );
      // found a subsumed term
      if( !d_term.isNull() ){
        subsumed.push_back( d_term );
        if( !checkExistsOnly ){
          // remove it if checkExistsOnly = false
          d_term = Node::null();
        }
      }
    }else{
      Assert( !checkExistsOnly && checkSubsume );
    }
    return d_term;
  }else{
    // the current value 
    Assert( pol || ( vals[index].isConst() && vals[index].getType().isBoolean() ) );
    Node cv = pol ? vals[index] : ( vals[index]==pbe->d_true ? pbe->d_false : pbe->d_true );
    // if checkExistsOnly = false, check if the current value is subsumed if checkSubsume = true, if so, don't add
    if( !checkExistsOnly && checkSubsume ){
      std::vector< bool > check_subsumed_by;
      if( status==0 ){
        if( cv==pbe->d_false ){
          check_subsumed_by.push_back( spol );
        }
      }else if( status==-1 ){
        check_subsumed_by.push_back( spol );
        if( cv==pbe->d_false ){
          check_subsumed_by.push_back( !spol );
        }
      }
      // check for subsumed nodes
      for( unsigned i=0; i<check_subsumed_by.size(); i++ ){
        Node csval = check_subsumed_by[i] ? pbe->d_true : pbe->d_false;
        // check if subsumed
        std::map< Node, SubsumeTrie >::iterator itc = d_children.find( csval );
        if( itc!=d_children.end() ){
          unsigned next_index = f ? f->next( index ) : index+1;
          Node ret = itc->second.addTermInternal( pbe, t, vals, pol, subsumed, spol, f, next_index, -1, checkExistsOnly, checkSubsume );
          // ret subsumes t
          if( !ret.isNull() ){
            return ret;
          }
        }
      }
    }
    Node ret;
    std::vector< bool > check_subsume;
    if( status==0 ){
      unsigned next_index = f ? f->next( index ) : index+1;
      if( checkExistsOnly ){
        std::map< Node, SubsumeTrie >::iterator itc = d_children.find( cv );
        if( itc!=d_children.end() ){
          ret = itc->second.addTermInternal( pbe, t, vals, pol, subsumed, spol, f, next_index, 0, checkExistsOnly, checkSubsume );
        }
      }else{
        Assert( spol );
        ret = d_children[cv].addTermInternal( pbe, t, vals, pol, subsumed, spol, f, next_index, 0, checkExistsOnly, checkSubsume );
        if( ret!=t ){
          // we were subsumed by ret, return
          return ret;
        }
      }
      if( checkSubsume ){
        // check for subsuming
        if( cv==pbe->d_true ){
          check_subsume.push_back( !spol );
        }
      }
    }else if( status==1 ){
      Assert( checkSubsume );
      check_subsume.push_back( !spol );
      if( cv==pbe->d_true ){
        check_subsume.push_back( spol );
      }
    }
    if( checkSubsume ){
      // check for subsumed terms
      for( unsigned i=0; i<check_subsume.size(); i++ ){
        Node csval = check_subsume[i] ? pbe->d_true : pbe->d_false;
        std::map< Node, SubsumeTrie >::iterator itc = d_children.find( csval );
        if( itc!=d_children.end() ){
          unsigned next_index = f ? f->next( index ) : index+1;
          itc->second.addTermInternal( pbe, t, vals, pol, subsumed, spol, f, next_index, 1, checkExistsOnly, checkSubsume );
          // clean up
          if( itc->second.isEmpty() ){
            Assert( !checkExistsOnly );
            d_children.erase( csval );
          }
        }
      }
    }
    return ret;
  }
}

Node CegConjecturePbe::SubsumeTrie::addTerm( CegConjecturePbe * pbe, Node t, std::vector< Node >& vals, bool pol, std::vector< Node >& subsumed, IndexFilter * f ) {
  unsigned start_index = f ? f->start() : 0;
  return addTermInternal( pbe, t, vals, pol, subsumed, true, f, start_index, 0, false, true );
}

Node CegConjecturePbe::SubsumeTrie::addCond( CegConjecturePbe * pbe, Node c, std::vector< Node >& vals, bool pol, IndexFilter * f ) {
  unsigned start_index = f ? f->start() : 0;
  std::vector< Node > subsumed;
  return addTermInternal( pbe, c, vals, pol, subsumed, true, f, start_index, 0, false, false );
}

void CegConjecturePbe::SubsumeTrie::getSubsumed( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::vector< Node >& subsumed, IndexFilter * f ){
  unsigned start_index = f ? f->start() : 0;
  addTermInternal( pbe, Node::null(), vals, pol, subsumed, true, f, start_index, 1, true, true );
}

void CegConjecturePbe::SubsumeTrie::getSubsumedBy( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::vector< Node >& subsumed_by, IndexFilter * f ){
  // flip polarities
  unsigned start_index = f ? f->start() : 0;
  addTermInternal( pbe, Node::null(), vals, !pol, subsumed_by, false, f, start_index, 1, true, true );
}

void CegConjecturePbe::SubsumeTrie::getLeavesInternal( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::map< int, std::vector< Node > >& v, 
                                                       IndexFilter * f, unsigned index, int status ) {
  if( index==vals.size() ){
    Assert( !d_term.isNull() );
    Assert( std::find( v[status].begin(), v[status].end(), d_term )==v[status].end() );
    v[status].push_back( d_term );
  }else{
    Assert( vals[index].isConst() && vals[index].getType().isBoolean() );
    // filter should be for cv
    Assert( f==NULL || vals[index]==( pol ? pbe->d_true : pbe->d_false ) );
    for( std::map< Node, SubsumeTrie >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
      int new_status = status;
      // if the current value is true
      if( vals[index]==( pol ? pbe->d_true : pbe->d_false ) ){
        if( status!=0 ){
          new_status = ( it->first == pbe->d_true ? 1 : -1 );
          if( status!=-2 && new_status!=status ){
            new_status = 0;
          }
        }
      }
      unsigned next_index = f ? f->next( index ) : index+1;
      it->second.getLeavesInternal( pbe, vals, pol, v, f, next_index, new_status );
    }
  }
}

void CegConjecturePbe::SubsumeTrie::getLeaves( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::map< int, std::vector< Node > >& v, IndexFilter * f ) {
  unsigned start_index = f ? f->start() : 0;
  getLeavesInternal( pbe, vals, pol, v, f, start_index, -2 );
}

void CegConjecturePbe::IndexFilter::mk( std::vector< Node >& vals, bool pol ) {
  Trace("sygus-pbe-debug") << "Make for : ";
  print_val( "sygus-pbe-debug", vals, pol );
  Trace("sygus-pbe-debug") << std::endl;
  Node poln = NodeManager::currentNM()->mkConst( pol );
  
  unsigned curr_index = 0;
  while( curr_index<vals.size() && vals[curr_index]!=poln ){
    curr_index++;
  }
  d_next[0] = curr_index;
  Trace("sygus-pbe-debug") << "0 -> " << curr_index << std::endl;
  unsigned i = curr_index;
  while( i<vals.size() ){
    while( i<vals.size() && vals[i]!=poln ){
      i++;
    }
    i++;
    d_next[curr_index+1] = i;
    Trace("sygus-pbe-debug") << curr_index+1 << " -> " << i << std::endl;
    curr_index = i;
  }
  
  // verify it is correct
  unsigned j = start();
  for( unsigned k=0; k<j; k++ ){
    AlwaysAssert( vals[k]!=poln );
  }
  Trace("sygus-pbe-debug") << "...start : " << j << std::endl;
  unsigned counter = 0;
  while( j<vals.size() ){
    Trace("sygus-pbe-debug") << "...at : " << j << std::endl;
    AlwaysAssert( vals[j]==poln );
    unsigned jj = next( j );
    AlwaysAssert( jj>j );
    for( unsigned k=(j+1); k<jj; k++ ){
      AlwaysAssert( vals[k]!=poln );
    }
    AlwaysAssert( counter<=vals.size() );
    counter++;
    j = jj;
  }
  
  
}

unsigned CegConjecturePbe::IndexFilter::start() {
  std::map< unsigned, unsigned >::iterator it = d_next.find( 0 );
  if( it==d_next.end() ){
    return 0;
  }else{
    return it->second;
  }
}

unsigned CegConjecturePbe::IndexFilter::next( unsigned i ) {
  std::map< unsigned, unsigned >::iterator it = d_next.find( i+1 );
  if( it==d_next.end() ){
    return i+1;
  }else{
    return it->second;
  }      
}

bool CegConjecturePbe::IndexFilter::isEq( std::vector< Node >& vals, Node v ) {
  unsigned index = start();
  while( index<vals.size() ){
    if( vals[index]!=v ){
      return false;
    }
    index = next( index );
  }
  return true;
}

Node CegConjecturePbe::constructSolution( Node c ){
  std::map< Node, CandidateInfo >::iterator itc = d_cinfo.find( c );
  Assert( itc!=d_cinfo.end() );
  if( !itc->second.d_solution.isNull() ){
    // already has a solution
    return itc->second.d_solution;
  }else{
    // only check if an enumerator updated
    if( itc->second.d_check_sol ){
      Trace("sygus-pbe") << "Construct solution, #iterations = " << itc->second.d_cond_count << std::endl;
      itc->second.d_check_sol = false;
      // try multiple times if we have done multiple conditions, due to non-determinism
      Node vc;
      for( unsigned i=0; i<=itc->second.d_cond_count; i++ ){
        Trace("sygus-pbe-dt") << "ConstructPBE for candidate: " << c << std::endl;
        Node e = itc->second.getRootEnumerator();
        UnifContext x;
        x.initialize( this, c );
        Node vcc = constructSolution(c, e, role_equal, x, 1);
        if( !vcc.isNull() ){
          if( vc.isNull() || ( !vc.isNull() && d_tds->getSygusTermSize( vcc )<d_tds->getSygusTermSize( vc ) ) ){
            Trace("sygus-pbe") << "**** PBE SOLVED : " << c << " = " << vcc << std::endl;
            Trace("sygus-pbe") << "...solved at iteration " << i << std::endl;
            vc = vcc;
          }
        }
      }
      if( !vc.isNull() ){
        itc->second.d_solution = vc;
        return vc;
      }
      Trace("sygus-pbe") << "...failed to solve." << std::endl;
    }
    return Node::null();
  }
}

Node CegConjecturePbe::constructBestSolvedTerm( std::vector< Node >& solved, UnifContext& x ){
  Assert( !solved.empty() );
  // TODO
  return solved[0];
}

Node CegConjecturePbe::constructBestStringSolvedTerm( std::vector< Node >& solved, UnifContext& x ) {
  Assert( !solved.empty() );
  // TODO
  return solved[0];
}

Node CegConjecturePbe::constructBestSolvedConditional( std::vector< Node >& solved, UnifContext& x ){
  Assert( !solved.empty() );
  // TODO
  return solved[0];
}

Node CegConjecturePbe::constructBestConditional( std::vector< Node >& conds, UnifContext& x ) {
  Assert( !conds.empty() );
  // TODO
  double r = Random::getRandom().pickDouble(0.0, 1.0);
  unsigned cindex = r*conds.size();
  if( cindex>conds.size() ){
    cindex = conds.size() - 1;
  }
  return conds[cindex];
}

Node CegConjecturePbe::constructBestStringToConcat( std::vector< Node > strs,
                                                    std::map< Node, unsigned > total_inc, 
                                                    std::map< Node, std::vector< unsigned > > incr,
                                                    UnifContext& x ) {
  Assert( !strs.empty() );
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

Node CegConjecturePbe::constructSolution(
    Node c, Node e, NodeRole nrole, UnifContext& x, int ind)
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
  std::map<TypeNode, EnumTypeInfo>::iterator itt = d_cinfo[c].d_tinfo.find(etn);
  Assert(itt != d_cinfo[c].d_tinfo.end());
  EnumTypeInfo& tinfo = itt->second;

  // get the enumerator information
  std::map< Node, EnumInfo >::iterator itn = d_einfo.find( e );
  Assert( itn!=d_einfo.end() );
  EnumInfo& einfo = itn->second;

  Node ret_dt;
  if (nrole == role_equal)
  {
    if (!x.isReturnValueModified())
    {
      if (einfo.isSolved())
      {
        // this type has a complete solution
        ret_dt = einfo.getSolved();
        indent("sygus-pbe-dt", ind);
        Trace("sygus-pbe-dt") << "return PBE: success : solved "
                              << d_tds->sygusToBuiltin(ret_dt) << std::endl;
        Assert(!ret_dt.isNull());
      }
      else
      {
        // could be conditionally solved
        std::vector<Node> subsumed_by;
        einfo.d_term_trie.getSubsumedBy(this, x.d_vals, true, subsumed_by);
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
        std::map<Node, EnumInfo>::iterator itet;
        std::map<EnumRole, Node>::iterator itnt =
            tinfo.d_enum.find(enum_concat_term);
        if( itnt != itt->second.d_enum.end() ){
          Node et = itnt->second;
          itet = d_einfo.find( et );
          Assert(itet != d_einfo.end());
        }else{
          success = false;
        }
        if (success)
        {
          // get the current examples
          std::map<Node, std::vector<Node> >::iterator itx =
              d_examples_out.find(c);
          Assert(itx != d_examples_out.end());
          std::vector<String> ex_vals;
          x.getCurrentStrings(this, itx->second, ex_vals);
          Assert(itn->second.d_enum_vals.size()
                 == itn->second.d_enum_vals_res.size());

          // test each example in the term enumerator for the type
          std::vector<Node> str_solved;
          for (unsigned i = 0, size = itet->second.d_enum_vals.size(); i < size;
               i++)
          {
            if (x.isStringSolved(
                    this, ex_vals, itet->second.d_enum_vals_res[i]))
            {
              str_solved.push_back(itet->second.d_enum_vals[i]);
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
            Trace("sygus-pbe-dt-debug") << "  ...not currently string solved."
                                        << std::endl;
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
      std::map<Node, std::vector<Node> >::iterator itx = d_examples_out.find(c);
      Assert(itx != d_examples_out.end());
      // make the value of the examples
      std::vector<String> ex_vals;
      x.getCurrentStrings(this, itx->second, ex_vals);
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
      Assert(einfo.d_enum_vals.size() == einfo.d_enum_vals_res.size());

      for (unsigned i = 0, size = einfo.d_enum_vals.size(); i < size; i++)
      {
        Node val_t = einfo.d_enum_vals[i];
        indent("sygus-pbe-dt-debug", ind);
        Trace("sygus-pbe-dt-debug") << "increment string values : " << val_t
                                    << " : ";
        Assert(einfo.d_enum_vals_res[i].size() == itx->second.size());
        unsigned tot = 0;
        bool exsuccess = x.getStringIncrement(this,
                                              isPrefix,
                                              ex_vals,
                                              einfo.d_enum_vals_res[i],
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
          Trace("sygus-pbe-dt-debug") << "...success, total increment = " << tot
                                      << std::endl;
        }
      }

      if (!incr.empty())
      {
        ret_dt = constructBestStringToConcat(inc_strs, total_inc, incr, x);
        Assert(!ret_dt.isNull());
        indent("sygus-pbe-dt", ind);
        Trace("sygus-pbe-dt") << "PBE: CONCAT strategy : choose "
                              << (isPrefix ? "pre" : "suf") << "fix value "
                              << d_tds->sygusToBuiltin(ret_dt) << std::endl;
        // update the context
        bool ret = x.updateStringPosition(this, incr[ret_dt]);
        AlwaysAssert(ret == (total_inc[ret_dt] > 0));
        x.d_has_string_pos = nrole;
      }else{
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
               && !x.isValidStrategy(snode.d_strats[sindex]))
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
      Trace("sygus-pbe-dt") << "...try STRATEGY " << strat << "..."
                            << std::endl;

      std::map<unsigned, Node> look_ahead_solved_children;
      std::vector<Node> dt_children_cons;
      bool success = true;

      // for ITE
      Node split_cond_enum;
      int split_cond_res_index = -1;

      for (unsigned sc = 0, size = etis->d_cenum.size(); sc < size; sc++)
      {
        indent("sygus-pbe-dt", ind + 1);
        Trace("sygus-pbe-dt") << "construct PBE child #" << sc << "..."
                              << std::endl;
        Node rec_c;
        std::map<unsigned, Node>::iterator itla =
            look_ahead_solved_children.find(sc);
        if (itla != look_ahead_solved_children.end())
        {
          rec_c = itla->second;
          indent("sygus-pbe-dt-debug", ind + 1);
          Trace("sygus-pbe-dt-debug") << "ConstructPBE: look ahead solved : "
                                      << d_tds->sygusToBuiltin(rec_c)
                                      << std::endl;
        }
        else
        {
          std::pair<Node, NodeRole>& cenum = etis->d_cenum[sc];

          // update the context
          std::vector<Node> prev;
          if (strat == strat_ITE && sc > 0)
          {
            std::map<Node, EnumInfo>::iterator itnc =
                d_einfo.find(split_cond_enum);
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
            std::map<Node, EnumInfo>::iterator itnc = d_einfo.find(ce);
            Assert(itnc != d_einfo.end());
            EnumInfo& einfo_child = itnc->second;

            // only used if the return value is not modified
            if (!x.isReturnValueModified())
            {
              if (x.d_uinfo.find(ce) == x.d_uinfo.end())
              {
                Trace("sygus-pbe-dt-debug2")
                    << "  reg : PBE: Look for direct solutions for conditional "
                       "enumerator "
                    << ce << " ... " << std::endl;
                Assert(einfo_child.d_enum_vals.size()
                       == einfo_child.d_enum_vals_res.size());
                for (unsigned i = 1; i <= 2; i++)
                {
                  std::pair<Node, NodeRole>& te_pair = etis->d_cenum[i];
                  Node te = te_pair.first;
                  std::map<Node, EnumInfo>::iterator itnt = d_einfo.find(te);
                  Assert(itnt != d_einfo.end());
                  bool branch_pol = (i == 1);
                  // for each condition, get terms that satisfy it in this
                  // branch
                  for (unsigned k = 0, size = einfo_child.d_enum_vals.size();
                       k < size;
                       k++)
                  {
                    Node cond = einfo_child.d_enum_vals[k];
                    std::vector<Node> solved;
                    itnt->second.d_term_trie.getSubsumedBy(
                        this,
                        einfo_child.d_enum_vals_res[k],
                        branch_pol,
                        solved);
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
            einfo_child.d_term_trie.getLeaves(
                this, x.d_vals, true, possible_cond);

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
                  Trace("sygus-pbe-dt-debug") << d_tds->sygusToBuiltin(cond)
                                              << std::endl;
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
            if( !rec_c.isNull() ){
              Assert(einfo_child.d_enum_val_to_index.find(rec_c)
                     != einfo_child.d_enum_val_to_index.end());
              split_cond_res_index = einfo_child.d_enum_val_to_index[rec_c];
              split_cond_enum = ce;
              Assert(split_cond_res_index >= 0);
              Assert(split_cond_res_index
                     < (int)einfo_child.d_enum_vals_res.size());
            }
          }
          else
          {
            rec_c = constructSolution(c, cenum.first, cenum.second, x, ind + 2);
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
      }else{
        indent("sygus-pbe-dt-debug", ind);
        Trace("sygus-pbe-dt-debug") << "PBE: failed for strategy " << strat
                                    << std::endl;
      }
    }
  }

  if( !ret_dt.isNull() ){
    Assert( ret_dt.getType()==e.getType() );
  }
  indent("sygus-pbe-dt", ind);
  Trace("sygus-pbe-dt") << "ConstructPBE: returned " << ret_dt << std::endl;
  return ret_dt;
}

bool CegConjecturePbe::UnifContext::updateContext( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol ) {
  Assert( d_vals.size()==vals.size() );
  bool changed = false;
  Node poln = pol ? pbe->d_true : pbe->d_false;
  for( unsigned i=0; i<vals.size(); i++ ){
    if( vals[i]!=poln ){
      if( d_vals[i]==pbe->d_true ){
        d_vals[i] = pbe->d_false;
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

bool CegConjecturePbe::UnifContext::updateStringPosition( CegConjecturePbe * pbe, std::vector< unsigned >& pos ) {
  Assert( pos.size()==d_str_pos.size() );
  bool changed = false;
  for( unsigned i=0; i<pos.size(); i++ ){
    if( pos[i]>0 ){
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

bool CegConjecturePbe::UnifContext::isReturnValueModified() {
  if (d_has_string_pos != role_invalid)
  {
    return true;
  }
  return false;
}

bool CegConjecturePbe::UnifContext::isValidStrategy(EnumTypeInfoStrat* etis)
{
  StrategyType st = etis->d_this;
  if (d_has_string_pos == role_string_prefix && st == strat_CONCAT_SUFFIX)
  {
    return false;
  }
  if (d_has_string_pos == role_string_suffix && st == strat_CONCAT_PREFIX)
  {
    return false;
  }
  return true;
}

void CegConjecturePbe::UnifContext::initialize( CegConjecturePbe * pbe, Node c ) {
  Assert( d_vals.empty() );
  Assert( d_str_pos.empty() );
  
  // initialize with #examples
  Assert( pbe->d_examples.find( c )!=pbe->d_examples.end() );
  unsigned sz = pbe->d_examples[c].size();
  for( unsigned i=0; i<sz; i++ ){
    d_vals.push_back( pbe->d_true );
  }
  
  if( !pbe->d_examples_out[c].empty() ){
    // output type of the examples
    TypeNode exotn = pbe->d_examples_out[c][0].getType();
    
    if( exotn.isString() ){
      for( unsigned i=0; i<sz; i++ ){
        d_str_pos.push_back( 0 );
      }
    }
  }
  d_visit_role.clear();
}

void CegConjecturePbe::UnifContext::getCurrentStrings(
    CegConjecturePbe* pbe,
    const std::vector<Node>& vals,
    std::vector<String>& ex_vals)
{
  bool isPrefix = d_has_string_pos == role_string_prefix;
  String dummy;
  for( unsigned i=0; i<vals.size(); i++ ){
    if( d_vals[i]==pbe->d_true ){
      Assert( vals[i].isConst() );
      unsigned pos_value = d_str_pos[i];
      if( pos_value>0 ){
        Assert(d_has_string_pos != role_invalid);
        String s = vals[i].getConst<String>();
        Assert( pos_value<=s.size() );
        ex_vals.push_back( isPrefix ? s.suffix( s.size()-pos_value ) : 
                                      s.prefix( s.size()-pos_value ) );
      }else{
        ex_vals.push_back( vals[i].getConst<String>() );
      }
    }else{
      // irrelevant, add dummy
      ex_vals.push_back( dummy );
    }
  }
}

bool CegConjecturePbe::UnifContext::getStringIncrement(
    CegConjecturePbe* pbe,
    bool isPrefix,
    const std::vector<String>& ex_vals,
    const std::vector<Node>& vals,
    std::vector<unsigned>& inc,
    unsigned& tot)
{
  for( unsigned j=0; j<vals.size(); j++ ){
    unsigned ival = 0;
    if( d_vals[j]==pbe->d_true ){
      // example is active in this context
      Assert( vals[j].isConst() );
      String mystr = vals[j].getConst<String>();
      ival = mystr.size();
      if( mystr.size()<=ex_vals[j].size() ){
        if( !( isPrefix ? ex_vals[j].strncmp(mystr, ival) : ex_vals[j].rstrncmp(mystr, ival) ) ){
          Trace("sygus-pbe-dt-debug") << "X";
          return false;
        }
      }else{
        Trace("sygus-pbe-dt-debug") << "X";
        return false;
      }
    }
    Trace("sygus-pbe-dt-debug") << ival;
    tot += ival;
    inc.push_back( ival );
  }
  return true;
}
bool CegConjecturePbe::UnifContext::isStringSolved(
    CegConjecturePbe* pbe,
    const std::vector<String>& ex_vals,
    const std::vector<Node>& vals)
{
  for( unsigned j=0; j<vals.size(); j++ ){
    if( d_vals[j]==pbe->d_true ){
      // example is active in this context
      Assert( vals[j].isConst() );
      String mystr = vals[j].getConst<String>();
      if( ex_vals[j]!=mystr ){
        return false;
      }
    }
  }
  return true;
}

CegConjecturePbe::StrategyNode::~StrategyNode()
{
  for (unsigned j = 0, size = d_strats.size(); j < size; j++)
  {
    delete d_strats[j];
  }
  d_strats.clear();
}
}
}
}
