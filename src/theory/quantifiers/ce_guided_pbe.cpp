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
#include "theory/quantifiers/ce_guided_pbe.h"

#include "expr/datatype.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/datatypes/datatypes_rewriter.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

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

void CegConjecturePbe::print_role(const char* c, unsigned r)
{
  switch(r){
  case CegConjecturePbe::enum_io:Trace(c) << "IO";break;
  case CegConjecturePbe::enum_ite_condition:Trace(c) << "CONDITION";break;
  case CegConjecturePbe::enum_concat_term:Trace(c) << "CTERM";break;
  case CegConjecturePbe::enum_any:Trace(c) << "ANY";break;
  default:Trace(c) << "role_" << r;break;
  }
}

void CegConjecturePbe::print_strat(const char* c, unsigned s)
{
  switch (s)
  {
    case CegConjecturePbe::strat_ITE: Trace(c) << "ITE"; break;
    case CegConjecturePbe::strat_CONCAT: Trace(c) << "CONCAT"; break;
    case CegConjecturePbe::strat_ID: Trace(c) << "ID"; break;
    default: Trace(c) << "strat_" << s; break;
  }
}

CegConjecturePbe::CegConjecturePbe(QuantifiersEngine* qe, CegConjecture* p)
    : d_qe(qe),
      d_parent(p){
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

void CegConjecturePbe::initialize(Node n,
                                  std::vector<Node>& candidates,
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
        collectEnumeratorTypes( c, ctn, enum_io );
        // if we have non-trivial strategies, then use pbe
        if( d_cinfo[c].isNonTrivial() ){
          // static learning of redundant constructors
          staticLearnRedundantOps( c, lemmas );
          d_is_pbe = true;
        }
      }
    }
  }
  if( !d_is_pbe ){
    Trace("sygus-unif") << "Do not do PBE optimizations, register..." << std::endl;
    for( unsigned i=0; i<candidates.size(); i++ ){
      d_qe->getTermDatabaseSygus()->registerEnumerator(
          candidates[i], candidates[i], d_parent);
    }
  }
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


void CegConjecturePbe::registerEnumerator( Node et, Node c, TypeNode tn, unsigned enum_role, bool inSearch ) {
  Trace("sygus-unif-debug") << "...register " << et << " for " << ((DatatypeType)tn.toType()).getDatatype().getName();
  Trace("sygus-unif-debug") << ", role = ";
  print_role( "sygus-unif-debug", enum_role );
  Trace("sygus-unif-debug") << ", in search = " << inSearch << std::endl;
  d_einfo[et].initialize(c, enum_role);
  // if we are actually enumerating this (could be a compound node in the strategy)
  if( inSearch ){
    std::map< TypeNode, Node >::iterator itn = d_cinfo[c].d_search_enum.find( tn );
    if( itn==d_cinfo[c].d_search_enum.end() ){
      // use this for the search
      d_cinfo[c].d_search_enum[tn] = et;
      d_cinfo[c].d_esym_list.push_back( et );
      d_einfo[et].d_enum_slave.push_back( et );
      //register measured term with database
      d_qe->getTermDatabaseSygus()->registerEnumerator(et, c, d_parent, true);
      d_einfo[et].d_active_guard =
          d_qe->getTermDatabaseSygus()->getActiveGuardForEnumerator(et);
    }else{
      Trace("sygus-unif-debug") << "Make " << et << " a slave of " << itn->second << std::endl;
      d_einfo[itn->second].d_enum_slave.push_back( et );
    }
  }
}

void CegConjecturePbe::collectEnumeratorTypes( Node e, TypeNode tn, unsigned enum_role ) {
  if( d_cinfo[e].d_tinfo.find( tn )==d_cinfo[e].d_tinfo.end() ){
    // register type
    Trace("sygus-unif") << "Register enumerating type : " << tn << std::endl;
    d_cinfo[e].initializeType( tn );
  }
  if( d_cinfo[e].d_tinfo[tn].d_enum.find( enum_role )==d_cinfo[e].d_tinfo[tn].d_enum.end() ){
  
    Node ee = NodeManager::currentNM()->mkSkolem( "ee", tn );
    d_cinfo[e].d_tinfo[tn].d_enum[enum_role] = ee;
    Trace("sygus-unif-debug") << "...enumerator " << ee << " for " << ((DatatypeType)tn.toType()).getDatatype().getName() << ", role = ";
    print_role( "sygus-unif-debug", enum_role );
    Trace("sygus-unif-debug") << std::endl;
    // wait to register : may or may not actually be enumerating it

    if( enum_role==enum_io ){
      // look at information on how we will construct solutions for this type
      Assert( tn.isDatatype() );
      const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
      Assert( dt.isSygus() );
      std::map< Node, std::vector< TypeNode > > cop_to_child_types;
      std::map< Node, std::map< unsigned, Node > > cop_to_child_templ;
      std::map< Node, std::map< unsigned, Node > > cop_to_child_templ_arg;
      std::map< Node, unsigned > cop_to_strat;
      std::map< Node, unsigned > cop_to_cindex;

      // look at builtin operartors first (when r=0), then defined operators
      // (when r=1)
      for( unsigned r=0; r<2; r++ ){
        for( unsigned j=0; j<dt.getNumConstructors(); j++ ){
          Node cop = Node::fromExpr( dt[j].getConstructor() );
          Node op = Node::fromExpr( dt[j].getSygusOp() );
          if( r==0 ){
            cop_to_cindex[cop] = j;
            if( op.getKind() == kind::BUILTIN ){
              Kind sk = NodeManager::operatorToKind( op );
              if( sk==kind::ITE ){
                // we can do unification
                Assert( dt[j].getNumArgs()==3 );
                cop_to_strat[cop] = strat_ITE;
              }else if( sk==kind::STRING_CONCAT ){
                if( dt[j].getNumArgs()==2 ) {
                  cop_to_strat[cop] = strat_CONCAT;
                }
              }
              if( cop_to_strat.find( cop )!=cop_to_strat.end() ){
                Trace("sygus-unif") << "...type " << dt.getName()
                                    << " has strategy ";
                print_strat("sygus-unif", cop_to_strat[cop]);
                Trace("sygus-unif") << "..." << std::endl;
                // add child types
                for( unsigned k=0; k<dt[j].getNumArgs(); k++ ){
                  TypeNode ct = TypeNode::fromType( dt[j][k].getRangeType() );
                  Trace("sygus-unif") << "   Child type " << k << " : " << ((DatatypeType)ct.toType()).getDatatype().getName() << std::endl;
                  cop_to_child_types[cop].push_back( ct );
                }
              }
            }
          }else if( cop_to_strat.find( cop )==cop_to_strat.end() ){
            // could be a defined function (this handles the ICFP benchmarks)
            std::vector< Node > utchildren;
            utchildren.push_back( cop );
            std::vector< Node > sks;
            std::vector< TypeNode > sktns;
            for( unsigned k=0; k<dt[j].getNumArgs(); k++ ){
              Type t = dt[j][k].getRangeType();
              TypeNode ttn = TypeNode::fromType( t );
              Node kv = NodeManager::currentNM()->mkSkolem( "ut", ttn );
              sks.push_back( kv );
              sktns.push_back( ttn );
              utchildren.push_back( kv );
            }
            Node ut = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, utchildren );
            std::vector< Node > echildren;
            echildren.push_back( Node::fromExpr( dt.getSygusEvaluationFunc() ) );
            echildren.push_back( ut );
            Node sbvl = Node::fromExpr( dt.getSygusVarList() );
            for( unsigned k=0; k<sbvl.getNumChildren(); k++ ){
              echildren.push_back( sbvl[k] );
            }
            Node eut = NodeManager::currentNM()->mkNode( kind::APPLY_UF, echildren );
            Trace("sygus-unif-debug2") << "Test evaluation of " << eut << "..." << std::endl;
            eut = d_qe->getTermDatabaseSygus()->unfold( eut );
            Trace("sygus-unif-debug2") << "...got " << eut << std::endl;       
            Trace("sygus-unif-debug2") << "Type : " << eut.getType() << std::endl;     

            if( eut.getKind()==kind::ITE ){
              if( dt[j].getNumArgs()>=eut.getNumChildren() ){
                cop_to_strat[cop] = strat_ITE;
              }
            }else if( eut.getKind()==kind::STRING_CONCAT ){
              if (dt[j].getNumArgs() >= eut.getNumChildren()
                  && eut.getNumChildren() == 2)
              {
                cop_to_strat[cop] = strat_CONCAT;
              }
            }else if( eut.getKind()==kind::APPLY_UF ){
              // identity operator?
              if( dt[j].getNumArgs()==1 ){
                cop_to_strat[cop] = strat_ID;
              }
            }
            
            if( cop_to_strat.find( cop )!=cop_to_strat.end() ){
              std::map< unsigned, unsigned > templ_injection;
              std::vector< Node > vs;
              std::vector< Node > ss;
              std::map< Node, unsigned > templ_var_index;
              for( unsigned k=0; k<sks.size(); k++ ){
                Assert( sks[k].getType().isDatatype() );
                const Datatype& cdt = ((DatatypeType)sks[k].getType().toType()).getDatatype();
                echildren[0] = Node::fromExpr( cdt.getSygusEvaluationFunc() );
                echildren[1] = sks[k];
                Trace("sygus-unif-debug2") << "...set eval dt to " << sks[k] << std::endl;
                Node esk = NodeManager::currentNM()->mkNode( kind::APPLY_UF, echildren );
                vs.push_back( esk );
                Node tvar = NodeManager::currentNM()->mkSkolem( "templ", esk.getType() );
                templ_var_index[tvar] = k;
                Trace("sygus-unif-debug2") << "* template inference : looking for " << tvar << " for arg " << k << std::endl;
                ss.push_back( tvar );
                Trace("sygus-unif-debug2") << "* substitute : " << esk << " -> " << tvar << std::endl;
              }
              eut = eut.substitute( vs.begin(), vs.end(), ss.begin(), ss.end() );
              Trace("sygus-unif-debug2") << "Defined constructor " << j << ", base term is " << eut << std::endl;
              std::map< unsigned, Node > test_args;
              if( cop_to_strat[cop] == strat_ID ){
                test_args[0] = eut;
              }else{
                for( unsigned k=0; k<eut.getNumChildren(); k++ ){
                  test_args[k] = eut[k];
                }
              }
              for( std::map< unsigned, Node >::iterator it = test_args.begin(); it != test_args.end(); ++it ){
                unsigned k = it->first;
                Node eut_c = it->second;
                //success if we can find a injection from args to sygus args
                if( !inferTemplate( k, eut_c, templ_var_index, templ_injection ) ){
                  Trace("sygus-unif-debug2") << "...failed to find injection (range)." << std::endl;
                  cop_to_strat.erase( cop );
                  break;
                }
                if( templ_injection.find( k )==templ_injection.end() ){
                  Trace("sygus-unif-debug2") << "...failed to find injection (domain)." << std::endl;
                  cop_to_strat.erase( cop );
                  break;
                }
              }
              if( cop_to_strat.find( cop )!=cop_to_strat.end() ){
                Trace("sygus-unif") << "...type " << dt.getName() << " has defined constructor matching strategy ";
                print_strat("sygus-unif", cop_to_strat[cop]);
                Trace("sygus-unif") << "..." << std::endl;
                for( unsigned k=0; k<eut.getNumChildren(); k++ ){
                  Assert( templ_injection.find( k )!=templ_injection.end() );
                  unsigned sk_index = templ_injection[k];
                  //also store the template information, if necessary
                  Node teut = eut[k];
                  if( !teut.isVar() ){
                    if( cop_to_strat[cop] == strat_ID ){
                      Trace("sygus-unif-debug") << "...cannot use template with ID strategy." << std::endl;
                      cop_to_strat.erase( cop );
                    }else{
                      cop_to_child_templ[cop][k] = teut;
                      cop_to_child_templ_arg[cop][k] = ss[sk_index];
                      Trace("sygus-unif") << "  Arg " << k << " : template : " << teut << ", arg " << ss[sk_index] << std::endl;
                    }
                  }else{
                    Assert( teut==ss[sk_index] );
                  }
                }
                // collect children types
                for( unsigned k=0; k<dt[j].getNumArgs(); k++ ){
                  Trace("sygus-unif") << "   Child type " << k << " : " << ((DatatypeType)sktns[k].toType()).getDatatype().getName() << std::endl;
                  cop_to_child_types[cop].push_back( sktns[k] );
                }
              }
            }
          }
        }
      }
      bool search_this = true;
      for( std::map< Node, unsigned >::iterator itc = cop_to_strat.begin(); itc != cop_to_strat.end(); ++itc ){
        if( itc->second==strat_CONCAT || ( itc->second==strat_ID && dt.getNumConstructors()==1 ) ){
          search_this = false;
          break;
        }
      }
      Trace("sygus-unif-debug2") << "...this register..." << std::endl;
      registerEnumerator( ee, e, tn, enum_role, search_this );
      
      if( cop_to_child_types.empty() ){
        Trace("sygus-unif") << "...consider " << dt.getName() << " a basic type" << std::endl;
      }else{
        for( std::map< Node, std::vector< TypeNode > >::iterator itct = cop_to_child_types.begin(); itct != cop_to_child_types.end(); ++itct ){
          Node cop = itct->first;
          Assert( cop_to_strat.find( cop )!=cop_to_strat.end() );
          unsigned strat = cop_to_strat[cop];
          d_cinfo[e].d_tinfo[tn].d_strat[cop].d_this = strat;
          Trace("sygus-unif-debug") << "Process strategy for operator : " << cop << " : ";
          print_strat("sygus-unif-debug", strat );
          Trace("sygus-unif-debug") << std::endl;

          for( unsigned j=0; j<itct->second.size(); j++ ){
            //calculate if we should allocate a new enumerator : should be true if we have a new role
            unsigned enum_role_c = enum_role;
            if( strat==strat_ITE ){
              if( j==0 ){
                enum_role_c = enum_ite_condition;
              }else{
                // role is the same as parent
              }
            }else if( strat==strat_CONCAT ){
              enum_role_c = enum_concat_term;
            }else if( strat==strat_ID ){
              // role is the same as parent
            }
            
            // register the child type
            TypeNode ct = itct->second[j];
            d_cinfo[e].d_tinfo[tn].d_strat[cop].d_csol_cts.push_back( ct );
            
            // make the enumerator
            Node et;
            if( cop_to_child_templ[cop].find( j )!=cop_to_child_templ[cop].end() ){
              // it is templated, allocate a fresh variable
              et = NodeManager::currentNM()->mkSkolem( "et", ct );
              Trace("sygus-unif-debug") << "...enumerate " << et << " of type " << ((DatatypeType)ct.toType()).getDatatype().getName();
              Trace("sygus-unif-debug") << " for arg " << j << " of " << ((DatatypeType)tn.toType()).getDatatype().getName() << std::endl;
              registerEnumerator( et, e, ct, enum_role_c, true );
              d_einfo[et].d_template = cop_to_child_templ[cop][j];
              d_einfo[et].d_template_arg = cop_to_child_templ_arg[cop][j];
              Assert( !d_einfo[et].d_template.isNull() );
              Assert( !d_einfo[et].d_template_arg.isNull() );
            }else{
              Trace("sygus-unif-debug") << "...child type enumerate " << ((DatatypeType)ct.toType()).getDatatype().getName() << ", role = ";
              print_role( "sygus-unif-debug", enum_role_c );
              Trace("sygus-unif-debug") << std::endl;
              collectEnumeratorTypes( e, ct, enum_role_c );
              // otherwise use the previous
              Assert( d_cinfo[e].d_tinfo[ct].d_enum.find( enum_role_c )!=d_cinfo[e].d_tinfo[ct].d_enum.end() );
              et = d_cinfo[e].d_tinfo[ct].d_enum[enum_role_c];
            }
            Trace("sygus-unif-debug") << "Register child enumerator " << et << ", arg " << j << " of " << cop << ", role = ";
            print_role( "sygus-unif-debug", enum_role_c );
            Trace("sygus-unif-debug") << std::endl;
            Assert( !et.isNull() );
            d_cinfo[e].d_tinfo[tn].d_strat[cop].d_cenum.push_back( et );
          }
          Trace("sygus-unif") << "Initialized strategy ";
          print_strat( "sygus-unif", strat );
          Trace("sygus-unif") << " for " << ((DatatypeType)tn.toType()).getDatatype().getName() << ", operator " << cop;
          Trace("sygus-unif") << ", #children = " << d_cinfo[e].d_tinfo[tn].d_strat[cop].d_cenum.size() << std::endl;
          Assert( d_cinfo[e].d_tinfo[tn].d_strat[cop].d_cenum.size()==d_cinfo[e].d_tinfo[tn].d_strat[cop].d_csol_cts.size() );
        }
      }
    }else{
      Trace("sygus-unif-debug") << "...this register (non-io)" << std::endl;
      registerEnumerator( ee, e, tn, enum_role, true );
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
      Trace("sygus-unif") << "  " << es << ", role = ";
      print_role("sygus-unif", itns->second.getRole());
      Trace("sygus-unif") << std::endl;
    }
  }
  Trace("sygus-unif") << std::endl;
  Trace("sygus-unif") << "Strategy for candidate " << c << " is : " << std::endl;
  std::map< Node, bool > visited;
  std::vector< Node > redundant;
  staticLearnRedundantOps( c, d_cinfo[c].getRootEnumerator(), visited, redundant, lemmas, 0 );
  for( unsigned i=0; i<lemmas.size(); i++ ){  
    Trace("sygus-unif") << "...can exclude based on  : " << lemmas[i] << std::endl;
  }
}

void CegConjecturePbe::staticLearnRedundantOps( Node c, Node e, std::map< Node, bool >& visited, std::vector< Node >& redundant,
                                                std::vector< Node >& lemmas, int ind ) {

  std::map< Node, EnumInfo >::iterator itn = d_einfo.find( e );
  Assert( itn!=d_einfo.end() );                                    
  if( visited.find( e )==visited.end() ){
    visited[e] = true;

    indent("sygus-unif", ind);
    Trace("sygus-unif") << e << " : role : ";
    print_role("sygus-unif", itn->second.getRole());
    Trace("sygus-unif") << " : ";

    if( itn->second.isTemplated() ){
      Trace("sygus-unif") << "basic, templated : \\ " << itn->second.d_template_arg << ". " << itn->second.d_template << std::endl;
    }else{
      TypeNode etn = e.getType();
      std::map< TypeNode, EnumTypeInfo >::iterator itt = d_cinfo[c].d_tinfo.find( etn );
      Assert( itt!=d_cinfo[c].d_tinfo.end() );
      if( itt->second.d_strat.empty() ){
        Trace("sygus-unif") << "basic" << std::endl;
      }else{
        Trace("sygus-unif") << "compound" << std::endl;
        // various strategies 
        for( std::map< Node, EnumTypeInfoStrat >::iterator itts = itt->second.d_strat.begin(); itts!=itt->second.d_strat.end(); ++itts ){
          indent("sygus-unif", ind+1);
          Trace("sygus-unif") << "Strategy : ";
          unsigned strat = itts->second.d_this;
          print_strat("sygus-unif", strat);
          Trace("sygus-unif") << std::endl;
          for( unsigned i=0; i<itts->second.d_cenum.size(); i++ ){
            std::vector< Node > redundant_c;
            bool no_repeat_op = false;
            // do not repeat operators that the strategy uses
            if( itts->second.d_csol_cts[i]==etn ){
              if( strat==strat_ITE && i!=0 ){
                no_repeat_op = true;
              }else if( strat==strat_CONCAT || strat==strat_ID ){
                no_repeat_op = true;
              }
            }
            if( no_repeat_op ){
              redundant_c.push_back( itts->first );
            }
            //do not use standard Boolean connectives in ITE conditions
            if( strat==strat_ITE && i==0 && itts->second.d_csol_cts[1]==itts->second.d_csol_cts[2] ){
              TypeNode ctn = itts->second.d_csol_cts[0];
              const Datatype& cdt = ((DatatypeType)ctn.toType()).getDatatype();
              for( unsigned j=0; j<cdt.getNumConstructors(); j++ ){
                Kind ck = d_tds->getConsNumKind( ctn, j );
                if( ck!=UNDEFINED_KIND && TermUtil::isBoolConnective( ck ) ){
                  bool typeCorrect = true;
                  for( unsigned k=0; k<cdt[j].getNumArgs(); k++ ){
                    if( d_tds->getArgType( cdt[j], k )!=ctn ){
                      typeCorrect = false;
                      break;
                    }
                  }
                  if( typeCorrect ){
                    Trace("sygus-unif-debug") << "Exclude Boolean connective in ITE conditional : " << ck << " in conditional type " << cdt.getName() << std::endl;
                    Node exc_cons = Node::fromExpr( cdt[j].getConstructor() );
                    if( std::find( redundant_c.begin(), redundant_c.end(), exc_cons )==redundant_c.end() ){
                      redundant_c.push_back( exc_cons );
                    }
                  }
                }
              }
            }
            // recurse
            staticLearnRedundantOps( c, itts->second.d_cenum[i], visited, redundant_c, lemmas, ind+2 );
          }
        }
      }
    }
  }else{
    indent("sygus-unif", ind);
    Trace("sygus-unif") << e << std::endl;
  }
  if( !redundant.empty() ){
    // TODO : if this becomes more general, must get master enumerator here
    if( itn->second.d_enum_slave.size()==1 ){
      for( unsigned i=0; i<redundant.size(); i++ ){
        int cindex = Datatype::indexOf( redundant[i].toExpr() );
        Assert( cindex!=-1 );
        const Datatype& dt = Datatype::datatypeOf( redundant[i].toExpr() );
        Node tst = datatypes::DatatypesRewriter::mkTester( e, cindex, dt ).negate();
        if( std::find( lemmas.begin(), lemmas.end(), tst )==lemmas.end() ){
          lemmas.push_back( tst );
        }
      }
    }
  }
}

// ------------------------------------------- solution construction from enumeration

void CegConjecturePbe::getCandidateList( std::vector< Node >& candidates, std::vector< Node >& clist ) {
  for( unsigned i=0; i<candidates.size(); i++ ){
    Node v = candidates[i];
    std::map< Node, CandidateInfo >::iterator it = d_cinfo.find( v );
    if( it!=d_cinfo.end() ){
      for( unsigned j=0; j<it->second.d_esym_list.size(); j++ ){
        Node e = it->second.d_esym_list[j];
        std::map< Node, EnumInfo >::iterator it = d_einfo.find( e );
        Assert( it != d_einfo.end() );
        if( getGuardStatus( it->second.d_active_guard )==1 ){
          clist.push_back( e );
        }
      }
    }
  }
}

bool CegConjecturePbe::constructCandidates( std::vector< Node >& enums, std::vector< Node >& enum_values, 
                                            std::vector< Node >& candidates, std::vector< Node >& candidate_values, 
                                            std::vector< Node >& lems ) {
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
  if( getGuardStatus( it->second.d_active_guard )==1 ){
    Assert( std::find( it->second.d_enum_vals.begin(), it->second.d_enum_vals.end(), v )==it->second.d_enum_vals.end() );
    Node c = it->second.d_parent_candidate;
    Node exp_exc;
    if( d_examples_out_invalid.find( c )==d_examples_out_invalid.end() ){
      std::map< Node, CandidateInfo >::iterator itc = d_cinfo.find( c );
      Assert( itc != d_cinfo.end() );      
      TypeNode xtn = x.getType();
      Node bv = d_tds->sygusToBuiltin( v, xtn );
      std::map< Node, std::vector< std::vector< Node > > >::iterator itx = d_examples.find( c );
      std::map< Node, std::vector< Node > >::iterator itxo = d_examples_out.find( c );
      Assert( itx!=d_examples.end() );
      Assert( itxo!=d_examples_out.end() );
      Assert( itx->second.size()==itxo->second.size() );
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
        for( unsigned j=0; j<itx->second.size(); j++ ){
          Node res = d_tds->evaluateBuiltin( xtn, bv, itx->second[j] );
          Trace("sygus-pbe-enum-debug") << "...got res = " << res << " from " << bv << std::endl;
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
          if( cond_vals.find( d_true )!=cond_vals.end() || cond_vals.empty() ){  // latter is the degenerate case of no examples
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
          // is it excluded for domain-specific reason?
          std::vector< Node > exp_exc_vec;
          if( getExplanationForEnumeratorExclude( c, x, v, results, it->second, exp_exc_vec ) ){
            Assert( !exp_exc_vec.empty() );
            exp_exc = exp_exc_vec.size()==1 ? exp_exc_vec[0] : NodeManager::currentNM()->mkNode( kind::AND, exp_exc_vec );
            Trace("sygus-pbe-enum") << "  ...fail : term is excluded (domain-specific)" << std::endl;
          }else{
            //if( cond_vals.size()!=2 ){
            //  // must discriminate
            //  Trace("sygus-pbe-enum") << "  ...fail : conditional is constant." << std::endl;
            //  keep = false;
            //}
            // must be unique up to examples
            Node val = itv->second.d_term_trie.addCond( this, v, results, true );
            if( val==v ){
              Trace("sygus-pbe-enum") << "  ...success!   add to PBE pool : " << d_tds->sygusToBuiltin( v ) << std::endl;
              keep = true;
            }else{
              Trace("sygus-pbe-enum") << "  ...fail : term is not unique" << std::endl;
            }
            itc->second.d_cond_count++;
          }
        }
        if( keep ){
          // notify the parent to retry the build of PBE
          itc->second.d_check_sol = true;
          itv->second.addEnumValue( this, v, results );
          /*
          if( Trace.isOn("sygus-pbe-enum") ){
            if( itv->second.getRole()==enum_io ){
              if( !prevIsCover && itv->second.isFeasible() ){
                Trace("sygus-pbe-enum") << "...PBE : success : Evaluation of "
          << xs << " now covers all examples." << std::endl;
              }
            }
          }
          */
        }
      }
    }else{
      Trace("sygus-pbe-enum-debug") << "  ...examples do not have output." << std::endl;
    }
    //exclude this value on subsequent iterations
    Node g = it->second.d_active_guard;
    if( exp_exc.isNull() ){
      // if we did not already explain why this should be excluded, use default
      exp_exc = d_tds->getExplanationForConstantEquality( x, v );
    }
    Node exlem = NodeManager::currentNM()->mkNode( kind::OR, g.negate(), exp_exc.negate() );
    Trace("sygus-pbe-enum-lemma") << "CegConjecturePbe : enumeration exclude lemma : " << exlem << std::endl;
    lems.push_back( exlem );
  }else{
    Trace("sygus-pbe-enum-debug") << "  ...guard is inactive." << std::endl;
  }
}

/** NegContainsSygusInvarianceTest
*
* This class is used to construct a minimal shape of a term that cannot
* be contained in at least one output of an I/O pair.
*
* Say our PBE conjecture is:
*
* exists f.
*   f( "abc" ) = "abc abc" ^
*   f( "de" ) = "de de"
*
* Then, this class is used when there is a candidate solution t[x1] such that
* either
*   contains( "abc abc", t["abc"] ) ---> false or
*   contains( "de de", t["de"] ) ---> false
*
* In particular it is used to determine whether certain generalizations of t[x1]
* are still sufficient to falsify one of the above containments.
*
* For example:
*
* str.++( x1, "d" ) can be minimized to str.++( _, "d" )
*   ...since contains( "abc abc", str.++( y, "d" ) ) ---> false,
*      for any y.
* str.replace( "de", x1, "b" ) can be minimized to str.replace( "de", x1, _ )
*   ...since contains( "abc abc", str.replace( "de", "abc", y ) ) ---> false,
*      for any y.
*
* It is an instance of quantifiers::SygusInvarianceTest, which
* traverses the AST of a given term, replaces each subterm by a
* fresh variable y and checks whether an invariance test (such as
* the one specified by this class) holds.
*
*/
class NegContainsSygusInvarianceTest : public quantifiers::SygusInvarianceTest {
public:
  NegContainsSygusInvarianceTest() : d_cpbe(nullptr){}
  ~NegContainsSygusInvarianceTest(){}

  /** initialize this invariance test
  *  cpbe is the conjecture utility.
  *  e is the enumerator which we are reasoning about (associated with a synth
  *    fun).
  *  exo is the list of outputs of the PBE conjecture.
  *  ncind is the set of possible indices of the PBE conjecture to check
  *    invariance of non-containment.
  *    For example, in the above example, when t[x1] = "ab", then this
  *    has the index 1 since contains("de de", "ab") ---> false but not
  *    the index 0 since contains("abc abc","ab") ---> true.
  */
  void init(quantifiers::CegConjecturePbe* cpbe,
            Node e,
            std::vector<Node>& exo,
            std::vector<unsigned>& ncind)
  {
    if (cpbe->hasExamples(e))
    {
      Assert(cpbe->getNumExamples(e) == exo.size());
      d_enum = e;
      d_exo.insert( d_exo.end(), exo.begin(), exo.end() );
      d_neg_con_indices.insert( d_neg_con_indices.end(), ncind.begin(), ncind.end() );
      d_cpbe = cpbe;
    }
  }

 protected:
  /** checks whether contains( out_i, nvn[in_i] ) --> false for some I/O pair i.
   */
  bool invariant( quantifiers::TermDbSygus * tds, Node nvn, Node x ){
    if (!d_enum.isNull())
    {
      TypeNode tn = nvn.getType();
      Node nbv = tds->sygusToBuiltin( nvn, tn );
      Node nbvr = tds->extendedRewrite( nbv );
      // if for any of the examples, it is not contained, then we can exclude
      for( unsigned i=0; i<d_neg_con_indices.size(); i++ ){
        unsigned ii = d_neg_con_indices[i];
        Assert( ii<d_exo.size() );
        Node nbvre = d_cpbe->evaluateBuiltin(tn, nbvr, d_enum, ii);
        Node out = d_exo[ii];
        Node cont = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, out, nbvre );
        Node contr = Rewriter::rewrite( cont );
        if( contr==tds->d_false ){
          if( Trace.isOn("sygus-pbe-cterm") ){
            Trace("sygus-pbe-cterm") << "PBE-cterm : enumerator : do not consider ";
            Trace("sygus-pbe-cterm") << nbv << " for any " << tds->sygusToBuiltin( x ) << " since " << std::endl;
            Trace("sygus-pbe-cterm") << "   PBE-cterm :    for input example : ";
            std::vector< Node > ex;
            d_cpbe->getExample(d_enum, ii, ex);
            for( unsigned j=0; j<ex.size(); j++ ){
              Trace("sygus-pbe-cterm") << ex[j] << " ";
            }
            Trace("sygus-pbe-cterm") << std::endl;
            Trace("sygus-pbe-cterm") << "   PBE-cterm :     this rewrites to : " << nbvre << std::endl;
            Trace("sygus-pbe-cterm") << "   PBE-cterm : and is not in output : " << out << std::endl;
          }
          return true;
        }
      }
    }
    return false;
  }

 private:
  /** The enumerator whose value we are considering in this invariance test */
  Node d_enum;
  /** The output examples for the enumerator */
  std::vector<Node> d_exo;
  /** The set of I/O pair indices i such that
   *    contains( out_i, nvn[in_i] ) ---> false
   */
  std::vector<unsigned> d_neg_con_indices;
  /** reference to the PBE utility */
  quantifiers::CegConjecturePbe* d_cpbe;
};


bool CegConjecturePbe::getExplanationForEnumeratorExclude( Node c, Node x, Node v, std::vector< Node >& results, EnumInfo& ei, std::vector< Node >& exp ) {
  if( ei.d_enum_slave.size()==1 ){
    // this check whether the example evaluates to something that is larger than the output
    //  if so, then this term is never useful when using a concatenation strategy
    if (ei.getRole() == enum_concat_term)
    {
      if( Trace.isOn("sygus-pbe-cterm-debug") ){
        Trace("sygus-pbe-enum") << std::endl;
      }

      // check if all examples had longer length that the output
      std::map< Node, std::vector< Node > >::iterator itxo = d_examples_out.find( c );
      Assert( itxo!=d_examples_out.end() );
      Assert( itxo->second.size()==results.size() );
      Trace("sygus-pbe-cterm-debug") << "Check enumerator exclusion for " << x << " -> " << d_tds->sygusToBuiltin( v ) << " based on containment." << std::endl;
      std::vector< unsigned > cmp_indices;
      for( unsigned i=0; i<results.size(); i++ ){
        Assert( results[i].isConst() );
        Assert( itxo->second[i].isConst() );
        /*
        unsigned vlen = results[i].getConst<String>().size();
        unsigned xlen = itxo->second[i].getConst<String>().size();
        Trace("sygus-pbe-cterm-debug") << "  " << results[i] << " <> " << itxo->second[i];
        int index = vlen>xlen ? 1 : ( vlen<xlen ? -1 : 0 );
        Trace("sygus-pbe-cterm-debug") << "..." << index << std::endl;
        cmp_indices[index].push_back( i );
        */
        Trace("sygus-pbe-cterm-debug") << "  " << results[i] << " <> " << itxo->second[i];
        Node cont = NodeManager::currentNM()->mkNode( kind::STRING_STRCTN, itxo->second[i], results[i] );
        Node contr = Rewriter::rewrite( cont );
        if( contr==d_false ){
          cmp_indices.push_back( i );
          Trace("sygus-pbe-cterm-debug") << "...not contained." << std::endl;
        }else{
          Trace("sygus-pbe-cterm-debug") << "...contained." << std::endl;
        }
      }
      // TODO : stronger requirement if we incorporate ITE + CONCAT mixed strategy : must be longer than *all* examples
      if( !cmp_indices.empty() ){
        //set up the inclusion set
        NegContainsSygusInvarianceTest ncset;
        ncset.init(this, x, itxo->second, cmp_indices);
        d_tds->getExplanationFor( x, v, exp, ncset );
        Trace("sygus-pbe-cterm") << "PBE-cterm : enumerator exclude " << d_tds->sygusToBuiltin( v ) << " due to negative containment." << std::endl;
        return true;
      }
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
  std::map< unsigned, Node >::iterator it = d_tinfo[d_root].d_enum.find( enum_io );
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
        Node vcc = constructSolution( c, e, x, 1 );
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
  double r = (double)(rand())/((double)(RAND_MAX));
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
  // TODO
  double r = (double)(rand())/((double)(RAND_MAX));
  unsigned cindex = r*strs.size();
  if( cindex>strs.size() ){
    cindex = strs.size() - 1;
  }
  return strs[cindex];
}                         
                                    
Node CegConjecturePbe::constructSolution( Node c, Node e, UnifContext& x, int ind ) {
  indent("sygus-pbe-dt-debug", ind);
  Trace("sygus-pbe-dt-debug") << "ConstructPBE: enum: " << e << " in context ";
  print_val("sygus-pbe-dt-debug", x.d_vals);
  Trace("sygus-pbe-dt-debug") << std::endl;
  std::map< Node, EnumInfo >::iterator itn = d_einfo.find( e );
  Assert( itn!=d_einfo.end() );
  Node ret_dt;
  if (itn->second.getRole() == enum_any)
  {
    indent("sygus-pbe-dt", ind);
    ret_dt = constructBestSolvedTerm( itn->second.d_enum_vals, x );
    Trace("sygus-pbe-dt") << "return PBE: success : use any " << d_tds->sygusToBuiltin( ret_dt ) << std::endl;
    Assert( !ret_dt.isNull() );
  }
  else if (itn->second.getRole() == enum_io && !x.isReturnValueModified()
           && itn->second.isSolved())
  {
    // this type has a complete solution
    ret_dt = itn->second.getSolved();
    indent("sygus-pbe-dt", ind);
    Trace("sygus-pbe-dt") << "return PBE: success : solved " << d_tds->sygusToBuiltin( ret_dt ) << std::endl;
    Assert( !ret_dt.isNull() );
  }else{
    TypeNode etn = e.getType();
    std::map< TypeNode, EnumTypeInfo >::iterator itt = d_cinfo[c].d_tinfo.find( etn );
    Assert( itt!=d_cinfo[c].d_tinfo.end() );
    if( d_tds->sygusToBuiltinType( e.getType() ).isString() ){
      // check if a current value that closes all examples
      
      // get the term enumerator for this type
      bool success = true;
      std::map< Node, EnumInfo >::iterator itet;
      if (itn->second.getRole() == enum_concat_term)
      {
        itet = itn;
      }else{
        std::map< unsigned, Node >::iterator itnt = itt->second.d_enum.find( enum_concat_term );
        if( itnt != itt->second.d_enum.end() ){
          Node et = itnt->second;
          itet = d_einfo.find( et );
        }else{
          success = false;
        }
      }
      if( success ){
        Assert( itet!=d_einfo.end() );

        // get the current examples
        std::map< Node, std::vector< Node > >::iterator itx = d_examples_out.find( c );
        Assert( itx!=d_examples_out.end() );
        std::vector< CVC4::String > ex_vals;
        x.getCurrentStrings( this, itx->second, ex_vals );
        Assert( itn->second.d_enum_vals.size()==itn->second.d_enum_vals_res.size() );
        
        // test each example in the term enumerator for the type
        std::vector< Node > str_solved;
        for( unsigned i=0; i<itet->second.d_enum_vals.size(); i++ ){
          if( x.isStringSolved( this, ex_vals, itet->second.d_enum_vals_res[i] ) ){
            str_solved.push_back( itet->second.d_enum_vals[i] );
          }
        }
        if( !str_solved.empty() ){
          ret_dt = constructBestStringSolvedTerm( str_solved, x );
          indent("sygus-pbe-dt", ind);
          Trace("sygus-pbe-dt") << "return PBE: success : string solved " << d_tds->sygusToBuiltin( ret_dt ) << std::endl;
        }else{
          indent("sygus-pbe-dt-debug", ind);
          Trace("sygus-pbe-dt-debug") << "  ...not currently string solved." << std::endl;
        }
      }
    }
    else if (itn->second.getRole() == enum_io && !x.isReturnValueModified())
    {
      // it has an enumerated value that is conditionally correct under the current assumptions
      std::vector< Node > subsumed_by;
      itn->second.d_term_trie.getSubsumedBy( this, x.d_vals, true, subsumed_by );
      if( !subsumed_by.empty() ){
        ret_dt = constructBestSolvedTerm( subsumed_by, x );
        indent("sygus-pbe-dt", ind);
        Trace("sygus-pbe-dt") << "return PBE: success : conditionally solved" << d_tds->sygusToBuiltin( ret_dt ) << std::endl;
      }else{
        indent("sygus-pbe-dt-debug", ind);
        Trace("sygus-pbe-dt-debug") << "  ...not currently conditionally solved." << std::endl;
      }
    }
    if( ret_dt.isNull() ){
      if( !itn->second.isTemplated() ){
        // try to construct a compound solution, if strategies are available
        
        // do various strategies 
        for( std::map< Node, EnumTypeInfoStrat >::iterator itts = itt->second.d_strat.begin(); itts!=itt->second.d_strat.end(); ++itts ){
          std::map< unsigned, Node > dt_children_cons;
          unsigned strat = itts->second.d_this;
          
          bool success = true;
          
          // for ITE
          std::map< unsigned, Node > look_ahead_solved_children;
          Node split_cond_enum;
          int split_cond_res_index = -1;
          
          //for CONCAT
          Node incr_val;
          int incr_type = 0;
          std::map< Node, std::vector< unsigned > > incr;

          // construct the child order based on heuristics
          std::vector< unsigned > corder;
          std::unordered_set<unsigned> cused;
          if( strat==strat_CONCAT ){
            for( unsigned r=0; r<2; r++ ){
              // Concatenate strategy can only be applied from the endpoints.
              // This chooses the appropriate endpoint for which we stay within
              // the same SyGuS type.
              // In other words, if we are synthesizing based on a production
              // rule ( T -> str.++( T1, ..., Tn ) ), then we
              // prefer recursing on the 1st argument of the concat if T1 = T,
              // and the last argument if Tn = T.
              unsigned sc = r==0 ? 0 : itts->second.d_cenum.size()-1;
              Node ce = itts->second.d_cenum[sc];
              if( ce.getType()==etn ){
                // prefer simple recursion (self type)
                Assert( d_einfo.find( ce )!=d_einfo.end() );
                Assert(d_einfo[ce].getRole() == enum_concat_term);
                corder.push_back( sc );
                cused.insert(sc);
                break;
              }
            }
          }
          // fill remaining children for which there is no preference
          for (unsigned sc = 0; sc < itts->second.d_cenum.size(); sc++)
          {
            if (cused.find(sc) == cused.end())
            {
              corder.push_back( sc );
            }
          }
          Assert( corder.size()==itts->second.d_cenum.size() );
            
            
          for( unsigned scc=0; scc<corder.size(); scc++ ){
            unsigned sc = corder[scc];
            Node rec_c;
            indent("sygus-pbe-dt", ind);
            Trace("sygus-pbe-dt") << "construct PBE child #" << sc << "..." << std::endl;
            std::map< unsigned, Node >::iterator itla = look_ahead_solved_children.find( sc );
            if( itla!=look_ahead_solved_children.end() ){
              rec_c = itla->second;
              indent("sygus-pbe-dt-debug", ind+1);
              Trace("sygus-pbe-dt-debug") << "ConstructPBE: look ahead solved : " << d_tds->sygusToBuiltin( rec_c ) << std::endl;
            }else{
              // get the child enumerator
              Node ce = itts->second.d_cenum[sc];
              if( strat==strat_ITE && scc==0 ){
                Assert( itts->second.d_cenum.size()==3 ); // for now, fix to 3 child ITEs
                // choose a condition
                
                // register the condition enumerator
                std::map< Node, EnumInfo >::iterator itnc = d_einfo.find( ce );
                Assert( itnc!=d_einfo.end() );
                // only used if the return value is not modified
                if( !x.isReturnValueModified() ){
                  if( x.d_uinfo.find( ce )==x.d_uinfo.end() ){
                    Trace("sygus-pbe-dt-debug2") << "  reg : PBE: Look for direct solutions for conditional enumerator " << ce << " ... " << std::endl;
                    x.d_uinfo[ce].d_status = 0;
                    Assert( itnc->second.d_enum_vals.size()==itnc->second.d_enum_vals_res.size() );
                    for( unsigned i=1; i<=2; i++ ){
                      Node te = itts->second.d_cenum[i];
                      std::map< Node, EnumInfo >::iterator itnt = d_einfo.find( te );
                      Assert( itnt!=d_einfo.end() );
                      bool branch_pol = ( i==1 );
                      // for each condition, get terms that satisfy it in this branch
                      for( unsigned k=0; k<itnc->second.d_enum_vals.size(); k++ ){
                        Node cond = itnc->second.d_enum_vals[k];
                        std::vector< Node > solved;
                        itnt->second.d_term_trie.getSubsumedBy( this, itnc->second.d_enum_vals_res[k], branch_pol, solved );
                        Trace("sygus-pbe-dt-debug2") << "  reg : PBE: " << d_tds->sygusToBuiltin( cond ) << " has " << solved.size() << " solutions in branch " << i << std::endl;
                        if( !solved.empty() ){
                          Node slv = constructBestSolvedTerm( solved, x );
                          Trace("sygus-pbe-dt-debug") << "  reg : PBE: ..." << d_tds->sygusToBuiltin( slv ) << " is a solution under branch " << i;
                          Trace("sygus-pbe-dt-debug") << " of condition " << d_tds->sygusToBuiltin( cond ) << std::endl;
                          x.d_uinfo[ce].d_look_ahead_sols[cond][i] = slv;
                        }
                      }
                    }
                  }
                }
                
                // get the conditionals in the current context : they must be distinguishable
                std::map< int, std::vector< Node > > possible_cond;
                std::map< Node, int > solved_cond;  //stores branch
                itnc->second.d_term_trie.getLeaves( this, x.d_vals, true, possible_cond );
                
                std::map< int, std::vector< Node > >::iterator itpc = possible_cond.find( 0 );
                if( itpc!=possible_cond.end() ){
                  indent("sygus-pbe-dt-debug", ind);
                  Trace("sygus-pbe-dt-debug") << "PBE : We have " << itpc->second.size() << " distinguishable conditionals:" << std::endl;       
                  for( unsigned k=0; k<itpc->second.size(); k++ ){                  
                    indent("sygus-pbe-dt-debug", ind+1);
                    Trace("sygus-pbe-dt-debug") << d_tds->sygusToBuiltin( itpc->second[k] ) << std::endl;
                  }   
                  
                
                  // static look ahead conditional : choose conditionals that have solved terms in at least one branch
                  //    only applicable if we have not modified the return value
                  std::map< int, std::vector< Node > > solved_cond;
                  if( !x.isReturnValueModified() ){
                    Assert( x.d_uinfo.find( ce )!=x.d_uinfo.end() );
                    int solve_max = 0;
                    for( unsigned k=0; k<itpc->second.size(); k++ ){
                      Node cond = itpc->second[k];
                      std::map< Node, std::map< unsigned, Node > >::iterator itla = x.d_uinfo[ce].d_look_ahead_sols.find( cond );
                      if( itla!=x.d_uinfo[ce].d_look_ahead_sols.end() ){
                        int nsolved = itla->second.size();
                        solve_max = nsolved > solve_max ? nsolved : solve_max;
                        solved_cond[nsolved].push_back( cond );
                      }
                    }
                    int n = solve_max;
                    while( n>0 ){
                      if( !solved_cond[n].empty() ){
                        rec_c = constructBestSolvedConditional( solved_cond[n], x );
                        indent("sygus-pbe-dt", ind);
                        Trace("sygus-pbe-dt") << "PBE: ITE strategy : choose solved conditional " << d_tds->sygusToBuiltin( rec_c ) << " with " << n << " solved children..." << std::endl;
                        std::map< Node, std::map< unsigned, Node > >::iterator itla = x.d_uinfo[ce].d_look_ahead_sols.find( rec_c );
                        Assert( itla!=x.d_uinfo[ce].d_look_ahead_sols.end() );
                        for( std::map< unsigned, Node >::iterator itla2 = itla->second.begin(); itla2 != itla->second.end(); ++itla2 ){
                          look_ahead_solved_children[ itla2->first ] = itla2->second;
                        }
                        break;
                      }
                      n--;
                    }
                  }
                  
                  // dynamic look ahead conditional : compute if there are any solved terms in this branch  TODO
                  if( ind>0 ){
                    
                  }
                  
                  // otherwise, guess a conditional
                  if( rec_c.isNull() ){
                    rec_c = constructBestConditional( itpc->second, x );
                    Assert( !rec_c.isNull() );
                    indent("sygus-pbe-dt", ind);
                    Trace("sygus-pbe-dt") << "PBE: ITE strategy : choose random conditional " << d_tds->sygusToBuiltin( rec_c ) << std::endl;
                  }
                }else{
                  // TODO : degenerate case where children have different types
                  indent("sygus-pbe-dt", ind);
                  Trace("sygus-pbe-dt") << "return PBE: failed ITE strategy, cannot find a distinguishable condition" << std::endl;
                }
                if( !rec_c.isNull() ){
                  Assert( itnc->second.d_enum_val_to_index.find( rec_c )!=itnc->second.d_enum_val_to_index.end() );
                  split_cond_res_index = itnc->second.d_enum_val_to_index[rec_c];
                  split_cond_enum = ce;
                  Assert( split_cond_res_index>=0 );
                  Assert( split_cond_res_index<(int)itnc->second.d_enum_vals_res.size() );
                }
              }else if( strat==strat_CONCAT && scc==0 ){
                std::map< Node, EnumInfo >::iterator itsc = d_einfo.find( ce );
                Assert( itsc!=d_einfo.end() );
                // ensured by the child order we set above
                Assert(itsc->second.getRole() == enum_concat_term);
                // check if each return value is a prefix/suffix of all open examples
                incr_type = sc==0 ? -1 : 1;
                if( x.d_has_string_pos==0 || x.d_has_string_pos==incr_type ){
                  bool isPrefix = incr_type==-1;
                  std::map< Node, unsigned > total_inc;
                  std::vector< Node > inc_strs;
                  std::map< Node, std::vector< Node > >::iterator itx = d_examples_out.find( c );
                  Assert( itx!=d_examples_out.end() );
                  // make the value of the examples
                  std::vector< CVC4::String > ex_vals;
                  x.getCurrentStrings( this, itx->second, ex_vals );

                  // check if there is a value for which is a prefix/suffix of all active examples
                  Assert( itsc->second.d_enum_vals.size()==itsc->second.d_enum_vals_res.size() );
                  
                  for( unsigned i=0; i<itsc->second.d_enum_vals.size(); i++ ){
                    Node val_t = itsc->second.d_enum_vals[i];
                    indent("sygus-pbe-dt-debug", ind);
                    Trace("sygus-pbe-dt-debug") << "increment string values : " << val_t << " : ";
                    Assert( itsc->second.d_enum_vals_res[i].size()==itx->second.size() );
                    unsigned tot = 0;
                    bool exsuccess = x.getStringIncrement( this, isPrefix, ex_vals, itsc->second.d_enum_vals_res[i], incr[val_t], tot );
                    if( tot==0 ){
                      exsuccess = false;
                    }
                    if( !exsuccess ){
                      incr.erase( val_t );
                      Trace("sygus-pbe-dt-debug") << "...fail" << std::endl;
                    }else{
                      total_inc[ val_t ] = tot;
                      inc_strs.push_back( val_t );
                      Trace("sygus-pbe-dt-debug") << "...success, total increment = " << tot << std::endl;
                    }
                  }

                  if( !incr.empty() ){
                    rec_c = constructBestStringToConcat( inc_strs, total_inc, incr, x );
                    incr_val = rec_c;
                    Assert( !rec_c.isNull() );
                    indent("sygus-pbe-dt", ind);
                    Trace("sygus-pbe-dt") << "PBE: CONCAT strategy : choose " << ( isPrefix ? "pre" : "suf" ) << "fix value " << d_tds->sygusToBuiltin( rec_c ) << std::endl;
                  }else{
                    indent("sygus-pbe-dt", ind);
                    Trace("sygus-pbe-dt") << "PBE: failed CONCAT strategy, no values are " << ( isPrefix ? "pre" : "suf" ) << "fix of all examples." << std::endl;
                  }
                }else{
                  indent("sygus-pbe-dt", ind);
                  Trace("sygus-pbe-dt") << "PBE: failed CONCAT strategy, prefix/suffix mismatch." << std::endl;
                }
              }else{
                // a standard term
                
                // store previous values
                std::vector< Node > prev;
                std::vector< unsigned > prev_str_pos;
                int prev_has_str_pos = false;
                // update the context
                bool ret = false;
                if( strat==strat_ITE ){
                  std::map< Node, EnumInfo >::iterator itnc = d_einfo.find( split_cond_enum );
                  Assert( itnc!=d_einfo.end() );
                  Assert( split_cond_res_index>=0 );
                  Assert( split_cond_res_index<(int)itnc->second.d_enum_vals_res.size() );
                  prev = x.d_vals;
                  ret = x.updateContext( this, itnc->second.d_enum_vals_res[split_cond_res_index], sc==1 );
                }else if( strat==strat_CONCAT ){
                  prev_str_pos = x.d_str_pos;
                  prev_has_str_pos = x.d_has_string_pos;
                  Assert( incr.find( incr_val )!=incr.end() );
                  ret = x.updateStringPosition( this, incr[incr_val] );
                  x.d_has_string_pos = incr_type;
                }else if( strat==strat_ID ){
                  ret = true;
                }
                // must have updated the context
                AlwaysAssert( ret );
                // recurse
                rec_c = constructSolution( c, ce, x, ind+1 );
                if( !rec_c.isNull() ){
                  //revert context
                  if( strat==strat_ITE ){
                    x.d_vals = prev;
                  }else if( strat==strat_CONCAT ){
                    x.d_str_pos = prev_str_pos;
                    x.d_has_string_pos = prev_has_str_pos;
                  }
                }
              }
            }
            if( !rec_c.isNull() ){
              dt_children_cons[sc] = rec_c;
            }else{
              success = false;
              break;
            }
          }
          if( success ){
            std::vector< Node > dt_children;
            Assert( !itts->first.isNull() );
            dt_children.push_back( itts->first );
            for( unsigned sc=0; sc<itts->second.d_cenum.size(); sc++ ){
              std::map< unsigned, Node >::iterator itdc = dt_children_cons.find( sc );
              Assert( itdc!=dt_children_cons.end() );
              dt_children.push_back( itdc->second );
            }         
            ret_dt = NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, dt_children );
            indent("sygus-pbe-dt-debug", ind);
            Trace("sygus-pbe-dt-debug") << "PBE: success : constructed for strategy ";
            print_strat( "sygus-pbe-dt-debug", strat );
            Trace("sygus-pbe-dt-debug") << std::endl;
            break;
          }else{
            indent("sygus-pbe-dt-debug", ind);
            Trace("sygus-pbe-dt-debug") << "PBE: failed for strategy ";
            print_strat( "sygus-pbe-dt-debug", strat );
            Trace("sygus-pbe-dt-debug") << std::endl;
          }
        }
        if( ret_dt.isNull() ){
          indent("sygus-pbe-dt", ind);
          Trace("sygus-pbe-dt") << "return PBE: fail : all strategies failed " << std::endl;
        }
      }else{
        indent("sygus-pbe-dt", ind);
        Trace("sygus-pbe-dt") << "return PBE: fail : non-basic" << std::endl;
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
  return changed;
}

bool CegConjecturePbe::UnifContext::isReturnValueModified() {
  if( d_has_string_pos!=0 ){
    return true;
  }
  return false;
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
}


void CegConjecturePbe::UnifContext::getCurrentStrings( CegConjecturePbe * pbe, std::vector< Node >& vals, std::vector< CVC4::String >& ex_vals ) {
  bool isPrefix = d_has_string_pos==-1;
  CVC4::String dummy;
  for( unsigned i=0; i<vals.size(); i++ ){
    if( d_vals[i]==pbe->d_true ){
      Assert( vals[i].isConst() );
      unsigned pos_value = d_str_pos[i];
      if( pos_value>0 ){
        Assert( d_has_string_pos!=0 );
        CVC4::String s = vals[i].getConst<String>();
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

bool CegConjecturePbe::UnifContext::getStringIncrement( CegConjecturePbe * pbe, bool isPrefix, std::vector< CVC4::String >& ex_vals, std::vector< Node >& vals, std::vector< unsigned >& inc, unsigned& tot ) {
  for( unsigned j=0; j<vals.size(); j++ ){
    unsigned ival = 0;
    if( d_vals[j]==pbe->d_true ){
      // example is active in this context
      Assert( vals[j].isConst() );
      CVC4::String mystr = vals[j].getConst<String>();
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
bool CegConjecturePbe::UnifContext::isStringSolved( CegConjecturePbe * pbe, std::vector< CVC4::String >& ex_vals, std::vector< Node >& vals ) {
  for( unsigned j=0; j<vals.size(); j++ ){
    if( d_vals[j]==pbe->d_true ){
      // example is active in this context
      Assert( vals[j].isConst() );
      CVC4::String mystr = vals[j].getConst<String>();
      if( ex_vals[j]!=mystr ){
        return false;
      }
    }
  }
  return true;
}

int CegConjecturePbe::getGuardStatus( Node g ) {
  bool value;
  if( d_qe->getValuation().hasSatValue( g, value ) ) {
    if( value ){
      return 1;
    }else{
      return -1;
    }
  }else{
    return 0;
  }
}

}
