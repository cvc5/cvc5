/*********************                                                        */
/*! \file sygus_process_conj.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of techniqures for static preprocessing and analysis
 ** of sygus conjectures.
 **/
#include "theory/quantifiers/sygus_process_conj.h"

#include <stack>

#include "expr/datatype.h"
#include "theory/quantifiers/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegConjectureProcessArg * CegConjectureProcessArg::getParent() {
  if( d_parent!=nullptr ){
    CegConjectureProcessArg * p = d_parent->getParent();
    d_parent = p;
    return p;
  }
  return this;
}

void CegConjectureProcessFun::init(Node f) {
  d_synth_fun = f;
  Assert(f.getType().isFunction());
  d_deq_id_counter = 0;
  d_deq_id_eqc.clear();
  
  // initialize the arguments
  std::unordered_map<TypeNode, unsigned, TypeNodeHashFunction> type_to_init_deq_id;
  std::vector<Type> argTypes = static_cast<FunctionType>(f.getType().toType()).getArgTypes();
  for( unsigned j=0; j<argTypes.size(); j++ ){
    d_arg_props.push_back(CegConjectureProcessArg());
    // assign the disequality ids to the argument position
    // initially, all variables of the same type have the same deq id
    TypeNode atn = TypeNode::fromType( argTypes[j] );
    std::unordered_map<TypeNode, unsigned, TypeNodeHashFunction>::iterator it = type_to_init_deq_id.find(atn);
    unsigned deqid;
    if(it==type_to_init_deq_id.end()){
      deqid = allocateDeqId();
      type_to_init_deq_id[atn] = deqid;
    }else{
      deqid = it->second;
    }
    d_arg_props[j].d_deq_id = deqid;
    // add to deq id equivalence class
    d_deq_id_eqc[deqid].insert( j );
  }
}

unsigned CegConjectureProcessFun::allocateDeqId() {
  unsigned deqid = d_deq_id_counter;
  d_deq_id_counter++;
  d_deq_id_eqc.push_back(std::unordered_set< unsigned >());
  return deqid;
}

void CegConjectureProcessFun::processTerms(std::vector< Node >& ns, std::vector< Node >& ks, Node nf,
                                           std::unordered_set< Node, NodeHashFunction >& synth_fv, 
                                           std::unordered_map<Node, std::unordered_set< Node, NodeHashFunction >, NodeHashFunction >& free_vars) {
  Assert( ns.size()==ks.size() );
  Trace("sygus-process-arg-deps") << "Process " << ns.size() << " applications of " << d_synth_fun << "..." << std::endl;
  
  // update constant argument information
  for(unsigned index=0; index<ns.size(); index++ ){
    Node n = ns[index];
    Trace("sygus-process-arg-deps") << "  process constant argument information for application #" << index << ": " << n << std::endl;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      Node arg = n[i];
      if( d_arg_props[i].d_set_const_arg ){
        if( !d_arg_props[i].d_const_arg.isNull() && arg!=d_arg_props[i].d_const_arg ){
          d_arg_props[i].d_const_arg = Node::null();
        }
      }else{
        d_arg_props[i].d_const_arg = arg;
      }
    }
  }
  
  
  // update the disequality ids
  for(unsigned index=0; index<ns.size(); index++ ){
    Node n = ns[index];
    Assert(n.getKind()==APPLY_UF);
    Assert(n.getOperator()==d_synth_fun);
    Trace("sygus-process-arg-deps") << "  process equivalence of arguments for application #" << index << ": " << n << std::endl;
    for( unsigned i=0; i<d_deq_id_counter; i++ ){
      if( d_deq_id_eqc[i].size()>1 ){
        // partition based on the content of arguments of n
        std::unordered_map< Node, std::vector< unsigned >, NodeHashFunction > term_to_args;
        for( std::unordered_set< unsigned >::iterator it = d_deq_id_eqc[i].begin(); it != d_deq_id_eqc[i].end(); ++it ){
          unsigned a = (*it);
          term_to_args[n[a]].push_back(a);
        }
        bool firstTime = true;
        for(std::unordered_map< Node, std::vector< unsigned >, NodeHashFunction >::iterator it = term_to_args.begin();
            it != term_to_args.end(); ++it ){
          if( firstTime ){
            // leave the first set in the original eqc
            firstTime = false;          
          }else{
            unsigned deqid = allocateDeqId();
            // move to new eqc and update
            for( unsigned j=0; j<it->second.size(); j++ ){
              unsigned am = it->second[j];
              d_deq_id_eqc[i].erase(am);
              d_deq_id_eqc[deqid].insert(am);
              Assert(d_arg_props[am].d_deq_id==i);
              d_arg_props[am].d_deq_id = deqid;
            }
          }
        }
      }
    }
  }

  // process the arguments of n
  
  // the relevant variables
  std::unordered_set< Node, NodeHashFunction > rlv_vars;
  Assert( free_vars.find(nf)!=free_vars.end());
  rlv_vars = free_vars[nf];
  
  // compute equivalence classes of arguments
  // where all arguments have disjoint variables
  std::unordered_map< Node, CegConjectureProcessArg *, NodeHashFunction > var_to_eqc;
  /*
  std::unordered_map< CegConjectureProcessArg *, std::unordered_set< Node, NodeHashFunction > > eqc_to_var;
  for( unsigned i=0; i<d_arg_props.size(); i++ ){
    CegConjectureProcessArg * ca = d_arg_props[i]->getParent();
    if( eqc_to_var.find(ca)==eqc_to_var.end() ){
      eqc_to_var[ca].clear();
    }
  }
  */
  
  // exists f. forall xy. ( f( 2*x ) mod 2 = 0 ^ f( y ) != f( y+1 ) )
  
  // exists f. forall . f( 1 ) = 0 ^ f( 2 ) = 1
  
  // exists P. forall x. P( x+1, x ) ^ ~P( x, x+1 )
  
  // f( t1, t2 ) = t
  // forall w. w = f( t1, t2 ) => ( w = t )
  // forall x1 x2 w. w = f( x1, x2 ) => ( ( x1 = t1 ^ x2 = t2 ) => w = t )
  // forall x1 x2 w. ( ( x1 = t1 ^ x2 = t2 ) => w = f( x1, x2 ) ) => w = t )
  
  // If FV( ti ) ^ FV( tj ) != empty
  // for some f( t1...tn ), then argument i is relevant iff argument j is.
  
  
  // exists f. forall xz. f(x,2*x) = t[x] ^  
  
  // only arguments that are not generalizations of others are relevant
  // exists f. forall x. C( f( x, t[x] ) )
  //    solved by f -> (\ xy s[x,y])
  //    also solved by f -> (\ xy s[x,t[x]])
    
  for(unsigned index=0; index<ns.size(); index++ ){
    Node n = ns[index];
    Trace("sygus-process-arg-deps") << "  process relevance for application #" << index << ": " << n << std::endl;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      CegConjectureProcessArg * ca = d_arg_props[i]->getParent();
      // get the free variables in n[i]
      std::unordered_map<Node, std::unordered_set< Node, NodeHashFunction >, NodeHashFunction >::iterator itf = free_vars.find( n[i] );
      Assert( itf != free_vars.end() );
      for( std::unordered_set< Node, NodeHashFunction >::iterator itfv = itf->second.begin(); itfv != itf->second.end(); ++itfv ){
        Assert( ca->d_parent==nullptr );
        // have we assigned this variable to an equivalence class?
        Node var = *itfv;
        std::unordered_map< Node, CegConjectureProcessArg *, NodeHashFunction >::iterator itfve = var_to_eqc.find( var );
        if( itfve==var_to_eqc.end() ){
          var_to_eqc[var] = ca;
          //eqc_to_var[ca].push_back( var );
        }else{
          if( ca!=itfve->second ){
            // merge the equivalence classes
            ca->d_parent = itfve->second;
            ca = itfve->second;
          }
        }
      }
    }
  }
  
    /*
    std::unordered_set< unsigned > new_rlv_args;
    for(unsigned index=0; index<ns.size(); index++ ){
      Node n = ns[index];
      Trace("sygus-process-arg-deps") << "  process relevance for application #" << index << ": " << n << std::endl;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        // if argument is currently irrelevant, check whether it remains irrelevant
        if( !d_arg_props[i].d_relevant && new_rlv_args.find(i)!=new_rlv_args.end()){
          Node nn = n[i];
          Trace("sygus-process-arg-deps") << "    argument #i (" << nn << ")";
          // it is a synth fun?
          if( nn.isVar() && synth_fv.find(nn)!=synth_fv.end() ){
            //is it relevant?
            if( rlv_vars.find(nn)!=rlv_vars.end() ){
              new_rlv_args.push_back(i);
              Trace("sygus-process-arg-deps") << " is a relevant variable." << std::endl;
            }else{
              Trace("sygus-process-arg-deps") << " is an irrelevant variable." << std::endl;
            }
          }else{
            // this can be more precise
            new_rlv_args.push_back(i);
            Trace("sygus-process-arg-deps") << " is a relevant term." << std::endl;
          }
        }
      }
    }
    */

}

CegConjectureProcess::CegConjectureProcess(QuantifiersEngine* qe) : d_qe(qe) {}
CegConjectureProcess::~CegConjectureProcess() {}

Node CegConjectureProcess::simplify(Node q)
{
  Trace("sygus-process") << "Simplify conjecture : " << q << std::endl;
  Assert(q.getKind()==FORALL);
  
  // initialize the information about each function to synthesize
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    Node f = q[0][i];
    if(f.getType().isFunction() ){
      d_sf_info[f].init( f );
    }
  }
  
  // get the base on the conjecture
  Node base = q[1];
  std::unordered_set< Node, NodeHashFunction > synth_fv;
  if (base.getKind() == NOT && base[0].getKind() == FORALL)
  {
    for( unsigned j=0; j<base[0][0].getNumChildren(); j++ ){
      synth_fv.insert(base[0][0][j]);
    }
    base = base[0][1];
  }
  std::vector< Node > conjuncts;
  getComponentVector( AND, base, conjuncts );
  
    // process the conjunctions
  for (unsigned i = 0; i < conjuncts.size(); i++)
  {
    processConjunct(conjuncts[i], synth_fv);
  }
  
  return q;
}

void CegConjectureProcess::initialize(Node n, std::vector<Node>& candidates)
{
  if (Trace.isOn("sygus-process"))
  {
    Trace("sygus-process") << "Process conjecture : " << n
                           << " with candidates: " << std::endl;
    for (unsigned i = 0; i < candidates.size(); i++)
    {
      Trace("sygus-process") << "  " << candidates[i] << std::endl;
    }
  }

}

void CegConjectureProcess::processConjunct(Node n, std::unordered_set< Node, NodeHashFunction >& synth_fv) {
  Trace("sygus-process-arg-deps") << "Process conjunct: " << std::endl;
  Trace("sygus-process-arg-deps") << "  " << n << std::endl;
  
  // first, flatten the conjunct 
  // make a copy of free variables since we may add new ones
  std::unordered_set< Node, NodeHashFunction > synth_fv_n = synth_fv;
  std::unordered_map<Node,Node,NodeHashFunction> defs;
  std::unordered_map<Node,std::vector<Node>,NodeHashFunction> fun_to_defs;
  Node nf = flatten(n,synth_fv_n,defs,fun_to_defs);
  
  
  Trace("sygus-process-arg-deps") << "Flattened to: " << std::endl;
  Trace("sygus-process-arg-deps") << "  " << nf << std::endl;
  
  // get free variables in nf
  std::unordered_map<Node, std::unordered_set< Node, NodeHashFunction >, NodeHashFunction > free_vars;
  getFreeVariables(nf,synth_fv_n,free_vars);
  // get free variables in each application
  for(std::unordered_map<Node,Node,NodeHashFunction>::iterator it = defs.begin(); it != defs.end(); ++it ){
    getFreeVariables(it->second,synth_fv_n,free_vars);
  }
  
  // process the applications of synthesis functions
  for(std::unordered_map<Node,std::vector<Node>,NodeHashFunction>::iterator it = fun_to_defs.begin(); it != fun_to_defs.end(); ++it ){
    Node f = it->first;
    Trace("sygus-process-arg-deps") << "Processing applications of " << f << " : " << std::endl;
    std::map<Node, CegConjectureProcessFun>::iterator its = d_sf_info.find(f);
    if(its!=d_sf_info.end()){
      std::vector< Node > ns;
      for( unsigned j=0; j<it->second.size(); j++ ){
        Node k = it->second[j];
        Assert( defs.find(k)!=defs.end() );
        ns.push_back( defs[k] );
      }
      its->second.processTerms(ns,it->second,nf,synth_fv_n,free_vars);
    }else{
      Assert( false );      
    }
  }
}

Node CegConjectureProcess::CegConjectureProcess::flatten(Node n, std::unordered_set< Node, NodeHashFunction >& synth_fv, 
                                                         std::unordered_map<Node,Node,NodeHashFunction>& defs, 
                                                         std::unordered_map<Node,std::vector<Node>,NodeHashFunction>& fun_to_defs) {
  std::unordered_map<Node, Node, NodeHashFunction> visited;
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it;
  std::stack<Node> visit;
  Node cur;
  visit.push(n);
  do {
    cur = visit.top();
    visit.pop();
    it = visited.find(cur);

    if (it == visited.end()) {
      visited[cur] = Node::null();
      visit.push(cur);
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push(cur[i]);
      }
    } else if (it->second.isNull()) {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        it = visited.find(cur[i]);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur[i] != it->second;
        children.push_back(it->second);
      }
      if (childChanged) {
        ret = NodeManager::currentNM()->mkNode(cur.getKind(), children);
      }
      // is it a function to synthesize?
      if( cur.getKind()==APPLY_UF ){
        Node f = cur.getOperator();
        std::map<Node, CegConjectureProcessFun>::iterator its = d_sf_info.find(f);
        if(its!=d_sf_info.end()){
          // if so, flatten
          Node k = NodeManager::currentNM()->mkBoundVar("vf",cur.getType());
          defs[k] = ret;
          fun_to_defs[f].push_back(k);
          ret = k;
          synth_fv.insert(k);
        }
      }
      //post-rewrite
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

void CegConjectureProcess::getFreeVariables(Node n, std::unordered_set< Node, NodeHashFunction >& synth_fv,
  std::unordered_map<Node, std::unordered_set< Node, NodeHashFunction >, NodeHashFunction >& free_vars ){

  // first must compute free variables in each subterm of n,
  // as well as contains_synth_fun
  std::unordered_map<Node, bool, NodeHashFunction> visited;
  std::unordered_map<Node, bool, NodeHashFunction>::iterator it;
  std::stack<Node> visit;
  Node cur;
  visit.push(n);
  do {
    cur = visit.top();
    visit.pop();
    it = visited.find(cur);

    if (it == visited.end()) {
      visited[cur] = false;
      visit.push(cur);
      for (unsigned i = 0; i < cur.getNumChildren(); i++) {
        visit.push(cur[i]);
      }
    }else if( !it->second ){
      if( synth_fv.find(cur)!=synth_fv.end() ){
        // it is a free variable
        free_vars[cur].insert(cur);
      }
      else
      {
        // otherwise, carry the free variables from the children
        for (unsigned i = 0; i < cur.getNumChildren(); i++) {
          free_vars[cur].insert(free_vars[cur[i]].begin(),free_vars[cur[i]].end());
        }
      }
      visited[cur] = true;
    }
  } while (!visit.empty());
}

Node CegConjectureProcess::getSymmetryBreakingPredicate(
    Node x, Node e, TypeNode tn, unsigned tindex, unsigned depth)
{
  return Node::null();
}

void CegConjectureProcess::debugPrint(const char* c) {}

void CegConjectureProcess::getComponentVector( Kind k, Node n, std::vector< Node >& args ) 
{
  if (n.getKind() == k)
  {
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      args.push_back(n[i]);
    }
  }
  else
  {
    args.push_back(n);
  }
}

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */
