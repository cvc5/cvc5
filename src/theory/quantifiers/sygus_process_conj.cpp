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
    TypeNode atn = TypeNode::fromType( argTypes[j] );
    Node k = NodeManager::currentNM()->mkBoundVar("a",atn);
    d_arg_vars.push_back(k);
    d_arg_var_num[k] = j;
    d_arg_props.push_back(CegConjectureProcessArg());
    // assign the disequality ids to the argument position
    // initially, all variables of the same type have the same deq id
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

bool CegConjectureProcessFun::checkMatch( Node cn, Node n, std::unordered_map< unsigned, Node >& n_arg_map ) {
  std::unordered_map<TNode, TNode, TNodeHashFunction> visited;
  std::unordered_map<TNode, TNode, TNodeHashFunction>::iterator it;
  std::stack<TNode> visit[2];
  TNode cur[2];
  visit[0].push(cn);
  visit[1].push(n);
  do {
    for( unsigned r=0; r<2; r++ ){
      cur[r] = visit[r].top();
      visit[r].pop();
    }
    it = visited.find(cur[0]);

    if (it == visited.end()) {
      visited[cur[0]] = cur[1];
      if( cur[0]!=cur[1] ){
        unsigned arg_index = 0;
        if( isArgVar( cur[0], arg_index ) ){
          // must map to the correct term
          std::unordered_map< unsigned, Node >::iterator itn = n_arg_map.find( arg_index );
          if( itn==n_arg_map.end() || itn->second!=cur[1] ){
            return false;
          }
        }else if( cur[0].hasOperator() && cur[1].hasOperator() &&
                  cur[0].getNumChildren()==cur[1].getNumChildren() && 
                  cur[0].getOperator()==cur[1].getOperator() ){
          for( unsigned r=0; r<2; r++ ){
            for (unsigned i = 0; i < cur[r].getNumChildren(); i++) {
              visit[r].push(cur[r][i]);
            }
          }
        }else{
          return false;          
        }
      }
    }else if( it->second!=cur[1] ){
      return false;      
    }
  } while (!visit[0].empty());
  return true;
}

bool CegConjectureProcessFun::isArgVar( Node n, unsigned& arg_index ) {
  if( n.isVar() ){
    std::unordered_map< Node, unsigned, NodeHashFunction >::iterator ita = d_arg_var_num.find( n );
    if( ita!=d_arg_var_num.end() ){
      arg_index = ita->second;
      return true;
    }
  }
  return false;
}

Node CegConjectureProcessFun::inferDefinition( Node n, std::unordered_map< Node, unsigned, NodeHashFunction >& term_to_arg_use,
                                               std::unordered_map<Node, std::unordered_set< Node, NodeHashFunction >, NodeHashFunction >& free_vars){
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::stack<TNode> visit;
  TNode cur;
  visit.push(n);
  do {
    cur = visit.top();
    visit.pop();
    it = visited.find(cur);
    if (it == visited.end()) {
      // if it is ground, we can use it
      if( free_vars[cur].empty() ){
        visited[cur] = cur;
      }else{
        // if it is term used by another argument, use it
        std::unordered_map< Node, unsigned, NodeHashFunction >::iterator itt = term_to_arg_use.find(cur);
        if(itt != term_to_arg_use.end() ){
          visited[cur] = d_arg_vars[itt->second];          
        }else if( cur.getNumChildren()>0 ){
          // try constructing children
          visited[cur] = Node::null();
          visit.push(cur);
          for (unsigned i = 0; i < cur.getNumChildren(); i++) {
            visit.push(cur[i]);
          }
        }else{
          return Node::null();        
        }
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
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}


void CegConjectureProcessFun::processTerms(std::vector< Node >& ns, std::vector< Node >& ks, Node nf,
                                           std::unordered_set< Node, NodeHashFunction >& synth_fv, 
                                           std::unordered_map<Node, std::unordered_set< Node, NodeHashFunction >, NodeHashFunction >& free_vars) {
  Assert( ns.size()==ks.size() );
  Trace("sygus-process-arg-deps") << "Process " << ns.size() << " applications of " << d_synth_fun << "..." << std::endl;
  
  // get the relevant variables
  std::unordered_set< Node, NodeHashFunction > rlv_vars;
  Assert( free_vars.find(nf)!=free_vars.end());
  rlv_vars = free_vars[nf];
  
  // update constant argument information
  for(unsigned index=0; index<ns.size(); index++ ){
    Node n = ns[index];
    Trace("sygus-process-arg-deps") << "  analyze argument information for application #" << index << ": " << n << std::endl;

    // the arguments that we have processed
    std::unordered_set< unsigned > args_processed;
    
    // first, check if any variables maintain their definition   
    std::unordered_map< unsigned, Node > n_arg_map;
    for( unsigned a=0; a<n.getNumChildren(); a++ ){
      n_arg_map[a] = n[a];      
    }
    for( unsigned a=0; a<n.getNumChildren(); a++ ){
      if( !d_arg_props[a].d_relevant && !d_arg_props[a].d_const_arg.isNull() ){
        if( checkMatch( d_arg_props[a].d_const_arg, n[a], n_arg_map ) ){
          args_processed.insert( a );
          Trace("sygus-process-arg-deps") << "   ...processed arg #" << a << " (consistent definition)." << std::endl;
        }
      }
    }
    
    // compute term to argument mapping
    std::unordered_map< Node, std::vector< unsigned >, NodeHashFunction > term_to_args;
    for( unsigned a=0; a<n.getNumChildren(); a++ ){
      if( args_processed.find(a)==args_processed.end() ){
        term_to_args[n[a]].push_back(a);
      }
    }
    
    std::unordered_map< Node, unsigned, NodeHashFunction > term_to_arg_use;
    std::unordered_map< unsigned, Node > arg_use_map;

    for(std::unordered_map< Node, std::vector< unsigned >, NodeHashFunction >::iterator it = term_to_args.begin();
        it != term_to_args.end(); ++it ){
      Node nn = it->first;
      Trace("sygus-process-arg-deps") << "    argument " << nn;
      // check the status of this term
      if( nn.isVar() && synth_fv.find(nn)!=synth_fv.end() ){
        //is it relevant?
        if( rlv_vars.find(nn)!=rlv_vars.end() ){
          Trace("sygus-process-arg-deps") << " is a relevant variable." << std::endl;
          // check if we have marked at least one argument for this variable as relevant
          
          
        }else{
          Trace("sygus-process-arg-deps") << " is an irrelevant variable." << std::endl;
        }
      }else{
        // this can be more precise
        Trace("sygus-process-arg-deps") << " is a relevant term." << std::endl;
      }
    }
      
      /*
      Node arg = n[i];
      if( d_arg_props[i].d_set_const_arg ){
        if( !d_arg_props[i].d_const_arg.isNull() && arg!=d_arg_props[i].d_const_arg ){
          d_arg_props[i].d_const_arg = Node::null();
        }
      }else{
        d_arg_props[i].d_const_arg = arg;
      }
      */
  }


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
