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

void CegConjectureProcessFun::processTerm(Node n, Node k, Node nf,
                   std::unordered_map<Node, std::unordered_set< Node, NodeHashFunction >, NodeHashFunction >& free_vars) {
  Assert(n.getKind()==APPLY_UF);
  Assert(n.getOperator()==d_synth_fun);
  
  // update the disequality ids
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
    base = base[0][1];
    for( unsigned j=0; j<base[0].getNumChildren(); j++ ){
      synth_fv.insert(base[0][j]);
    }
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
  // make a copy of free variables
  std::unordered_set< Node, NodeHashFunction > synth_fv_n = synth_fv;
  std::unordered_map<Node,Node,NodeHashFunction> defs;
  std::unordered_map<Node,std::vector<Node>,NodeHashFunction> fun_to_defs;
  Node nf = flatten(n,synth_fv_n,defs,fun_to_defs);
  
  
  Trace("sygus-process-arg-deps") << "Flattened to: " << std::endl;
  Trace("sygus-process-arg-deps") << "  " << nf << std::endl;
  
  // get free variables in nf
  std::unordered_map<Node, std::unordered_set< Node, NodeHashFunction >, NodeHashFunction > free_vars;
  getFreeVariables(n,synth_fv,free_vars);
  
  // process the applications of synthesis functions
  for(std::unordered_map<Node,std::vector<Node>,NodeHashFunction>::iterator it = fun_to_defs.begin(); it != fun_to_defs.end(); ++it ){
    Node f = it->first;
    std::map<Node, CegConjectureProcessFun>::iterator its = d_sf_info.find(f);
    if(its!=d_sf_info.end()){
      for( unsigned j=0; j<it->second.size(); j++ ){
        Node k = it->second[j];
        Assert( defs.find(k)!=defs.end() );
        Node fa = defs[k];
        its->second.processTerm(fa,k,nf,free_vars);
      }
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
        std::unordered_set< Node, NodeHashFunction >& fv_cur = free_vars[cur];
        for (unsigned i = 0; i < cur.getNumChildren(); i++) {
          fv_cur.insert(free_vars[cur[i]].begin(),free_vars[cur[i]].end());
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
