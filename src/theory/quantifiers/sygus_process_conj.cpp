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
  std::unordered_map<TypeNode, unsigned, TypeNodeHashFunction> type_to_init_deq_id;
  std::vector<Type> argTypes = static_cast<FunctionType>(f.getType().toType()).getArgTypes();
  for( unsigned j=0; j<argTypes.size(); j++ ){
    // assign the disequality ids to the argument position
    // initially, all variables of the same type have the same deq id
    TypeNode atn = TypeNode::fromType( argTypes[j] );
    std::unordered_map<TypeNode, unsigned, TypeNodeHashFunction>::iterator it = type_to_init_deq_id.find(atn);
    unsigned deqid;
    if(it==type_to_init_deq_id.end()){
      deqid = d_deq_id_counter;
      type_to_init_deq_id[atn] = d_deq_id_counter;
      d_deq_id_counter++;
    }else{
      deqid = it->second;
    }
    d_arg_props[j].d_deq_id = deqid;
    // add to deq id equivalence class
    d_deq_id_eqc[deqid].insert( j );
  }
}

void CegConjectureProcessFun::processTerm(Node n, 
                                         std::unordered_map<TNode, std::unordered_set< TNode, TNodeHashFunction >, TNodeHashFunction >& freeVars,
                                         std::unordered_set< TNode, TNodeHashFunction >& synth_fv) {
  // update the disequality ids
  
  
  // merge equal variables
  
  
  // take free variables in each argument
        
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
  std::unordered_set< TNode, TNodeHashFunction > synth_fv;
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

void CegConjectureProcess::processConjunct(Node n, std::unordered_set< TNode, TNodeHashFunction >& synth_fv) {
  // free variables in each node
  std::unordered_map<TNode, std::unordered_set< TNode, TNodeHashFunction >, TNodeHashFunction > free_vars;
  // free variables in each arguments
  std::unordered_map<unsigned, std::unordered_set< TNode, TNodeHashFunction > > free_vars_args;
  
  std::unordered_map<TNode, bool, TNodeHashFunction> visited;
  std::unordered_map<TNode, bool, TNodeHashFunction>::iterator it;
  std::stack<TNode> visit;
  TNode cur;
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
      bool processed = false;
      if( cur.getKind()==APPLY_UF ){
        Node f = cur.getOperator();
        std::map<Node, CegConjectureProcessFun>::iterator its = d_sf_info.find(f);
        if(its!=d_sf_info.end()){
          // it is an application of a function to synthesize
          // process this f-application using the class
          its->second.processTerm(cur,free_vars,synth_fv);
          processed = true;
        }
      }
      if( !processed ){
        if( synth_fv.find(cur)!=synth_fv.end() ){
          // it is a free variable
          free_vars[cur].insert(cur);
        }
        else
        {
          // otherwise, carry the free variables from the children
          std::unordered_set< TNode, TNodeHashFunction >& fv_cur = free_vars[cur];
          for (unsigned i = 0; i < cur.getNumChildren(); i++) {
            fv_cur.insert(free_vars[cur[i]].begin(),free_vars[cur[i]].end());
          }
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
