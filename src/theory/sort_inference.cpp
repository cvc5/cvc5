/*********************                                                        */
/*! \file sort_inference.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sort inference module
 **
 ** This class implements sort inference, based on a simple algorithm:
 ** First, we assume all functions and predicates have distinct uninterpreted types.
 ** One pass is made through the input assertions, while a union-find data structure
 ** maintains necessary information regarding constraints on these types.
 **/

#include "theory/sort_inference.h"

#include <vector>

#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "theory/rewriter.h"
#include "theory/quantifiers/quant_util.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

namespace CVC4 {

void SortInference::UnionFind::print(const char * c){
  for( std::map< int, int >::iterator it = d_eqc.begin(); it != d_eqc.end(); ++it ){
    Trace(c) << "s_" << it->first << " = s_" << it->second << ", ";
  }
  for( unsigned i=0; i<d_deq.size(); i++ ){
    Trace(c) << "s_" << d_deq[i].first << " != s_" << d_deq[i].second << ", ";
  }
  Trace(c) << std::endl;
}
void SortInference::UnionFind::set( UnionFind& c ) {
  clear();
  for( std::map< int, int >::iterator it = c.d_eqc.begin(); it != c.d_eqc.end(); ++it ){
    d_eqc[ it->first ] = it->second;
  }
  d_deq.insert( d_deq.end(), c.d_deq.begin(), c.d_deq.end() );
}
int SortInference::UnionFind::getRepresentative( int t ){
  std::map< int, int >::iterator it = d_eqc.find( t );
  if( it==d_eqc.end() || it->second==t ){
    return t;
  }else{
    int rt = getRepresentative( it->second );
    d_eqc[t] = rt;
    return rt;
  }
}
void SortInference::UnionFind::setEqual( int t1, int t2 ){
  if( t1!=t2 ){
    int rt1 = getRepresentative( t1 );
    int rt2 = getRepresentative( t2 );
    if( rt1>rt2 ){
      d_eqc[rt1] = rt2;
    }else{
      d_eqc[rt2] = rt1;
    }
  }
}
bool SortInference::UnionFind::isValid() {
  for( unsigned i=0; i<d_deq.size(); i++ ){
    if( areEqual( d_deq[i].first, d_deq[i].second ) ){
      return false;
    }
  }
  return true;
}


void SortInference::recordSubsort( TypeNode tn, int s ){
  s = d_type_union_find.getRepresentative( s );
  if( std::find( d_sub_sorts.begin(), d_sub_sorts.end(), s )==d_sub_sorts.end() ){
    d_sub_sorts.push_back( s );
    d_type_sub_sorts[tn].push_back( s );
  }
}

void SortInference::printSort( const char* c, int t ){
  int rt = d_type_union_find.getRepresentative( t );
  if( d_type_types.find( rt )!=d_type_types.end() ){
    Trace(c) << d_type_types[rt];
  }else{
    Trace(c) << "s_" << rt;
  }
}

void SortInference::reset() {
  d_sub_sorts.clear();
  d_non_monotonic_sorts.clear();
  d_type_sub_sorts.clear();
  //reset info
  d_sortCount = 1;
  d_type_union_find.clear();
  d_type_types.clear();
  d_id_for_types.clear();
  d_op_return_types.clear();
  d_op_arg_types.clear();
  d_var_types.clear();
  //for rewriting
  d_symbol_map.clear();
  d_const_map.clear();
}

void SortInference::initialize(const std::vector<Node>& assertions)
{
  Trace("sort-inference-proc") << "Calculating sort inference..." << std::endl;
  // process all assertions
  std::map<Node, int> visited;
  NodeManager * nm = NodeManager::currentNM();
  int btId = getIdForType( nm->booleanType() );
  for (const Node& a : assertions)
  {
    Trace("sort-inference-debug") << "Process " << a << std::endl;
    std::map<Node, Node> var_bound;
    int pid = process(a, var_bound, visited);
    // the type of the topmost term must be Boolean
    setEqual( pid, btId );
  }
  Trace("sort-inference-proc") << "...done" << std::endl;
  for (const std::pair<const Node, int>& rt : d_op_return_types)
  {
    Trace("sort-inference") << rt.first << " : ";
    TypeNode retTn = rt.first.getType();
    if (!d_op_arg_types[rt.first].empty())
    {
      Trace("sort-inference") << "( ";
      for (size_t i = 0; i < d_op_arg_types[rt.first].size(); i++)
      {
        recordSubsort(retTn[i], d_op_arg_types[rt.first][i]);
        printSort("sort-inference", d_op_arg_types[rt.first][i]);
        Trace("sort-inference") << " ";
      }
      Trace("sort-inference") << ") -> ";
      retTn = retTn[(int)retTn.getNumChildren() - 1];
    }
    recordSubsort(retTn, rt.second);
    printSort("sort-inference", rt.second);
    Trace("sort-inference") << std::endl;
  }
  for (std::pair<const Node, std::map<Node, int> >& vt : d_var_types)
  {
    Trace("sort-inference")
        << "Quantified formula : " << vt.first << " : " << std::endl;
    for (const Node& v : vt.first[0])
    {
      recordSubsort(v.getType(), vt.second[v]);
      printSort("sort-inference", vt.second[v]);
      Trace("sort-inference") << std::endl;
    }
    Trace("sort-inference") << std::endl;
  }

  // determine monotonicity of sorts
  Trace("sort-inference-proc")
      << "Calculating monotonicty for subsorts..." << std::endl;
  std::map<Node, std::map<int, bool> > visitedm;
  for (const Node& a : assertions)
  {
    Trace("sort-inference-debug")
        << "Process monotonicity for " << a << std::endl;
    std::map<Node, Node> var_bound;
    processMonotonic(a, true, true, var_bound, visitedm);
  }
  Trace("sort-inference-proc") << "...done" << std::endl;

  Trace("sort-inference") << "We have " << d_sub_sorts.size()
                          << " sub-sorts : " << std::endl;
  for (unsigned i = 0, size = d_sub_sorts.size(); i < size; i++)
  {
    printSort("sort-inference", d_sub_sorts[i]);
    if (d_type_types.find(d_sub_sorts[i]) != d_type_types.end())
    {
      Trace("sort-inference") << " is interpreted." << std::endl;
    }
    else if (d_non_monotonic_sorts.find(d_sub_sorts[i])
             == d_non_monotonic_sorts.end())
    {
      Trace("sort-inference") << " is monotonic." << std::endl;
    }
    else
    {
      Trace("sort-inference") << " is not monotonic." << std::endl;
    }
  }
}

Node SortInference::simplify(Node n,
                             std::map<Node, Node>& model_replace_f,
                             std::map<Node, std::map<TypeNode, Node> >& visited)
{
  Trace("sort-inference-debug") << "Simplify " << n << std::endl;
  std::map<Node, Node> var_bound;
  TypeNode tnn;
  Node ret = simplifyNode(n, var_bound, tnn, model_replace_f, visited);
  ret = theory::Rewriter::rewrite(ret);
  return ret;
}

void SortInference::getNewAssertions(std::vector<Node>& new_asserts)
{
  NodeManager* nm = NodeManager::currentNM();
  // now, ensure constants are distinct
  for (const std::pair<const TypeNode, std::map<Node, Node> >& cm : d_const_map)
  {
    std::vector<Node> consts;
    for (const std::pair<const Node, Node>& c : cm.second)
    {
      Assert(c.first.isConst());
      consts.push_back(c.second);
    }
    // add lemma enforcing introduced constants to be distinct
    if (consts.size() > 1)
    {
      Node distinct_const = nm->mkNode(kind::DISTINCT, consts);
      Trace("sort-inference-rewrite")
          << "Add the constant distinctness lemma: " << std::endl;
      Trace("sort-inference-rewrite") << "  " << distinct_const << std::endl;
      new_asserts.push_back(distinct_const);
    }
  }

  // enforce constraints based on monotonicity
  Trace("sort-inference-proc") << "Enforce monotonicity..." << std::endl;

  for (const std::pair<const TypeNode, std::vector<int> >& tss :
       d_type_sub_sorts)
  {
    int nmonSort = -1;
    unsigned nsorts = tss.second.size();
    for (unsigned i = 0; i < nsorts; i++)
    {
      if (d_non_monotonic_sorts.find(tss.second[i])
          != d_non_monotonic_sorts.end())
      {
        nmonSort = tss.second[i];
        break;
      }
    }
    if (nmonSort != -1)
    {
      std::vector<Node> injections;
      TypeNode base_tn = getOrCreateTypeForId(nmonSort, tss.first);
      for (unsigned i = 0; i < nsorts; i++)
      {
        if (tss.second[i] != nmonSort)
        {
          TypeNode new_tn = getOrCreateTypeForId(tss.second[i], tss.first);
          // make injection to nmonSort
          Node a1 = mkInjection(new_tn, base_tn);
          injections.push_back(a1);
          if (d_non_monotonic_sorts.find(tss.second[i])
              != d_non_monotonic_sorts.end())
          {
            // also must make injection from nmonSort to this
            Node a2 = mkInjection(base_tn, new_tn);
            injections.push_back(a2);
          }
        }
      }
      if (Trace.isOn("sort-inference-rewrite"))
      {
        Trace("sort-inference-rewrite")
            << "Add the following injections for " << tss.first
            << " to ensure consistency wrt non-monotonic sorts : " << std::endl;
        for (const Node& i : injections)
        {
          Trace("sort-inference-rewrite") << "   " << i << std::endl;
        }
      }
      new_asserts.insert(
          new_asserts.end(), injections.begin(), injections.end());
    }
  }
  Trace("sort-inference-proc") << "...done" << std::endl;
  // no sub-sort information is stored
  reset();
  Trace("sort-inference-debug") << "Finished sort inference" << std::endl;
}

void SortInference::computeMonotonicity(const std::vector<Node>& assertions)
{
  std::map<Node, std::map<int, bool> > visitedmt;
  Trace("sort-inference-proc")
      << "Calculating monotonicty for types..." << std::endl;
  for (const Node& a : assertions)
  {
    Trace("sort-inference-debug")
        << "Process type monotonicity for " << a << std::endl;
    std::map<Node, Node> var_bound;
    processMonotonic(a, true, true, var_bound, visitedmt, true);
  }
  Trace("sort-inference-proc") << "...done" << std::endl;
}

void SortInference::setEqual( int t1, int t2 ){
  if( t1!=t2 ){
    int rt1 = d_type_union_find.getRepresentative( t1 );
    int rt2 = d_type_union_find.getRepresentative( t2 );
    if( rt1!=rt2 ){
      Trace("sort-inference-debug") << "Set equal : ";
      printSort( "sort-inference-debug", rt1 );
      Trace("sort-inference-debug") << " ";
      printSort( "sort-inference-debug", rt2 );
      Trace("sort-inference-debug") << std::endl;
      /*
      d_type_eq_class[rt1].insert( d_type_eq_class[rt1].end(), d_type_eq_class[rt2].begin(), d_type_eq_class[rt2].end() );
      d_type_eq_class[rt2].clear();
      Trace("sort-inference-debug") << "EqClass : { ";
      for( int i=0; i<(int)d_type_eq_class[rt1].size(); i++ ){
        Trace("sort-inference-debug") << d_type_eq_class[rt1][i] << ", ";
      }
      Trace("sort-inference-debug") << "}" << std::endl;
      */
      if( rt2>rt1 ){
        //swap
        int swap = rt1;
        rt1 = rt2;
        rt2 = swap;
      }
      std::map< int, TypeNode >::iterator it1 = d_type_types.find( rt1 );
      if( it1!=d_type_types.end() ){
        if( d_type_types.find( rt2 )==d_type_types.end() ){
          d_type_types[rt2] = it1->second;
          d_type_types.erase( rt1 );
        }else{
          Trace("sort-inference-debug") << "...fail : associated with types " << d_type_types[rt1] << " and " << d_type_types[rt2] << std::endl;
          return;
        }
      }
      d_type_union_find.d_eqc[rt1] = rt2;
    }
  }
}

int SortInference::getIdForType( TypeNode tn ){
  //register the return type
  std::map< TypeNode, int >::iterator it = d_id_for_types.find( tn );
  if( it==d_id_for_types.end() ){
    int sc = d_sortCount;
    d_type_types[d_sortCount] = tn;
    d_id_for_types[tn] = d_sortCount;
    d_sortCount++;
    return sc;
  }else{
    return it->second;
  }
}

int SortInference::process( Node n, std::map< Node, Node >& var_bound, std::map< Node, int >& visited ){
  std::map< Node, int >::iterator itv = visited.find( n );
  if( itv!=visited.end() ){
    return itv->second;
  }else{
    //add to variable bindings
    bool use_new_visited = false;
    std::map< Node, int > new_visited;
    if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
      if( d_var_types.find( n )!=d_var_types.end() ){
        return getIdForType( n.getType() );
      }else{
        //apply sort inference to quantified variables
        for( size_t i=0; i<n[0].getNumChildren(); i++ ){
          TypeNode nitn = n[0][i].getType();
          if( !nitn.isSort() )
          {
            // If the variable is of an interpreted sort, we assume the
            // the sort of the variable will stay the same sort.
            d_var_types[n][n[0][i]] = getIdForType( nitn );
          }
          else
          {
            // If it is of an uninterpreted sort, infer subsorts.
            d_var_types[n][n[0][i]] = d_sortCount;
            d_sortCount++;
          }
          var_bound[ n[0][i] ] = n;
        }
      }
      use_new_visited = true;
    }

    //process children
    std::vector< Node > children;
    std::vector< int > child_types;
    for( size_t i=0; i<n.getNumChildren(); i++ ){
      bool processChild = true;
      if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
        processChild =
            options::userPatternsQuant() == options::UserPatMode::IGNORE
                ? i == 1
                : i >= 1;
      }
      if( processChild ){
        children.push_back( n[i] );
        child_types.push_back( process( n[i], var_bound, use_new_visited ? new_visited : visited ) );
      }
    }

    //remove from variable bindings
    if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
      //erase from variable bound
      for( size_t i=0; i<n[0].getNumChildren(); i++ ){
        var_bound.erase( n[0][i] );
      }
    }
    Trace("sort-inference-debug") << "...Process " << n << std::endl;

    int retType;
    if( n.getKind()==kind::EQUAL && !n[0].getType().isBoolean() ){
      Trace("sort-inference-debug") << "For equality " << n << ", set equal types from : " << n[0].getType() << " " << n[1].getType() << std::endl;
      //if original types are mixed (e.g. Int/Real), don't commit type equality in either direction
      if( n[0].getType()!=n[1].getType() ){
        //for now, assume the original types
        for( unsigned i=0; i<2; i++ ){
          int ct = getIdForType( n[i].getType() );
          setEqual( child_types[i], ct );
        }
      }else{
        //we only require that the left and right hand side must be equal
        setEqual( child_types[0], child_types[1] );
      }
      d_equality_types[n] = child_types[0];
      retType = getIdForType( n.getType() );
    }
    else if (isHandledApplyUf(n.getKind()))
    {
      Node op = n.getOperator();
      TypeNode tn_op = op.getType();
      if( d_op_return_types.find( op )==d_op_return_types.end() ){
        if( n.getType().isBoolean() ){
          //use booleans
          d_op_return_types[op] = getIdForType( n.getType() );
        }else{
          //assign arbitrary sort for return type
          d_op_return_types[op] = d_sortCount;
          d_sortCount++;
        }
        // d_type_eq_class[d_sortCount].push_back( op );
        // assign arbitrary sort for argument types
        for( size_t i=0; i<n.getNumChildren(); i++ ){
          d_op_arg_types[op].push_back(d_sortCount);
          d_sortCount++;
        }
      }
      for( size_t i=0; i<n.getNumChildren(); i++ ){
        //the argument of the operator must match the return type of the subterm
        if( n[i].getType()!=tn_op[i] ){
          //if type mismatch, assume original types
          Trace("sort-inference-debug") << "Argument " << i << " of " << op << " " << n[i] << " has type " << n[i].getType();
          Trace("sort-inference-debug") << ", while operator arg has type " << tn_op[i] << std::endl;
          int ct1 = getIdForType( n[i].getType() );
          setEqual( child_types[i], ct1 );
          int ct2 = getIdForType( tn_op[i] );
          setEqual( d_op_arg_types[op][i], ct2 );
        }else{
          setEqual( child_types[i], d_op_arg_types[op][i] );
        }
      }
      //return type is the return type
      retType = d_op_return_types[op];
    }else{
      std::map< Node, Node >::iterator it = var_bound.find( n );
      if( it!=var_bound.end() ){
        Trace("sort-inference-debug") << n << " is a bound variable." << std::endl;
        //the return type was specified while binding
        retType = d_var_types[it->second][n];
      }else if( n.isVar() ){
        Trace("sort-inference-debug") << n << " is a variable." << std::endl;
        if( d_op_return_types.find( n )==d_op_return_types.end() ){
          //assign arbitrary sort
          d_op_return_types[n] = d_sortCount;
          d_sortCount++;
          // d_type_eq_class[d_sortCount].push_back( n );
        }
        retType = d_op_return_types[n];
      }else if( n.isConst() ){
        Trace("sort-inference-debug") << n << " is a constant." << std::endl;
        //can be any type we want
        retType = d_sortCount;
        d_sortCount++;
      }else{
        Trace("sort-inference-debug") << n << " is a interpreted symbol." << std::endl;
        //it is an interpreted term
        for( size_t i=0; i<children.size(); i++ ){
          Trace("sort-inference-debug") << children[i] << " forced to have " << children[i].getType() << std::endl;
          //must enforce the actual type of the operator on the children
          int ct = getIdForType( children[i].getType() );
          setEqual( child_types[i], ct );
        }
        //return type must be the actual return type
        retType = getIdForType( n.getType() );
      }
    }
    Trace("sort-inference-debug") << "...Type( " << n << " ) = ";
    printSort("sort-inference-debug", retType );
    Trace("sort-inference-debug") << std::endl;
    visited[n] = retType;
    return retType;
  }
}

void SortInference::processMonotonic( Node n, bool pol, bool hasPol, std::map< Node, Node >& var_bound, std::map< Node, std::map< int, bool > >& visited, bool typeMode ) {
  int pindex = hasPol ? ( pol ? 1 : -1 ) : 0;
  if( visited[n].find( pindex )==visited[n].end() ){
    visited[n][pindex] = true;
    Trace("sort-inference-debug") << "...Process monotonic " << pol << " " << hasPol << " " << n << std::endl;
    if( n.getKind()==kind::FORALL ){
      //only consider variables universally if it is possible this quantified formula is asserted positively
      if( !hasPol || pol ){
        for( unsigned i=0; i<n[0].getNumChildren(); i++ ){
          var_bound[n[0][i]] = n;
        }
      }
      processMonotonic( n[1], pol, hasPol, var_bound, visited, typeMode );
      if( !hasPol || pol ){
        for( unsigned i=0; i<n[0].getNumChildren(); i++ ){
          var_bound.erase( n[0][i] );
        }
      }
      return;
    }else if( n.getKind()==kind::EQUAL ){
      if( !hasPol || pol ){
        for( unsigned i=0; i<2; i++ ){
          if( var_bound.find( n[i] )!=var_bound.end() ){
            if( !typeMode ){
              int sid = getSortId( var_bound[n[i]], n[i] );
              d_non_monotonic_sorts[sid] = true;
            }else{
              d_non_monotonic_sorts_orig[n[i].getType()] = true;
            }
            break;
          }
        }
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      bool npol;
      bool nhasPol;
      theory::QuantPhaseReq::getPolarity( n, i, hasPol, pol, nhasPol, npol );
      processMonotonic( n[i], npol, nhasPol, var_bound, visited, typeMode );
    }
  }
}


TypeNode SortInference::getOrCreateTypeForId( int t, TypeNode pref ){
  int rt = d_type_union_find.getRepresentative( t );
  if( d_type_types.find( rt )!=d_type_types.end() ){
    return d_type_types[rt];
  }else{
    TypeNode retType;
    // See if we can assign pref. This is an optimization for reusing an
    // uninterpreted sort as the first subsort, so that fewer symbols needed
    // to be rewritten in the sort-inferred signature. Notice we only assign
    // pref here if it is an uninterpreted sort.
    if (!pref.isNull() && d_id_for_types.find(pref) == d_id_for_types.end()
        && pref.isSort())
    {
      retType = pref;
    }else{
      //must create new type
      std::stringstream ss;
      ss << "it_" << t << "_" << pref;
      retType = NodeManager::currentNM()->mkSort( ss.str() );
    }
    Trace("sort-inference") << "-> Make type " << retType << " to correspond to ";
    printSort("sort-inference", t );
    Trace("sort-inference") << std::endl;
    d_id_for_types[ retType ] = rt;
    d_type_types[ rt ] = retType;
    return retType;
  }
}

TypeNode SortInference::getTypeForId( int t ){
  int rt = d_type_union_find.getRepresentative( t );
  if( d_type_types.find( rt )!=d_type_types.end() ){
    return d_type_types[rt];
  }else{
    return TypeNode::null();
  }
}

Node SortInference::getNewSymbol( Node old, TypeNode tn ){
  // if no sort was inferred for this node, return original
  if( tn.isNull() || tn.isComparableTo( old.getType() ) ){
    return old;
  }else if( old.isConst() ){
    //must make constant of type tn
    if( d_const_map[tn].find( old )==d_const_map[tn].end() ){
      std::stringstream ss;
      ss << "ic_" << tn << "_" << old;
      d_const_map[tn][ old ] = NodeManager::currentNM()->mkSkolem( ss.str(), tn, "constant created during sort inference" );  //use mkConst???
    }
    return d_const_map[tn][ old ];
  }else if( old.getKind()==kind::BOUND_VARIABLE ){
    std::stringstream ss;
    ss << "b_" << old;
    return NodeManager::currentNM()->mkBoundVar( ss.str(), tn );
  }else{
    std::stringstream ss;
    ss << "i_" << old;
    return NodeManager::currentNM()->mkSkolem( ss.str(), tn, "created during sort inference" );
  }
}

Node SortInference::simplifyNode(
    Node n,
    std::map<Node, Node>& var_bound,
    TypeNode tnn,
    std::map<Node, Node>& model_replace_f,
    std::map<Node, std::map<TypeNode, Node> >& visited)
{
  std::map< TypeNode, Node >::iterator itv = visited[n].find( tnn );
  if( itv!=visited[n].end() ){
    return itv->second;
  }else{
    Trace("sort-inference-debug2") << "Simplify " << n << ", type context=" << tnn << std::endl;
    std::vector< Node > children;
    std::map< Node, std::map< TypeNode, Node > > new_visited;
    bool use_new_visited = false;
    if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
      //recreate based on types of variables
      std::vector< Node > new_children;
      for( size_t i=0; i<n[0].getNumChildren(); i++ ){
        TypeNode tn = getOrCreateTypeForId( d_var_types[n][ n[0][i] ], n[0][i].getType() );
        Node v = getNewSymbol( n[0][i], tn );
        Trace("sort-inference-debug2") << "Map variable " << n[0][i] << " to " << v << std::endl;
        new_children.push_back( v );
        var_bound[ n[0][i] ] = v;
      }
      children.push_back( NodeManager::currentNM()->mkNode( n[0].getKind(), new_children ) );
      use_new_visited = true;
    }

    //process children
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
      children.push_back( n.getOperator() );
    }
    Node op;
    if( n.hasOperator() ){
      op = n.getOperator();
    }
    bool childChanged = false;
    TypeNode tnnc;
    for( size_t i=0; i<n.getNumChildren(); i++ ){
      bool processChild = true;
      if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
        processChild =
            options::userPatternsQuant() == options::UserPatMode::IGNORE
                ? i == 1
                : i >= 1;
      }
      if( processChild ){
        if (isHandledApplyUf(n.getKind()))
        {
          Assert(d_op_arg_types.find(op) != d_op_arg_types.end());
          tnnc = getOrCreateTypeForId( d_op_arg_types[op][i], n[i].getType() );
          Assert(!tnnc.isNull());
        }
        else if (n.getKind() == kind::EQUAL && !n[0].getType().isBoolean()
                 && i == 0)
        {
          Assert(d_equality_types.find(n) != d_equality_types.end());
          tnnc = getOrCreateTypeForId( d_equality_types[n], n[0].getType() );
          Assert(!tnnc.isNull());
        }
        Node nc = simplifyNode(n[i],
                               var_bound,
                               tnnc,
                               model_replace_f,
                               use_new_visited ? new_visited : visited);
        Trace("sort-inference-debug2") << "Simplify " << i << " " << n[i] << " returned " << nc << std::endl;
        children.push_back( nc );
        childChanged = childChanged || nc!=n[i];
      }
    }

    //remove from variable bindings
    Node ret;
    if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
      //erase from variable bound
      for( size_t i=0; i<n[0].getNumChildren(); i++ ){
        Trace("sort-inference-debug2") << "Remove bound for " << n[0][i] << std::endl;
        var_bound.erase( n[0][i] );
      }
      ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
    }else if( n.getKind()==kind::EQUAL ){
      TypeNode tn1 = children[0].getType();
      TypeNode tn2 = children[1].getType();
      if( !tn1.isComparableTo( tn2 ) ){
        Trace("sort-inference-warn") << "Sort inference created bad equality: " << children[0] << " = " << children[1] << std::endl;
        Trace("sort-inference-warn") << "  Types : " << children[0].getType() << " " << children[1].getType() << std::endl;
        Assert(false);
      }
      ret = NodeManager::currentNM()->mkNode( kind::EQUAL, children );
    }
    else if (isHandledApplyUf(n.getKind()))
    {
      if( d_symbol_map.find( op )==d_symbol_map.end() ){
        //make the new operator if necessary
        bool opChanged = false;
        std::vector< TypeNode > argTypes;
        for( size_t i=0; i<n.getNumChildren(); i++ ){
          TypeNode tn = getOrCreateTypeForId( d_op_arg_types[op][i], n[i].getType() );
          argTypes.push_back( tn );
          if( tn!=n[i].getType() ){
            opChanged = true;
          }
        }
        TypeNode retType = getOrCreateTypeForId( d_op_return_types[op], n.getType() );
        if( retType!=n.getType() ){
          opChanged = true;
        }
        if( opChanged ){
          std::stringstream ss;
          ss << "io_" << op;
          TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, retType );
          d_symbol_map[op] = NodeManager::currentNM()->mkSkolem( ss.str(), typ, "op created during sort inference" );
          Trace("setp-model") << "Function " << op << " is replaced with " << d_symbol_map[op] << std::endl;
          model_replace_f[op] = d_symbol_map[op];
        }else{
          d_symbol_map[op] = op;
        }
      }
      children[0] = d_symbol_map[op];
      // make sure all children have been given proper types
      for (size_t i = 0, size = n.getNumChildren(); i < size; i++)
      {
        TypeNode tn = children[i+1].getType();
        TypeNode tna = getTypeForId( d_op_arg_types[op][i] );
        if (!tn.isSubtypeOf(tna))
        {
          Trace("sort-inference-warn") << "Sort inference created bad child: " << n << " " << n[i] << " " << tn << " " << tna << std::endl;
          Assert(false);
        }
      }
      ret = NodeManager::currentNM()->mkNode( kind::APPLY_UF, children );
    }else{
      std::map< Node, Node >::iterator it = var_bound.find( n );
      if( it!=var_bound.end() ){
        ret = it->second;
      }else if( n.getKind() == kind::VARIABLE || n.getKind() == kind::SKOLEM ){
        if( d_symbol_map.find( n )==d_symbol_map.end() ){
          TypeNode tn = getOrCreateTypeForId( d_op_return_types[n], n.getType() );
          d_symbol_map[n] = getNewSymbol( n, tn );
        }
        ret = d_symbol_map[n];
      }else if( n.isConst() ){
        //type is determined by context
        ret = getNewSymbol( n, tnn );
      }else if( childChanged ){
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }else{
        ret = n;
      }
    }
    visited[n][tnn] = ret;
    return ret;
  }
}

Node SortInference::mkInjection( TypeNode tn1, TypeNode tn2 ) {
  std::vector< TypeNode > tns;
  tns.push_back( tn1 );
  TypeNode typ = NodeManager::currentNM()->mkFunctionType( tns, tn2 );
  Node f = NodeManager::currentNM()->mkSkolem( "inj", typ, "injection for monotonicity constraint" );
  Trace("sort-inference") << "-> Make injection " << f << " from " << tn1 << " to " << tn2 << std::endl;
  Node v1 = NodeManager::currentNM()->mkBoundVar( "?x", tn1 );
  Node v2 = NodeManager::currentNM()->mkBoundVar( "?y", tn1 );
  Node ret = NodeManager::currentNM()->mkNode( kind::FORALL,
               NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, v1, v2 ),
               NodeManager::currentNM()->mkNode( kind::OR,
                 NodeManager::currentNM()->mkNode( kind::APPLY_UF, f, v1 ).eqNode( NodeManager::currentNM()->mkNode( kind::APPLY_UF, f, v2 ) ).negate(),
                 v1.eqNode( v2 ) ) );
  ret = theory::Rewriter::rewrite( ret );
  return ret;
}

int SortInference::getSortId( Node n ) {
  Node op = n.getKind()==kind::APPLY_UF ? n.getOperator() : n;
  if( d_op_return_types.find( op )!=d_op_return_types.end() ){
    return d_type_union_find.getRepresentative( d_op_return_types[op] );
  }else{
    return 0;
  }
}

int SortInference::getSortId( Node f, Node v ) {
  if( d_var_types.find( f )!=d_var_types.end() ){
    return d_type_union_find.getRepresentative( d_var_types[f][v] );
  }else{
    return 0;
  }
}

void SortInference::setSkolemVar( Node f, Node v, Node sk ){
  Trace("sort-inference-temp") << "Set skolem var for " << f << ", variable " << v << std::endl;
  if( isWellSortedFormula( f ) && d_var_types.find( f )==d_var_types.end() ){
    //calculate the sort for variables if not done so already
    std::map< Node, Node > var_bound;
    std::map< Node, int > visited;
    process( f, var_bound, visited );
  }
  d_op_return_types[sk] = getSortId( f, v );
  Trace("sort-inference-temp") << "Set skolem sort id for " << sk << " to " << d_op_return_types[sk] << std::endl;
}

bool SortInference::isWellSortedFormula( Node n ) {
  if (n.getType().isBoolean() && !isHandledApplyUf(n.getKind()))
  {
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !isWellSortedFormula( n[i] ) ){
        return false;
      }
    }
    return true;
  }else{
    return isWellSorted( n );
  }
}

bool SortInference::isWellSorted( Node n ) {
  if( getSortId( n )==0 ){
    return false;
  }else{
    if (isHandledApplyUf(n.getKind()))
    {
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        int s1 = getSortId( n[i] );
        int s2 = d_type_union_find.getRepresentative( d_op_arg_types[ n.getOperator() ][i] );
        if( s1!=s2 ){
          return false;
        }
        if( !isWellSorted( n[i] ) ){
          return false;
        }
      }
    }
    return true;
  }
}

bool SortInference::isMonotonic( TypeNode tn ) {
  Assert(tn.isSort());
  return d_non_monotonic_sorts_orig.find( tn )==d_non_monotonic_sorts_orig.end();
}

bool SortInference::isHandledApplyUf(Kind k) const
{
  return k == APPLY_UF && !options::ufHo();
}

}/* CVC4 namespace */
