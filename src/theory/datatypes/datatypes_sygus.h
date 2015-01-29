/*********************                                                        */
/*! \file theory_datatypes.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sygus utilities for theory of datatypes
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__DATATYPES_SYGUS_H
#define __CVC4__THEORY__DATATYPES__DATATYPES_SYGUS_H

#include "expr/node.h"
#include "util/datatype.h"
#include <iostream>
#include <map>
#include "context/context.h"
#include "context/cdchunk_list.h"
#include "context/cdhashmap.h"
#include "context/cdo.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class SygusUtil;

class SygusSplit
{
private:
  SygusUtil * d_util;
  std::map< Node, std::vector< Node > > d_splits;
  std::map< TypeNode, std::vector< bool > > d_sygus_nred;
  std::map< TypeNode, std::map< int, std::map< int, std::vector< bool > > > > d_sygus_pc_nred;
  std::map< TypeNode, std::map< int, std::map< int, std::vector< int > > > > d_sygus_pc_arg_pos;
  //information for builtin types
  std::map< TypeNode, std::map< int, Node > > d_type_value;
  std::map< TypeNode, Node > d_type_max_value;
  //information for sygus types
  std::map< TypeNode, TypeNode > d_register;  //stores sygus type
  std::map< TypeNode, std::map< int, Kind > > d_arg_kind;
  std::map< TypeNode, std::map< Kind, int > > d_kinds;
  std::map< TypeNode, std::map< int, Node > > d_arg_const;
  std::map< TypeNode, std::map< Node, int > > d_consts;
  std::map< TypeNode, std::map< Node, int > > d_ops;
  // type to (rewritten) to original
  std::map< TypeNode, std::map< Node, Node > > d_gen_terms;
  std::map< TypeNode, std::map< Node, bool > > d_gen_redundant;
private:
  bool isRegistered( TypeNode tn );
  int getKindArg( TypeNode tn, Kind k );
  int getConstArg( TypeNode tn, Node n );
  int getOpArg( TypeNode tn, Node n );
  bool hasKind( TypeNode tn, Kind k );
  bool hasConst( TypeNode tn, Node n );
  bool hasOp( TypeNode tn, Node n );
  bool isKindArg( TypeNode tn, int i );
  bool isConstArg( TypeNode tn, int i );
private:
  Node getVar( TypeNode tn, int i );
  Node getVarInc( TypeNode tn, std::map< TypeNode, int >& var_count );
private:
  /** register sygus type */
  void registerSygusType( TypeNode tn );
  /** register sygus operator */
  void registerSygusTypeConstructorArg( TypeNode tnn, const Datatype& dt, TypeNode tnnp, const Datatype& pdt, int csIndex, int sIndex );
  /** consider sygus split */
  bool considerSygusSplitKind( const Datatype& dt, const Datatype& pdt, TypeNode tn, TypeNode tnp, Kind k, Kind parent, int arg );
  bool considerSygusSplitConst( const Datatype& dt, const Datatype& pdt, TypeNode tn, TypeNode tnp, Node c, Kind parent, int arg );
  /** is assoc */
  bool isAssoc( Kind k );
  /** is comm */
  bool isComm( Kind k );
  /** isAntisymmetric */
  bool isAntisymmetric( Kind k, Kind& dk );
  /** is idempotent arg */
  bool isIdempotentArg( Node n, Kind ik, int arg );
  /** is singular arg */
  bool isSingularArg( Node n, Kind ik, int arg );
  /** get value */
  Node getTypeValue( TypeNode tn, int val );
  /** get value */
  Node getTypeMaxValue( TypeNode tn );
  /** get first occurrence */
  int getFirstArgOccurrence( const DatatypeConstructor& c, const Datatype& dt );
  /** is arg datatype */
  bool isArgDatatype( const DatatypeConstructor& c, int i, const Datatype& dt );
  /** get arg type */
  TypeNode getArgType( const DatatypeConstructor& c, int i );
private:
  // generic cache
  bool isGenericRedundant( TypeNode tn, Node g );
public:
  SygusSplit( SygusUtil * util ) : d_util( util ) {}
  /** get sygus splits */
  void getSygusSplits( Node n, const Datatype& dt, std::vector< Node >& splits, std::vector< Node >& lemmas );
};




class SygusSymBreak
{
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
  typedef context::CDHashMap< Node, int, NodeHashFunction > IntMap;
  typedef context::CDHashMap< int, int > IntIntMap;
private:
  SygusUtil * d_util;
  NodeMap d_testers;
  IntMap d_watched_terms;
  IntIntMap d_watched_count;
  context::CDO<Node> d_anchor;
  context::CDO<int> d_prog_depth;
  std::map< Node, Node > d_normalized;
  std::map< Node, Node > d_normalized_to_orig;
  void assignTester( Node tst, int depth );
  Node getCandidateProgramAtDepth( int depth, Node prog, int curr_depth, std::map< TypeNode, int >& var_count, std::vector< Node >& testers );
  void processProgramDepth( int depth );
  context::CDO<Node> d_conflict;
public:
  SygusSymBreak( SygusUtil * util, context::Context* c );
  /** add tester */
  void addTester( Node tst );
};

class SygusUtil
{
  friend class SygusSplit;
  friend class SygusSymBreak;
private:
  std::map< TypeNode, std::vector< Node > > d_fv;
  std::map< Node, TypeNode > d_fv_stype;
  SygusSplit * d_split;
  SygusSymBreak * d_sym_break;
private:
  Node getVar( TypeNode tn, int i );
  Node getVarInc( TypeNode tn, std::map< TypeNode, int >& var_count );
  Node mkGeneric( const Datatype& dt, int c, std::map< TypeNode, int >& var_count, std::map< int, Node >& pre );
  Node getSygusNormalized( Node n, std::map< TypeNode, int >& var_count, std::map< Node, Node >& subs );
public:
  SygusUtil( context::Context* c );
  SygusSplit * getSplit() { return d_split; }
  SygusSymBreak * getSymBreak() { return d_sym_break; }
};


}
}
}

#endif
