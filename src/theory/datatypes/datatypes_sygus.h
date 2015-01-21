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

#ifndef __CVC4__THEORY__DATATYPES__DATATYPES_SYGUS_H
#define __CVC4__THEORY__DATATYPES__DATATYPES_SYGUS_H

#include "expr/node.h"
#include "util/datatype.h"
#include <iostream>
#include <map>
#include "context/cdchunk_list.h"

namespace CVC4 {
namespace theory {
namespace datatypes {
  
class SygusSplit
{
private:
  std::map< TypeNode, std::vector< bool > > d_sygus_nred;
  std::map< Node, std::map< int, std::vector< bool > > > d_sygus_pc_nred;
  std::map< TypeNode, std::map< int, Node > > d_type_value;
  std::map< TypeNode, Node > d_type_max_value;
private:
  /** consider sygus split */
  bool considerSygusSplitKind( const Datatype& dt, const Datatype& pdt, Kind k, Kind parent, int arg,
                               std::map< Kind, int >& kinds, std::map< Kind, int >& pkinds,
                               std::map< Node, int >& consts, std::map< Node, int >& pconsts );
  bool considerSygusSplitConst( const Datatype& dt, const Datatype& pdt, Node c, Kind parent, int arg,
                                std::map< Kind, int >& kinds, std::map< Kind, int >& pkinds,
                                std::map< Node, int >& consts, std::map< Node, int >& pconsts );
  /** get sygus kinds */
  void getSygusKinds( const Datatype& dt, std::map< int, Kind >& arg_kind, std::map< Kind, int >& kinds, std::map< int, Node >& arg_const, std::map< Node, int >& consts );
  /** is assoc */
  bool isAssoc( Kind k );
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
public:
  /** get sygus splits */
  void getSygusSplits( Node n, const Datatype& dt, std::vector< Node >& splits );
};
  
  
}
}
}

#endif
