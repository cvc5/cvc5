/*********************                                                        */
/*! \file regexp_operation.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Symbolic Regular Expresion Operations
 **
 ** Symbolic Regular Expression Operations
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__REGEXP__OPERATION_H
#define __CVC4__THEORY__STRINGS__REGEXP__OPERATION_H

#include <vector>
#include <set>
#include <algorithm>
#include "util/hash.h"
#include "util/regexp.h"
#include "theory/theory.h"
#include "theory/rewriter.h"
//#include "context/cdhashmap.h"

namespace CVC4 {
namespace theory {
namespace strings {

class RegExpOpr {
  typedef std::pair< Node, CVC4::String > PairNodeStr;
  typedef std::set< Node > SetNodes;
  typedef std::pair< Node, Node > PairNodes;

private:
  unsigned d_card;
  Node d_emptyString;
  Node d_true;
  Node d_false;
  Node d_emptySingleton;
  Node d_emptyRegexp;
  Node d_zero;
  Node d_one;

  char d_char_start;
  char d_char_end;
  Node d_sigma;
  Node d_sigma_star;

  std::map< PairNodes, Node > d_simpl_cache;
  std::map< PairNodes, Node > d_simpl_neg_cache;
  std::map< Node, std::pair< int, Node > > d_delta_cache;
  std::map< PairNodeStr, Node > d_dv_cache;
  std::map< PairNodeStr, std::pair< Node, int > > d_deriv_cache;
  std::map< Node, std::pair< Node, int > > d_compl_cache;
  std::map< Node, bool > d_cstre_cache;
  std::map< Node, std::pair< std::set<unsigned>, std::set<Node> > > d_cset_cache;
  std::map< Node, std::pair< std::set<unsigned>, std::set<Node> > > d_fset_cache;
  std::map< PairNodes, Node > d_inter_cache;
  std::map< Node, std::vector< PairNodes > > d_split_cache;
  //bool checkStarPlus( Node t );
  void simplifyPRegExp( Node s, Node r, std::vector< Node > &new_nodes );
  void simplifyNRegExp( Node s, Node r, std::vector< Node > &new_nodes );
  std::string niceChar( Node r );
  int gcd ( int a, int b );
  Node mkAllExceptOne( char c );

  void getCharSet( Node r, std::set<unsigned> &pcset, SetNodes &pvset );
  Node intersectInternal( Node r1, Node r2, std::map< unsigned, std::set< PairNodes > > cache, bool &spflag );
  void firstChars( Node r, std::set<unsigned> &pcset, SetNodes &pvset );

  //TODO: for intersection
  bool follow( Node r, CVC4::String c, std::vector< char > &vec_chars );

public:
  RegExpOpr();

  bool checkConstRegExp( Node r );
  void simplify(Node t, std::vector< Node > &new_nodes, bool polarity);
  int delta( Node r, Node &exp );
  int derivativeS( Node r, CVC4::String c, Node &retNode );
  Node derivativeSingle( Node r, CVC4::String c );
  bool guessLength( Node r, int &co );
  Node intersect(Node r1, Node r2, bool &spflag);
  Node complement(Node r, int &ret);
  void splitRegExp(Node r, std::vector< PairNodes > &pset);

  std::string mkString( Node r );
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__REGEXP__OPERATION_H */
