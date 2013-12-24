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
 ** \brief Regular Expression Operations
 **
 ** Regular Expression Operations
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__REGEXP__OPERATION_H
#define __CVC4__THEORY__STRINGS__REGEXP__OPERATION_H

#include <vector>
#include "util/hash.h"
#include "theory/theory.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace strings {

class RegExpOpr {
	typedef std::pair< Node, CVC4::String > PairDvStr;
private:
    Node d_emptyString;
	char d_char_start;
	char d_char_end;
	Node d_sigma;
	Node d_sigma_star;
	
	std::map< Node, Node > d_compl_cache;
	std::map< Node, int > d_delta_cache;
	std::map< PairDvStr, Node > d_dv_cache;
	std::map< Node, bool > d_cstre_cache;
	//bool checkStarPlus( Node t );
	//void simplifyRegExp( Node s, Node r, std::vector< Node > &ret, std::vector< Node > &nn );
	//Node simplify( Node t, std::vector< Node > &new_nodes );
	std::string niceChar( Node r );
	int gcd ( int a, int b );

public:
	RegExpOpr();
	bool checkConstRegExp( Node r );
    //void simplify(std::vector< Node > &vec_node);
	Node mkAllExceptOne( char c );
	Node complement( Node r );
	int delta( Node r );
	Node derivativeSingle( Node r, CVC4::String c );
	bool guessLength( Node r, int &co );
	void firstChar( Node r );
	bool follow( Node r, CVC4::String c, std::vector< char > &vec_chars );
	std::string mkString( Node r );
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__REGEXP__OPERATION_H */
