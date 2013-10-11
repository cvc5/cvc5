/*********************                                                        */
/*! \file theory_strings_rewriter.cpp
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2013-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of strings.
 **
 ** Implementation of the theory of strings.
 **/
#include "theory/strings/theory_strings_rewriter.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

Node TheoryStringsRewriter::rewriteConcatString(TNode node) {
    Trace("strings-prerewrite") << "Strings::rewriteConcatString start " << node << std::endl;
    Node retNode = node;
    std::vector<Node> node_vec;
    Node preNode = Node::null();
    for(unsigned int i=0; i<node.getNumChildren(); ++i) {
        Node tmpNode = node[i];
        if(node[i].getKind() == kind::STRING_CONCAT) {
            tmpNode = rewriteConcatString(node[i]);
            if(tmpNode.getKind() == kind::STRING_CONCAT) {
                unsigned int j=0;
                if(!preNode.isNull()) {
                    if(tmpNode[0].isConst()) {
                        preNode = NodeManager::currentNM()->mkConst( preNode.getConst<String>().concat( tmpNode[0].getConst<String>() ) );
                        node_vec.push_back( preNode );
                        preNode = Node::null();
                        ++j;
                    } else {
                        node_vec.push_back( preNode );
                        preNode = Node::null();
                        node_vec.push_back( tmpNode[0] );
                        ++j;
                    }
                }
                for(; j<tmpNode.getNumChildren() - 1; ++j) {
                    node_vec.push_back( tmpNode[j] );
                }
                tmpNode = tmpNode[j];
            }
        }
        if(!tmpNode.isConst()) {
            if(preNode != Node::null()) {
                if(preNode.getKind() == kind::CONST_STRING && preNode.getConst<String>().isEmptyString() ) {
                    preNode = Node::null();
                } else {
                    node_vec.push_back( preNode );
                    preNode = Node::null();
                }
            }
            node_vec.push_back( tmpNode );
        } else {
            if(preNode.isNull()) {
                preNode = tmpNode;
            } else {
                preNode = NodeManager::currentNM()->mkConst( preNode.getConst<String>().concat( tmpNode.getConst<String>() ) );
            }
        }
    }
    if(preNode != Node::null()) {
        node_vec.push_back( preNode );
    }
    if(node_vec.size() > 1) {
        retNode = NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, node_vec);
    } else {
        retNode = node_vec[0];
    }
    Trace("strings-prerewrite") << "Strings::rewriteConcatString end " << retNode << std::endl;
    return retNode;
}

void TheoryStringsRewriter::simplifyRegExp( Node s, Node r, std::vector< Node > &ret ) {
	int k = r.getKind();
	switch( k ) {
		case kind::STRING_TO_REGEXP:
		{
			Node eq = NodeManager::currentNM()->mkNode( kind::EQUAL, s, r[0] );
			ret.push_back( eq );
		}
			break;
		case kind::REGEXP_CONCAT:
		{
			std::vector< Node > cc;
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				Node sk = NodeManager::currentNM()->mkSkolem( "recsym_$$", s.getType(), "created for regular expression concat" );
				simplifyRegExp( sk, r[i], ret );
				cc.push_back( sk );
			}
			Node cc_eq = NodeManager::currentNM()->mkNode( kind::EQUAL, s, 
						NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, cc ) );
			ret.push_back( cc_eq );
		}
			break;
		case kind::REGEXP_OR:
		{
			std::vector< Node > c_or;
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				simplifyRegExp( s, r[i], c_or );
			}
			Node eq = NodeManager::currentNM()->mkNode( kind::OR, c_or );
			ret.push_back( eq );
		}
			break;
		case kind::REGEXP_INTER:
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				simplifyRegExp( s, r[i], ret );
			}
			break;
		case kind::REGEXP_STAR:
		{
			Node eq = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, s, r );
			ret.push_back( eq );
		}
			break;
		default:
			//TODO: special sym: sigma, none, all
			Trace("strings-prerewrite") << "Unsupported term: " << r << " in simplifyRegExp." << std::endl;
			Assert( false );
			break;
	}
}
bool TheoryStringsRewriter::checkConstRegExp( Node t ) {
	if( t.getKind() != kind::STRING_TO_REGEXP ) {
		for( unsigned i = 0; i<t.getNumChildren(); ++i ) {
			if( !checkConstRegExp(t[i]) ) return false;
		}
		return true;
	} else {
		if( t[0].getKind() == kind::CONST_STRING ) {
			return true;
		} else {
			return false;
		}
	}
}

bool TheoryStringsRewriter::testConstStringInRegExp( CVC4::String &s, unsigned int index_start, Node r ) {
	Assert( index_start <= s.size() );
	int k = r.getKind();
	switch( k ) {
		case kind::STRING_TO_REGEXP:
		{
			CVC4::String s2 = s.substr( index_start, s.size() - index_start );
			if(r[0].getKind() == kind::CONST_STRING) {
				return ( s2 == r[0].getConst<String>() );
			} else {
				Assert( false, "RegExp contains variable" );
			}
		}
		case kind::REGEXP_CONCAT:
		{
			if( s.size() != index_start ) {
				std::vector<int> vec_k( r.getNumChildren(), -1 );
				int start = 0;
				int left = (int) s.size();
				int i=0;
				while( i<(int) r.getNumChildren() ) {
					bool flag = true;
					if( i == (int) r.getNumChildren() - 1 ) {
						if( testConstStringInRegExp( s, index_start + start, r[i] ) ) {
							return true;
						}
					} else if( i == -1 ) {
						return false;
					} else {
						for(vec_k[i] = vec_k[i] + 1; vec_k[i] <= left; ++vec_k[i]) {
							CVC4::String t = s.substr(index_start + start, vec_k[i]);
							if( testConstStringInRegExp( t, 0, r[i] ) ) {
								start += vec_k[i]; left -= vec_k[i]; flag = false;
								++i; vec_k[i] = -1;
								break;
							}
						}
					}

					if(flag) {
						--i;
						if(i >= 0) {
							start -= vec_k[i]; left += vec_k[i];
						}
					}
				}
				return false;
			} else {
				return true;
			}
		}
		case kind::REGEXP_OR:
		{
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				if(testConstStringInRegExp( s, index_start, r[i] )) return true;
			}
			return false;
		}
		case kind::REGEXP_INTER:
		{
			for(unsigned i=0; i<r.getNumChildren(); ++i) {
				if(!testConstStringInRegExp( s, index_start, r[i] )) return false;
			}
			return true;
		}
		case kind::REGEXP_STAR:
		{
			if( s.size() != index_start ) {
				for(unsigned int k=s.size() - index_start; k>0; --k) {
					CVC4::String t = s.substr(index_start, k);
					if( testConstStringInRegExp( t, 0, r[0] ) ) {
						if( index_start + k == s.size() || testConstStringInRegExp( s, index_start + k, r ) ) {
							return true;
						}
					}
				}
				return false;
			} else {
				return true;
			}
		}
		default:
			//TODO: special sym: sigma, none, all
			Trace("strings-postrewrite") << "Unsupported term: " << r << " in testConstStringInRegExp." << std::endl;
			Assert( false );
			return false;
	}
}
Node TheoryStringsRewriter::rewriteMembership(TNode node) {
	Node retNode;

    //Trace("strings-postrewrite") << "Strings::rewriteMembership start " << node << std::endl;
	
	Node x;
	if(node[0].getKind() == kind::STRING_CONCAT) {
		x = rewriteConcatString(node[0]);
	} else {
		x = node[0];
	}

	if( x.getKind() == kind::CONST_STRING && checkConstRegExp(node[1]) ) {
		//TODO x \in R[y]
		//test whether x in node[1]
		CVC4::String s = x.getConst<String>();
		retNode = NodeManager::currentNM()->mkConst( testConstStringInRegExp( s, 0, node[1] ) );
	} else {
		if( node[1].getKind() == kind::REGEXP_STAR ) {
			if( x == node[0] ) {
				retNode = node;
			} else {
				retNode = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, x, node[1] );
			}
		} else {
			std::vector<Node> node_vec;
			simplifyRegExp( x, node[1], node_vec );

			if(node_vec.size() > 1) {
				retNode = NodeManager::currentNM()->mkNode(kind::AND, node_vec);
			} else {
				retNode = node_vec[0];
			}
		}
	}
    //Trace("strings-prerewrite") << "Strings::rewriteMembership end " << retNode << std::endl;
    return retNode;
}

RewriteResponse TheoryStringsRewriter::postRewrite(TNode node) {
  Trace("strings-postrewrite") << "Strings::postRewrite start " << node << std::endl;
  Node retNode = node;
  Node orig = retNode;

    if(node.getKind() == kind::STRING_CONCAT) {
        retNode = rewriteConcatString(node);
    } else if(node.getKind() == kind::EQUAL) {
        Node leftNode  = node[0];
        if(node[0].getKind() == kind::STRING_CONCAT) {
            leftNode = rewriteConcatString(node[0]);
        }
        Node rightNode = node[1];
        if(node[1].getKind() == kind::STRING_CONCAT) {
            rightNode = rewriteConcatString(node[1]);
        }

        if(leftNode == rightNode) {
            retNode = NodeManager::currentNM()->mkConst(true);
        } else if(leftNode.isConst() && rightNode.isConst()) {
            retNode = NodeManager::currentNM()->mkConst(false);
        } else if(leftNode > rightNode) {
            retNode = NodeManager::currentNM()->mkNode(kind::EQUAL, rightNode, leftNode);
        } else if( leftNode != node[0] || rightNode != node[1]) {
            retNode = NodeManager::currentNM()->mkNode(kind::EQUAL, leftNode, rightNode);
        }
    } else if(node.getKind() == kind::STRING_LENGTH) {
        if(node[0].isConst()) {
            retNode = NodeManager::currentNM()->mkConst( ::CVC4::Rational( node[0].getConst<String>().size() ) );
        } else if(node[0].getKind() == kind::STRING_CONCAT) {
            Node tmpNode = rewriteConcatString(node[0]);
            if(tmpNode.isConst()) {
                retNode = NodeManager::currentNM()->mkConst( ::CVC4::Rational( tmpNode.getConst<String>().size() ) );
            } else {
                // it has to be string concat
                std::vector<Node> node_vec;
                for(unsigned int i=0; i<tmpNode.getNumChildren(); ++i) {
                    if(tmpNode[i].isConst()) {
                        node_vec.push_back( NodeManager::currentNM()->mkConst( ::CVC4::Rational( tmpNode[i].getConst<String>().size() ) ) );
                    } else {
                        node_vec.push_back( NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, tmpNode[i]) );
                    }
                }
                retNode = NodeManager::currentNM()->mkNode(kind::PLUS, node_vec);
            }
        }
    } else if(node.getKind() == kind::STRING_SUBSTR) {
		if( node[0].isConst() && node[1].isConst() && node[2].isConst() ) {
			int i = node[1].getConst<Rational>().getNumerator().toUnsignedInt();
			int j = node[2].getConst<Rational>().getNumerator().toUnsignedInt();
			if( node[0].getConst<String>().size() >= (unsigned) (i + j) ) {
				retNode = NodeManager::currentNM()->mkConst( node[0].getConst<String>().substr(i, j) );
			} else {
				// TODO: some issues, must be guarded by users
				retNode = NodeManager::currentNM()->mkConst( false );
			}
		} else {
			//handled by preprocess
		}
	} else if(node.getKind() == kind::STRING_IN_REGEXP) {
		retNode = rewriteMembership(node);
	}

  Trace("strings-postrewrite") << "Strings::postRewrite returning " << retNode << std::endl;
  return RewriteResponse(orig==retNode ? REWRITE_DONE : REWRITE_AGAIN_FULL, retNode);
}

RewriteResponse TheoryStringsRewriter::preRewrite(TNode node) {
    Node retNode = node;
	Node orig = retNode;
    Trace("strings-prerewrite") << "Strings::preRewrite start " << node << std::endl;

    if(node.getKind() == kind::STRING_CONCAT) {
        retNode = rewriteConcatString(node);
    } else if(node.getKind() == kind::REGEXP_PLUS) {
		retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, node[0],
					NodeManager::currentNM()->mkNode( kind::REGEXP_STAR, node[0]));
	} else if(node.getKind() == kind::REGEXP_OPT) {
		retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_OR,
					NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String("") ) ),
					node[0]);
	}

    Trace("strings-prerewrite") << "Strings::preRewrite returning " << retNode << std::endl;
    return RewriteResponse(orig==retNode ? REWRITE_DONE : REWRITE_AGAIN_FULL, retNode);
}
