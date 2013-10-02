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
                if(preNode.getKind() == kind::CONST_STRING && preNode.getConst<String>().toString()=="" ) {
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

RewriteResponse TheoryStringsRewriter::postRewrite(TNode node) {
  Trace("strings-postrewrite") << "Strings::postRewrite start " << node << std::endl;
  Node retNode = node;

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
    } else if(node.getKind() == kind::STRING_IN_REGEXP) {
        Node leftNode  = node[0];
        if(node[0].getKind() == kind::STRING_CONCAT) {
            leftNode = rewriteConcatString(node[0]);
        }
        // TODO: right part
        Node rightNode = node[1];
        // merge
        if( leftNode != node[0] || rightNode != node[1]) {
            retNode = NodeManager::currentNM()->mkNode(kind::STRING_IN_REGEXP, leftNode, rightNode);
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
	}

  Trace("strings-postrewrite") << "Strings::postRewrite returning " << node << std::endl;
  return RewriteResponse(REWRITE_DONE, retNode);
}

RewriteResponse TheoryStringsRewriter::preRewrite(TNode node) {
    Node retNode = node;
    Trace("strings-prerewrite") << "Strings::preRewrite start " << node << std::endl;

    if(node.getKind() == kind::STRING_CONCAT) {
        retNode = rewriteConcatString(node);
    }

    Trace("strings-prerewrite") << "Strings::preRewrite returning " << retNode << std::endl;
    return RewriteResponse(REWRITE_DONE, retNode);
}
