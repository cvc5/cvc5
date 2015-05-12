/*********************                                                        */
/*! \file theory_strings_rewriter.cpp
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of the theory of strings.
 **
 ** Implementation of the theory of strings.
 **/
#include "theory/strings/theory_strings_rewriter.h"
#include "theory/strings/options.h"
#include "smt/logic_exception.h"
#include <stdint.h>

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

Node TheoryStringsRewriter::rewriteConcatString( TNode node ) {
  Trace("strings-prerewrite") << "Strings::rewriteConcatString start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  Node preNode = Node::null();
  for(unsigned int i=0; i<node.getNumChildren(); ++i) {
    Node tmpNode = node[i];
    if(node[i].getKind() == kind::STRING_CONCAT) {
      tmpNode = rewriteConcatString(node[i]);
      if(tmpNode.getKind() == kind::STRING_CONCAT) {
        unsigned j=0;
        if(!preNode.isNull()) {
          if(tmpNode[0].isConst()) {
            preNode = NodeManager::currentNM()->mkConst( preNode.getConst<String>().concat( tmpNode[0].getConst<String>() ) );
            node_vec.push_back( preNode );
            preNode = Node::null();
          } else {
            node_vec.push_back( preNode );
            preNode = Node::null();
            node_vec.push_back( tmpNode[0] );
          }
          ++j;
        }
        for(; j<tmpNode.getNumChildren() - 1; ++j) {
          node_vec.push_back( tmpNode[j] );
        }
        tmpNode = tmpNode[j];
      }
    }
    if(!tmpNode.isConst()) {
      if(!preNode.isNull()) {
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

Node TheoryStringsRewriter::concatTwoNodes(TNode n1, TNode n2) {
  Assert(n1.getKind() != kind::REGEXP_CONCAT);
  TNode tmp = n2.getKind() == kind::REGEXP_CONCAT ? n2[0] : n2;
  if(n1.getKind() == kind::STRING_TO_REGEXP && tmp.getKind() == kind::STRING_TO_REGEXP) {
    tmp = NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, n1[0], tmp[0] );
    tmp = rewriteConcatString( tmp );
    tmp = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, tmp );
  } else {
    tmp = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, n1, tmp );
  }
  Node retNode = tmp;
  if(n2.getKind() == kind::REGEXP_CONCAT) {
    std::vector<Node> vec;
    if(tmp.getKind() != kind::REGEXP_CONCAT) {
      vec.push_back(retNode);
    } else {
      vec.push_back(retNode[0]);
      vec.push_back(retNode[1]);
    }
    for(unsigned j=1; j<n2.getNumChildren(); j++) {
      vec.push_back(n2[j]);
    }
    retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, vec );
  }
  Trace("regexp-ax-debug") << "Regexp::AX::concatTwoNodes: (" << n1 << ", " << n2 << ") -> " << retNode << std::endl;
  return retNode;
}

void TheoryStringsRewriter::unionAndConcat(std::vector<Node> &vec_nodes, Node node) {
  if(vec_nodes.empty()) {
    vec_nodes.push_back(node);
  } else {
    Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
    if(node != emptysingleton) {
      for(unsigned i=0; i<vec_nodes.size(); i++) {
        if(vec_nodes[i].getKind() == kind::REGEXP_CONCAT) {
          std::vector<Node> vec2;
          for(unsigned j=0; j<vec_nodes[i].getNumChildren() - 1; j++) {
            vec2.push_back(vec_nodes[i][j]);
          }
          TNode tmp = vec_nodes[i][vec_nodes[i].getNumChildren() - 1];
          tmp = concatTwoNodes(tmp, node);
          if(tmp.getKind() == kind::REGEXP_CONCAT) {
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              vec2.push_back(tmp[j]);
            }
          } else {
            vec2.push_back(tmp);
          }
          Assert(vec2.size() > 1);
          vec_nodes[i] = NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, vec2);
        } else if(vec_nodes[i].getKind() == kind::REGEXP_EMPTY) {
          //do nothing
        } else if(vec_nodes[i] == emptysingleton) {
          vec_nodes[i] = node;
        } else if(vec_nodes[i].getKind() == kind::STRING_TO_REGEXP) {
          vec_nodes[i] = concatTwoNodes(vec_nodes[i], node);
        } else {
          vec_nodes[i] = NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, vec_nodes[i], node);
        }
      }
    }
  }
}

void TheoryStringsRewriter::mergeInto(std::vector<Node> &t, const std::vector<Node> &s) {
  for(std::vector<Node>::const_iterator itr=s.begin(); itr!=s.end(); itr++) {
    if(std::find(t.begin(), t.end(), (*itr)) == t.end()) {
      t.push_back( *itr );
    }
  }
}

void TheoryStringsRewriter::shrinkConVec(std::vector<Node> &vec) {
  unsigned i = 0;
  Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
  while(i < vec.size()) {
    if( vec[i] == emptysingleton ) {
      vec.erase(vec.begin() + i);
    } else if(vec[i].getKind()==kind::STRING_TO_REGEXP && i<vec.size()-1 && vec[i+1].getKind()==kind::STRING_TO_REGEXP) {
      Node tmp = NodeManager::currentNM()->mkNode(kind::STRING_CONCAT, vec[i][0], vec[i+1][0]);
      tmp = rewriteConcatString(tmp);
      vec[i] = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, tmp);
      vec.erase(vec.begin() + i + 1);
    } else {
      i++;
    }
  }
}

Node TheoryStringsRewriter::applyAX( TNode node ) {
  Trace("regexp-ax") << "Regexp::AX start " << node << std::endl;
  Node retNode = node;

  int k = node.getKind();
  switch( k ) {
    case kind::REGEXP_UNION: {
      std::vector<Node> vec_nodes;
      for(unsigned i=0; i<node.getNumChildren(); i++) {
        Node tmp = applyAX(node[i]);
        if(tmp.getKind() == kind::REGEXP_UNION) {
          for(unsigned j=0; j<tmp.getNumChildren(); j++) {
            if(std::find(vec_nodes.begin(), vec_nodes.end(), tmp[j]) == vec_nodes.end()) {
              vec_nodes.push_back(tmp[j]);
            }
          }
        } else if(tmp.getKind() == kind::REGEXP_EMPTY) {
          // do nothing
        } else {
          if(std::find(vec_nodes.begin(), vec_nodes.end(), tmp) == vec_nodes.end()) {
            vec_nodes.push_back(tmp);
          }
        }
      }
      if(vec_nodes.empty()) {
        std::vector< Node > nvec;
        retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
      } else {
        retNode = vec_nodes.size() == 1 ? vec_nodes[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
      }
      break;
    }
    case kind::REGEXP_CONCAT: {
      std::vector< std::vector<Node> > vec_nodes;
      bool emptyflag = false;
      Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
      for(unsigned i=0; i<node.getNumChildren(); i++) {
        Node tmp = applyAX(node[i]);
        if(tmp.getKind() == kind::REGEXP_EMPTY) {
          emptyflag = true;
          break;
        } else if(tmp == emptysingleton) {
          //do nothing
        } else if(vec_nodes.empty()) {
          if(tmp.getKind() == kind::REGEXP_UNION) {
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              std::vector<Node> vtmp;
              if(tmp[j].getKind() == kind::REGEXP_CONCAT) {
                for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                  vtmp.push_back(tmp[j][j2]);
                }
              } else {
                vtmp.push_back(tmp[j]);
              }
              vec_nodes.push_back(vtmp);
            }
          } else if(tmp.getKind() == kind::REGEXP_CONCAT) {
            std::vector<Node> vtmp;
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              vtmp.push_back(tmp[j]);
            }
            vec_nodes.push_back(vtmp);
          } else {
            std::vector<Node> vtmp;
            vtmp.push_back(tmp);
            vec_nodes.push_back(vtmp);
          }
        } else {
          //non-empty vec
          if(tmp.getKind() == kind::REGEXP_UNION) {
            unsigned cnt = vec_nodes.size();
            for(unsigned i2=0; i2<cnt; i2++) {
              //std::vector<Node> vleft( vec_nodes[i2] );
              for(unsigned j=0; j<tmp.getNumChildren(); j++) {
                if(tmp[j] == emptysingleton) {
                  vec_nodes.push_back( vec_nodes[i2] );
                } else {
                  std::vector<Node> vt( vec_nodes[i2] );
                  if(tmp[j].getKind() != kind::REGEXP_CONCAT) {
                    vt.push_back( tmp[j] );
                  } else {
                    for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                      vt.push_back(tmp[j][j2]);
                    }
                  }
                  vec_nodes.push_back(vt);
                }
              }
            }
            vec_nodes.erase(vec_nodes.begin(), vec_nodes.begin() + cnt);
          } else if(tmp.getKind() == kind::REGEXP_CONCAT) {
            for(unsigned i2=0; i2<vec_nodes.size(); i2++) {
              for(unsigned j=0; j<tmp.getNumChildren(); j++) {
                vec_nodes[i2].push_back(tmp[j]);
              }
            }
          } else {
            for(unsigned i2=0; i2<vec_nodes.size(); i2++) {
              vec_nodes[i2].push_back(tmp);
            }
          }
        }
      }
      if(emptyflag) {
        std::vector< Node > nvec;
        retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
      } else if(vec_nodes.empty()) {
        retNode = emptysingleton;
      } else if(vec_nodes.size() == 1) {
        shrinkConVec(vec_nodes[0]);
        retNode = vec_nodes[0].empty()? emptysingleton 
          : vec_nodes[0].size()==1? vec_nodes[0][0] 
          : NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes[0]);
      } else {
        std::vector<Node> vtmp;
        for(unsigned i=0; i<vec_nodes.size(); i++) {
          shrinkConVec(vec_nodes[i]);
          if(!vec_nodes[i].empty()) {
            Node ntmp = vec_nodes[i].size()==1? vec_nodes[i][0] 
              : NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes[i]);
            vtmp.push_back(ntmp);
          }
        }
        retNode = vtmp.empty()? emptysingleton
          : vtmp.size()==1? vtmp[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vtmp);
      }
      break;
    }
    case kind::REGEXP_STAR: {
      Node tmp = applyAX(node[0]);
      Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
      if(tmp.getKind() == kind::REGEXP_EMPTY || tmp == emptysingleton) {
        retNode = emptysingleton;
      } else {
        if(tmp.getKind() == kind::REGEXP_UNION) {
          std::vector<Node> vec;
          for(unsigned i=0; i<tmp.getNumChildren(); i++) {
            if(tmp[i] != emptysingleton) {
              vec.push_back(tmp[i]);
            }
          }
          if(vec.size() != tmp.getNumChildren()) {
            tmp = vec.size()==1? vec[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec) ;
          }
        } else if(tmp.getKind() == kind::REGEXP_STAR) {
          tmp = tmp[0];
        }
        if(tmp != node[0]) {
          retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_STAR, tmp );
        }
      }
      break;
    }
    case kind::REGEXP_INTER: {
      std::vector< std::vector<Node> > vec_nodes;
      bool emptyflag = false;
      bool epsflag = false;
      Node emptysingleton = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( CVC4::String("") ) );
      for(unsigned i=0; i<node.getNumChildren(); i++) {
        Node tmp = applyAX(node[i]);
        if(tmp.getKind() == kind::REGEXP_EMPTY) {
          emptyflag = true;
          break;
        } else if(vec_nodes.empty()) {
          if(tmp.getKind() == kind::REGEXP_INTER) {
            std::vector<Node> vtmp;
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              vtmp.push_back(tmp[j]);
            }
            vec_nodes.push_back(vtmp);
          } else if(tmp.getKind() == kind::REGEXP_UNION) {
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              std::vector<Node> vtmp;
              if(tmp[j].getKind() == kind::REGEXP_INTER) {
                for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                  vtmp.push_back(tmp[j][j2]);
                }
              } else {
                vtmp.push_back(tmp[j]);
              }
              vec_nodes.push_back(vtmp);
            }
          } else {
            if(tmp == emptysingleton) {
              epsflag = true;
            }
            std::vector<Node> vtmp;
            vtmp.push_back(tmp);
            vec_nodes.push_back(vtmp);
          }
        } else {
          //non-empty vec
          if(tmp.getKind() == kind::REGEXP_INTER) {
            for(unsigned j=0; j<tmp.getNumChildren(); j++) {
              for(unsigned i2=0; i2<vec_nodes.size(); i2++) {
                if(std::find(vec_nodes[i2].begin(), vec_nodes[i2].end(), tmp[j]) == vec_nodes[i2].end()) {
                  vec_nodes[i2].push_back(tmp[j]);
                }
              }
            }
          } else if(tmp == emptysingleton) {
            if(!epsflag) {
              epsflag = true;
              for(unsigned j=0; j<vec_nodes.size(); j++) {
                vec_nodes[j].insert(vec_nodes[j].begin(), emptysingleton);
              }
            }
          } else if(tmp.getKind() == kind::REGEXP_UNION) {
            unsigned cnt = vec_nodes.size();
            for(unsigned i2=0; i2<cnt; i2++) {
              //std::vector<Node> vleft( vec_nodes[i2] );
              for(unsigned j=0; j<tmp.getNumChildren(); j++) {
                std::vector<Node> vt(vec_nodes[i2]);
                if(tmp[j].getKind() != kind::REGEXP_INTER) {
                  if(std::find(vt.begin(), vt.end(), tmp[j]) == vt.end()) {
                    vt.push_back(tmp[j]);
                  }
                } else {
                  std::vector<Node> vtmp;
                  for(unsigned j2=0; j2<tmp[j].getNumChildren(); j2++) {
                    vtmp.push_back(tmp[j][j2]);
                  }
                  mergeInto(vt, vtmp);
                }
                vec_nodes.push_back(vt);
              }
            }
            vec_nodes.erase(vec_nodes.begin(), vec_nodes.begin() + cnt);
          } else {
            for(unsigned j=0; j<vec_nodes.size(); j++) {
              if(std::find(vec_nodes[j].begin(), vec_nodes[j].end(), tmp) == vec_nodes[j].end()) {
                vec_nodes[j].push_back(tmp);
              }
            }
          }
        }
      }
      if(emptyflag) {
        std::vector< Node > nvec;
        retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
      } else if(vec_nodes.empty()) {
        //to check?
        retNode = emptysingleton;
      } else if(vec_nodes.size() == 1) {
        retNode = vec_nodes[0].empty() ? emptysingleton : vec_nodes[0].size() == 1 ? vec_nodes[0][0] : NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, vec_nodes[0] );
      } else {
        std::vector<Node> vtmp;
        for(unsigned i=0; i<vec_nodes.size(); i++) {
          Node tmp = vec_nodes[i].empty()? emptysingleton : vec_nodes[i].size() == 1 ? vec_nodes[i][0] : NodeManager::currentNM()->mkNode( kind::REGEXP_INTER, vec_nodes[i] );
          vtmp.push_back(tmp);
        }
        retNode = vtmp.size() == 1? vtmp[0] : NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vtmp );
      }
      break;
    }
/*    case kind::REGEXP_UNION: {
      break;
    }
    case kind::REGEXP_UNION: {
      break;
    }*/
    case kind::REGEXP_SIGMA: {
      break;
    }
    case kind::REGEXP_EMPTY: {
      break;
    }
    //default: {
      //to check?
    //}
  }

  Trace("regexp-ax") << "Regexp::AX end " << node << " to\n               " << retNode << std::endl;
  return retNode;
}

Node TheoryStringsRewriter::prerewriteConcatRegExp( TNode node ) {
  Assert( node.getKind() == kind::REGEXP_CONCAT );
  Trace("strings-prerewrite") << "Strings::prerewriteConcatRegExp start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  Node preNode = Node::null();
  bool emptyflag = false;
  for(unsigned int i=0; i<node.getNumChildren(); ++i) {
    Trace("strings-prerewrite") << "Strings::prerewriteConcatRegExp preNode: " << preNode << std::endl;
    Node tmpNode = node[i];
    if(tmpNode.getKind() == kind::REGEXP_CONCAT) {
      tmpNode = prerewriteConcatRegExp(node[i]);
      if(tmpNode.getKind() == kind::REGEXP_CONCAT) {
        unsigned j=0;
        if(!preNode.isNull()) {
          if(tmpNode[0].getKind() == kind::STRING_TO_REGEXP) {
            preNode = rewriteConcatString(
              NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, preNode, tmpNode[0][0] ) );
            node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
            preNode = Node::null();
          } else {
            node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
            preNode = Node::null();
            node_vec.push_back( tmpNode[0] );
          }
          ++j;
        }
        for(; j<tmpNode.getNumChildren() - 1; ++j) {
          node_vec.push_back( tmpNode[j] );
        }
        tmpNode = tmpNode[j];
      }
    }
    if( tmpNode.getKind() == kind::STRING_TO_REGEXP ) {
      if(preNode.isNull()) {
        preNode = tmpNode[0];
      } else {
        preNode = rewriteConcatString(
        NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, preNode, tmpNode[0] ) );
      }
    } else if( tmpNode.getKind() == kind::REGEXP_EMPTY ) {
      emptyflag = true;
      break;
    } else {
      if(!preNode.isNull()) {
        if(preNode.getKind() == kind::CONST_STRING && preNode.getConst<String>().isEmptyString() ) {
          preNode = Node::null();
        } else {
          node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
          preNode = Node::null();
        }
      }
      node_vec.push_back( tmpNode );
    }
  }
  if(emptyflag) {
    std::vector< Node > nvec;
    retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec );
  } else {
    if(!preNode.isNull()) {
      bool bflag = (preNode.getKind() == kind::CONST_STRING && preNode.getConst<String>().isEmptyString() );
      if(node_vec.empty() || !bflag ) {
        node_vec.push_back( NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, preNode ) );
      }
    }
    if(node_vec.size() > 1) {
      retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, node_vec);
    } else {
      retNode = node_vec[0];
    }
  }
  Trace("strings-prerewrite") << "Strings::prerewriteConcatRegExp end " << retNode << std::endl;
  return retNode;
}

Node TheoryStringsRewriter::prerewriteOrRegExp(TNode node) {
  Assert( node.getKind() == kind::REGEXP_UNION );
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  bool allflag = false;
  for(unsigned i=0; i<node.getNumChildren(); ++i) {
    if(node[i].getKind() == kind::REGEXP_UNION) {
      Node tmpNode = prerewriteOrRegExp( node[i] );
      if(tmpNode.getKind() == kind::REGEXP_UNION) {
        for(unsigned int j=0; j<tmpNode.getNumChildren(); ++j) {
          if(std::find(node_vec.begin(), node_vec.end(), tmpNode[j]) == node_vec.end()) {
            if(std::find(node_vec.begin(), node_vec.end(), tmpNode[j]) == node_vec.end()) {
              node_vec.push_back( tmpNode[j] );
            }
          }
        }
      } else if(tmpNode.getKind() == kind::REGEXP_EMPTY) {
        //nothing
      } else if(tmpNode.getKind() == kind::REGEXP_STAR && tmpNode[0].getKind() == kind::REGEXP_SIGMA) {
        allflag = true;
        retNode = tmpNode;
        break;
      } else {
        if(std::find(node_vec.begin(), node_vec.end(), tmpNode) == node_vec.end()) {
          node_vec.push_back( tmpNode );
        }
      }
    } else if(node[i].getKind() == kind::REGEXP_EMPTY) {
      //nothing
    } else if(node[i].getKind() == kind::REGEXP_STAR && node[i][0].getKind() == kind::REGEXP_SIGMA) {
      allflag = true;
      retNode = node[i];
      break;
    } else {
      if(std::find(node_vec.begin(), node_vec.end(), node[i]) == node_vec.end()) {
        node_vec.push_back( node[i] );
      }
    }
  }
  if(!allflag) {
    std::vector< Node > nvec;
    retNode = node_vec.size() == 0 ? NodeManager::currentNM()->mkNode( kind::REGEXP_EMPTY, nvec ) :
          node_vec.size() == 1 ? node_vec[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, node_vec);
  }
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp end " << retNode << std::endl;
  return retNode;
}

Node TheoryStringsRewriter::prerewriteAndRegExp(TNode node) {
  Assert( node.getKind() == kind::REGEXP_INTER );
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp start " << node << std::endl;
  Node retNode = node;
  std::vector<Node> node_vec;
  bool emptyflag = false;
  //Node allNode = Node::null();
  for(unsigned i=0; i<node.getNumChildren(); ++i) {
    if(node[i].getKind() == kind::REGEXP_INTER) {
      Node tmpNode = prerewriteAndRegExp( node[i] );
      if(tmpNode.getKind() == kind::REGEXP_INTER) {
        for(unsigned int j=0; j<tmpNode.getNumChildren(); ++j) {
          if(std::find(node_vec.begin(), node_vec.end(), tmpNode[j]) == node_vec.end()) {
            node_vec.push_back( tmpNode[j] );
          }
        }
      } else if(tmpNode.getKind() == kind::REGEXP_EMPTY) {
        emptyflag = true;
        retNode = tmpNode;
        break;
      } else if(tmpNode.getKind() == kind::REGEXP_STAR && tmpNode[0].getKind() == kind::REGEXP_SIGMA) {
        //allNode = tmpNode;
      } else {
        if(std::find(node_vec.begin(), node_vec.end(), tmpNode) == node_vec.end()) {
          node_vec.push_back( tmpNode );
        }
      }
    } else if(node[i].getKind() == kind::REGEXP_EMPTY) {
      emptyflag = true;
      retNode = node[i];
      break;
    } else if(node[i].getKind() == kind::REGEXP_STAR && node[i][0].getKind() == kind::REGEXP_SIGMA) {
      //allNode = node[i];
    } else {
      if(std::find(node_vec.begin(), node_vec.end(), node[i]) == node_vec.end()) {
        node_vec.push_back( node[i] );
      }
    }
  }
  if(!emptyflag) {
    std::vector< Node > nvec;
    retNode = node_vec.size() == 0 ? 
          NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, NodeManager::currentNM()->mkNode(kind::REGEXP_SIGMA, nvec)) :
          node_vec.size() == 1 ? node_vec[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_INTER, node_vec);
  }
  Trace("strings-prerewrite") << "Strings::prerewriteOrRegExp end " << retNode << std::endl;
  return retNode;
}

bool TheoryStringsRewriter::checkConstRegExp( TNode t ) {
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

bool TheoryStringsRewriter::testConstStringInRegExp( CVC4::String &s, unsigned int index_start, TNode r ) {
  Assert( index_start <= s.size() );
  Trace("regexp-debug") << "Checking " << s << " in " << r << ", starting at " << index_start << std::endl;
  int k = r.getKind();
  switch( k ) {
    case kind::STRING_TO_REGEXP: {
      CVC4::String s2 = s.substr( index_start, s.size() - index_start );
      if(r[0].getKind() == kind::CONST_STRING) {
        return ( s2 == r[0].getConst<String>() );
      } else {
        Assert( false, "RegExp contains variables" );
      }
    }
    case kind::REGEXP_CONCAT: {
      if( s.size() != index_start ) {
        std::vector<int> vec_k( r.getNumChildren(), -1 );
        int start = 0;
        int left = (int) s.size() - index_start;
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
        for(unsigned i=0; i<r.getNumChildren(); ++i) {
          if(!testConstStringInRegExp( s, index_start, r[i] )) return false;
        }
        return true;
      }
    }
    case kind::REGEXP_UNION: {
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if(testConstStringInRegExp( s, index_start, r[i] )) return true;
      }
      return false;
    }
    case kind::REGEXP_INTER: {
      for(unsigned i=0; i<r.getNumChildren(); ++i) {
        if(!testConstStringInRegExp( s, index_start, r[i] )) return false;
      }
      return true;
    }
    case kind::REGEXP_STAR: {
      if( s.size() != index_start ) {
        for(unsigned k=s.size() - index_start; k>0; --k) {
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
    case kind::REGEXP_EMPTY: {
      return false;
    }
    case kind::REGEXP_SIGMA: {
      if(s.size() == index_start + 1) {
        return true;
      } else {
        return false;
      }
    }
    case kind::REGEXP_RANGE: {
      if(s.size() == index_start + 1) {
        unsigned char a = r[0].getConst<String>().getFirstChar();
        unsigned char b = r[1].getConst<String>().getFirstChar();
        unsigned char c = s.getLastChar();
        return (a <= c && c <= b);
      } else {
        return false;
      }
    }
    case kind::REGEXP_LOOP: {
      unsigned l = r[1].getConst<Rational>().getNumerator().toUnsignedInt();
      if(s.size() == index_start) {
        return l==0? true : testConstStringInRegExp(s, index_start, r[0]);
      } else if(l==0 && r[1]==r[2]) {
        return false;
      } else {
        Assert(r.getNumChildren() == 3, "String rewriter error: LOOP has 2 childrens");
        if(l==0) {
          //R{0,u}
          unsigned u = r[2].getConst<Rational>().getNumerator().toUnsignedInt();
          for(unsigned len=s.size() - index_start; len>=1; len--) {
            CVC4::String t = s.substr(index_start, len);
            if(testConstStringInRegExp(t, 0, r[0])) {
              if(len + index_start == s.size()) {
                return true;
              } else {
                Node num2 = NodeManager::currentNM()->mkConst( CVC4::Rational(u - 1) );
                Node r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, r[0], r[1], num2);
                if(testConstStringInRegExp(s, index_start+len, r2)) {
                  return true;
                }
              }
            }
          }
          return false;
        } else {
          //R{l,l}
          Assert(r[1]==r[2], "String rewriter error: LOOP nums are not equal");
          if(l>s.size() - index_start) {
            if(testConstStringInRegExp(s, s.size(), r[0])) {
              l = s.size() - index_start;
            } else {
              return false;
            }
          }
          for(unsigned len=1; len<=s.size() - index_start; len++) {
            CVC4::String t = s.substr(index_start, len);
            if(testConstStringInRegExp(t, 0, r[0])) {
              Node num2 = NodeManager::currentNM()->mkConst( CVC4::Rational(l - 1) );
              Node r2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, r[0], num2, num2);
              if(testConstStringInRegExp(s, index_start+len, r2)) {
                return true;
              }
            }
          }
          return false;
        }
      }
    }
    default: {
      Trace("strings-error") << "Unsupported term: " << r << " in testConstStringInRegExp." << std::endl;
      Unreachable();
      return false;
    }
  }
}

Node TheoryStringsRewriter::rewriteMembership(TNode node) {
  Node retNode = node;
  Node x = node[0];
  Node r = node[1];//applyAX(node[1]);

  if(node[0].getKind() == kind::STRING_CONCAT) {
    x = rewriteConcatString(node[0]);
  }

  if(r.getKind() == kind::REGEXP_EMPTY) {
    retNode = NodeManager::currentNM()->mkConst( false );
  } else if(x.getKind()==kind::CONST_STRING && checkConstRegExp(r)) {
    //test whether x in node[1]
    CVC4::String s = x.getConst<String>();
    retNode = NodeManager::currentNM()->mkConst( testConstStringInRegExp( s, 0, r ) );
  } else if(r.getKind() == kind::REGEXP_SIGMA) {
    Node one = NodeManager::currentNM()->mkConst( ::CVC4::Rational(1) );
    retNode = one.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, x));
  } else if(r.getKind() == kind::REGEXP_STAR && r[0].getKind() == kind::REGEXP_SIGMA) {
    retNode = NodeManager::currentNM()->mkConst( true );
  } else if(r.getKind() == kind::REGEXP_CONCAT) {
    //opt
    bool flag = true;
    for(unsigned i=0; i<r.getNumChildren(); i++) {
      if(r[i].getKind() != kind::REGEXP_SIGMA) {
        flag = false;
        break;
      }
    }
    if(flag) {
      Node num = NodeManager::currentNM()->mkConst( ::CVC4::Rational( r.getNumChildren() ) );
      retNode = num.eqNode(NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, x));
    }
    //
  } else if(r.getKind() == kind::STRING_TO_REGEXP) {
    retNode = x.eqNode(r[0]);
  } else if(x != node[0] || r != node[1]) {
    retNode = NodeManager::currentNM()->mkNode( kind::STRING_IN_REGEXP, x, r );
  }
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
    } /*else if(node[0].getKind() == kind::STRING_SUBSTR_TOTAL) {
        retNode = node[0][2];
    }*/ else if(node[0].getKind() == kind::STRING_CONCAT) {
      Node tmpNode = rewriteConcatString(node[0]);
      if(tmpNode.isConst()) {
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::Rational( tmpNode.getConst<String>().size() ) );
      } /*else if(tmpNode.getKind() == kind::STRING_SUBSTR_TOTAL) {
      retNode = tmpNode[2];
      }*/ else {
        // it has to be string concat
        std::vector<Node> node_vec;
        for(unsigned int i=0; i<tmpNode.getNumChildren(); ++i) {
          if(tmpNode[i].isConst()) {
            node_vec.push_back( NodeManager::currentNM()->mkConst( ::CVC4::Rational( tmpNode[i].getConst<String>().size() ) ) );
          } else if(tmpNode[i].getKind() == kind::STRING_SUBSTR_TOTAL) {
            node_vec.push_back( tmpNode[i][2] );
          } else {
            node_vec.push_back( NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, tmpNode[i]) );
          }
        }
        retNode = NodeManager::currentNM()->mkNode(kind::PLUS, node_vec);
      }
    }
  } else if(node.getKind() == kind::STRING_SUBSTR_TOTAL) {
    Node zero = NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) );
    if(node[2] == zero) {
      retNode = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
    } else if( node[1].isConst() && node[2].isConst() ) {
      if(node[1].getConst<Rational>().sgn()>=0 && node[2].getConst<Rational>().sgn()>=0) {
        CVC4::Rational sum(node[1].getConst<Rational>() + node[2].getConst<Rational>());
        if( node[0].isConst() ) {
          CVC4::Rational size(node[0].getConst<String>().size());
          if( size >= sum ) {
            //because size is smaller than MAX_INT
            size_t i = node[1].getConst<Rational>().getNumerator().toUnsignedInt();
            size_t j = node[2].getConst<Rational>().getNumerator().toUnsignedInt();
            retNode = NodeManager::currentNM()->mkConst( node[0].getConst<String>().substr(i, j) );
          } else {
            retNode = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
          }
        } else if(node[0].getKind() == kind::STRING_CONCAT && node[0][0].isConst()) {
          CVC4::Rational size2(node[0][0].getConst<String>().size());
          if( size2 >= sum ) {
            //because size2 is smaller than MAX_INT
            size_t i = node[1].getConst<Rational>().getNumerator().toUnsignedInt();
            size_t j = node[2].getConst<Rational>().getNumerator().toUnsignedInt();
            retNode = NodeManager::currentNM()->mkConst( node[0][0].getConst<String>().substr(i, j) );
          }
        }
      } else {
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
      }
    } else if(node[1] == zero && node[2].getKind() == kind::STRING_LENGTH && node[2][0] == node[0]) {
      retNode = node[0];
    }
  } else if(node.getKind() == kind::STRING_STRCTN) {
    if( node[0] == node[1] ) {
      retNode = NodeManager::currentNM()->mkConst( true );
    } else if( node[0].isConst() && node[1].isConst() ) {
      CVC4::String s = node[0].getConst<String>();
      CVC4::String t = node[1].getConst<String>();
      if( s.find(t) != std::string::npos ) {
        retNode = NodeManager::currentNM()->mkConst( true );
      } else {
        retNode = NodeManager::currentNM()->mkConst( false );
      }
    } else if( node[0].getKind() == kind::STRING_CONCAT ) {
      if( node[1].getKind() != kind::STRING_CONCAT ){
        bool flag = false;
        for(unsigned i=0; i<node[0].getNumChildren(); i++) {
          if(node[0][i] == node[1]) {
            flag = true;
            break;
          }
        }
        if(flag) {
          retNode = NodeManager::currentNM()->mkConst( true );
        }
      } else {
        bool flag = false;
        unsigned n1 = node[0].getNumChildren();
        unsigned n2 = node[1].getNumChildren();
        if(n1 - n2) {
          for(unsigned i=0; i<=n1 - n2; i++) {
            if(node[0][i] == node[1][0]) {
              flag = true;
              for(unsigned j=1; j<n2; j++) {
                if(node[0][i+j] != node[1][j]) {
                  flag = false;
                  break;
                }
              }
              if(flag) {
                break;
              }
            }
          }
          if(flag) {
            retNode = NodeManager::currentNM()->mkConst( true );
          }
        }
      }
    }
  } else if(node.getKind() == kind::STRING_STRIDOF) {
    if( node[0].isConst() && node[1].isConst() && node[2].isConst() ) {
      CVC4::String s = node[0].getConst<String>();
      CVC4::String t = node[1].getConst<String>();
      CVC4::Rational RMAXINT(LONG_MAX);
      Assert(node[2].getConst<Rational>() <= RMAXINT, "Number exceeds LONG_MAX in string index_of");
      std::size_t i = node[2].getConst<Rational>().getNumerator().toUnsignedInt();
      std::size_t ret = s.find(t, i);
      if( ret != std::string::npos ) {
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::Rational((unsigned) ret) );
      } else {
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::Rational(-1) );
      }
    }
  } else if(node.getKind() == kind::STRING_STRREPL) {
    if(node[1] != node[2]) {
      if(node[0].isConst() && node[1].isConst()) {
        CVC4::String s = node[0].getConst<String>();
        CVC4::String t = node[1].getConst<String>();
        std::size_t p = s.find(t);
        if( p != std::string::npos ) {
          if(node[2].isConst()) {
            CVC4::String r = node[2].getConst<String>();
            CVC4::String ret = s.replace(t, r);
            retNode = NodeManager::currentNM()->mkConst( ::CVC4::String(ret) );
          } else {
            CVC4::String s1 = s.substr(0, (int)p);
            CVC4::String s3 = s.substr((int)p + (int)t.size());
            Node ns1 = NodeManager::currentNM()->mkConst( ::CVC4::String(s1) );
            Node ns3 = NodeManager::currentNM()->mkConst( ::CVC4::String(s3) );
            retNode = NodeManager::currentNM()->mkNode( kind::STRING_CONCAT, ns1, node[2], ns3 );
          }
        } else {
          retNode = node[0];
        }
      }
    } else {
      retNode = node[0];
    }
  } else if(node.getKind() == kind::STRING_PREFIX) {
    if(node[0].isConst() && node[1].isConst()) {
      CVC4::String s = node[1].getConst<String>();
      CVC4::String t = node[0].getConst<String>();
      retNode = NodeManager::currentNM()->mkConst( false );
      if(s.size() >= t.size()) {
        if(t == s.substr(0, t.size())) {
          retNode = NodeManager::currentNM()->mkConst( true );
        }
      }
    } else {
      Node lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[0]);
      Node lent = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[1]);
      retNode = NodeManager::currentNM()->mkNode(kind::AND,
            NodeManager::currentNM()->mkNode(kind::GEQ, lent, lens),
            node[0].eqNode(NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, node[1],
                    NodeManager::currentNM()->mkConst( ::CVC4::Rational(0) ), lens)));
    }
  } else if(node.getKind() == kind::STRING_SUFFIX) {
    if(node[0].isConst() && node[1].isConst()) {
      CVC4::String s = node[1].getConst<String>();
      CVC4::String t = node[0].getConst<String>();
      retNode = NodeManager::currentNM()->mkConst( false );
      if(s.size() >= t.size()) {
        if(t == s.substr(s.size() - t.size(), t.size())) {
          retNode = NodeManager::currentNM()->mkConst( true );
        }
      }
    } else {
      Node lens = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[0]);
      Node lent = NodeManager::currentNM()->mkNode(kind::STRING_LENGTH, node[1]);
      retNode = NodeManager::currentNM()->mkNode(kind::AND,
            NodeManager::currentNM()->mkNode(kind::GEQ, lent, lens),
            node[0].eqNode(NodeManager::currentNM()->mkNode(kind::STRING_SUBSTR_TOTAL, node[1],
                    NodeManager::currentNM()->mkNode(kind::MINUS, lent, lens), lens)));
    }
  } else if(node.getKind() == kind::STRING_ITOS || node.getKind() == kind::STRING_U16TOS || node.getKind() == kind::STRING_U32TOS) {
    if(node[0].isConst()) {
      bool flag = false;
      std::string stmp = node[0].getConst<Rational>().getNumerator().toString();
      if(node.getKind() == kind::STRING_U16TOS) {
        CVC4::Rational r1(UINT16_MAX);
        CVC4::Rational r2 = node[0].getConst<Rational>();
        if(r2>r1) {
          flag = true;
        }
      } else if(node.getKind() == kind::STRING_U32TOS) {
        CVC4::Rational r1(UINT32_MAX);
        CVC4::Rational r2 = node[0].getConst<Rational>();
        if(r2>r1) {
          flag = true;
        }
      }
      //std::string stmp = static_cast<std::ostringstream*>( &(std::ostringstream() << node[0]) )->str();
      if(flag || stmp[0] == '-') {
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::String("") );
      } else {
        retNode = NodeManager::currentNM()->mkConst( ::CVC4::String(stmp) );
      }
    }
  } else if(node.getKind() == kind::STRING_STOI || node.getKind() == kind::STRING_STOU16 || node.getKind() == kind::STRING_STOU32) {
    if(node[0].isConst()) {
      CVC4::String s = node[0].getConst<String>();
      if(s.isNumber()) {
        std::string stmp = s.toString();
        //if(stmp[0] == '0' && stmp.size() != 1) {
          //TODO: leading zeros
          //retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
        //} else {
          bool flag = false;
          CVC4::Rational r2(stmp.c_str());
          if(node.getKind() == kind::STRING_U16TOS) {
            CVC4::Rational r1(UINT16_MAX);
            if(r2>r1) {
              flag = true;
            }
          } else if(node.getKind() == kind::STRING_U32TOS) {
            CVC4::Rational r1(UINT32_MAX);
            if(r2>r1) {
              flag = true;
            }
          }
          if(flag) {
            retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
          } else {
            retNode = NodeManager::currentNM()->mkConst( r2 );
          }
        //}
      } else {
        retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
      }
    } else if(node[0].getKind() == kind::STRING_CONCAT) {
      for(unsigned i=0; i<node[0].getNumChildren(); ++i) {
        if(node[0][i].isConst()) {
          CVC4::String t = node[0][i].getConst<String>();
          if(!t.isNumber()) {
            retNode = NodeManager::currentNM()->mkConst(::CVC4::Rational(-1));
            break;
          }
        }
      }
    }
  } else if(node.getKind() == kind::STRING_IN_REGEXP) {
    retNode = rewriteMembership(node);
  }

  Trace("strings-postrewrite") << "Strings::postRewrite returning " << retNode << std::endl;
  return RewriteResponse(orig==retNode ? REWRITE_DONE : REWRITE_AGAIN_FULL, retNode);
}

bool TheoryStringsRewriter::hasEpsilonNode(TNode node) {
  for(unsigned int i=0; i<node.getNumChildren(); i++) {
    if(node[i].getKind() == kind::STRING_TO_REGEXP && node[i][0].getKind() == kind::CONST_STRING && node[i][0].getConst<String>().isEmptyString()) {
      return true;
    }
  }
  return false;
}

RewriteResponse TheoryStringsRewriter::preRewrite(TNode node) {
  Node retNode = node;
  Node orig = retNode;
  Trace("strings-prerewrite") << "Strings::preRewrite start " << node << std::endl;

  if(node.getKind() == kind::STRING_CONCAT) {
    retNode = rewriteConcatString(node);
  } 
  else if(node.getKind() == kind::REGEXP_CONCAT) {
    retNode = prerewriteConcatRegExp(node);
  } else if(node.getKind() == kind::REGEXP_UNION) {
    retNode = prerewriteOrRegExp(node);
  } else if(node.getKind() == kind::REGEXP_INTER) {
    retNode = prerewriteAndRegExp(node);
  } 
  else if(node.getKind() == kind::REGEXP_STAR) {
    if(node[0].getKind() == kind::REGEXP_STAR) {
      retNode = node[0];
    } else if(node[0].getKind() == kind::STRING_TO_REGEXP && node[0][0].getKind() == kind::CONST_STRING && node[0][0].getConst<String>().isEmptyString()) {
      retNode = node[0];
    } else if(node[0].getKind() == kind::REGEXP_EMPTY) {
      retNode = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP,
        NodeManager::currentNM()->mkConst( ::CVC4::String("") ) );
    } else if(node[0].getKind() == kind::REGEXP_UNION) {
      Node tmpNode = prerewriteOrRegExp(node[0]);
      if(tmpNode.getKind() == kind::REGEXP_UNION) {
        if(hasEpsilonNode(node[0])) {
          std::vector< Node > node_vec;
          for(unsigned int i=0; i<node[0].getNumChildren(); i++) {
            if(node[0][i].getKind() == kind::STRING_TO_REGEXP && node[0][i][0].getKind() == kind::CONST_STRING && node[0][i][0].getConst<String>().isEmptyString()) {
              //return true;
            } else {
              node_vec.push_back(node[0][i]);
            }
          }
          retNode = node_vec.size()==1 ? node_vec[0] : NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, node_vec);
          retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, retNode);
        }
      } else if(tmpNode.getKind() == kind::STRING_TO_REGEXP && tmpNode[0].getKind() == kind::CONST_STRING && tmpNode[0].getConst<String>().isEmptyString()) {
        retNode = tmpNode;
      } else {
        retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, tmpNode);
      }
    }
  } else if(node.getKind() == kind::REGEXP_PLUS) {
    retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_CONCAT, node[0],
      NodeManager::currentNM()->mkNode( kind::REGEXP_STAR, node[0]));
  } else if(node.getKind() == kind::REGEXP_OPT) {
    retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_UNION,
          NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String("") ) ),
          node[0]);
  } else if(node.getKind() == kind::REGEXP_RANGE) {
    if(node[0] == node[1]) {
      retNode = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, node[0] );
    }
    /*std::vector< Node > vec_nodes;
    unsigned char c = node[0].getConst<String>().getFirstChar();
    unsigned char end = node[1].getConst<String>().getFirstChar();
    for(; c<=end; ++c) {
      Node n = NodeManager::currentNM()->mkNode( kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst( ::CVC4::String( c ) ) );
      vec_nodes.push_back( n );
    }
    if(vec_nodes.size() == 1) {
      retNode = vec_nodes[0];
    } else {
      retNode = NodeManager::currentNM()->mkNode( kind::REGEXP_UNION, vec_nodes );
    }*/
  } else if(node.getKind() == kind::REGEXP_LOOP) {
    Node r = node[0];
    if(r.getKind() == kind::REGEXP_STAR) {
      retNode = r;
    } else {
      /* //lazy
      Node n1 = Rewriter::rewrite( node[1] );
      if(!n1.isConst()) {
        throw LogicException("re.loop contains non-constant integer (1).");
      }
      CVC4::Rational rz(0);
      CVC4::Rational RMAXINT(LONG_MAX);
      AlwaysAssert(rz <= n1.getConst<Rational>(), "Negative integer in string REGEXP_LOOP (1)");
      Assert(n1.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (1)");
      unsigned l = n1.getConst<Rational>().getNumerator().toUnsignedInt();
      if(node.getNumChildren() == 3) {
        Node n2 = Rewriter::rewrite( node[2] );
        if(!n2.isConst()) {
          throw LogicException("re.loop contains non-constant integer (2).");
        }
        if(n1 == n2) {
          if(l == 0) {
            retNode = NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP,
              NodeManager::currentNM()->mkConst(CVC4::String("")));
          } else if(l == 1) {
            retNode = node[0];
          }
        } else {
          AlwaysAssert(rz <= n2.getConst<Rational>(), "Negative integer in string REGEXP_LOOP (2)");
          Assert(n2.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (2)");
          unsigned u = n2.getConst<Rational>().getNumerator().toUnsignedInt();
          AlwaysAssert(l <= u, "REGEXP_LOOP (1) > REGEXP_LOOP (2)");
          if(l != 0) {
            Node zero = NodeManager::currentNM()->mkConst( CVC4::Rational(0) );
            Node num = NodeManager::currentNM()->mkConst( CVC4::Rational(u - l) );
            Node t1 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, node[0], n1, n1);
            Node t2 = NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, node[0], zero, num);
            retNode = NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, t1, t2);
          }
        }
      } else {
        retNode = l==0? NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, node[0]) :
          NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, 
            NodeManager::currentNM()->mkNode(kind::REGEXP_LOOP, node[0], n1, n1), 
            NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, node[0]));
      }
    }*/ //lazy
    /*else {*/
      // eager
      TNode n1 = Rewriter::rewrite( node[1] );
      //
      if(!n1.isConst()) {
        throw LogicException("re.loop contains non-constant integer (1).");
      }
      CVC4::Rational rz(0);
      CVC4::Rational RMAXINT(LONG_MAX);
      AlwaysAssert(rz <= n1.getConst<Rational>(), "Negative integer in string REGEXP_LOOP (1)");
      Assert(n1.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (1)");
      //
      unsigned l = n1.getConst<Rational>().getNumerator().toUnsignedInt();
      std::vector< Node > vec_nodes;
      for(unsigned i=0; i<l; i++) {
        vec_nodes.push_back(r);
      }
      if(node.getNumChildren() == 3) {
        TNode n2 = Rewriter::rewrite( node[2] );
        //if(!n2.isConst()) {
        //  throw LogicException("re.loop contains non-constant integer (2).");
        //}
        Node n = vec_nodes.size()==0 ? NodeManager::currentNM()->mkNode(kind::STRING_TO_REGEXP, NodeManager::currentNM()->mkConst(CVC4::String("")))
          : vec_nodes.size()==1 ? r : prerewriteConcatRegExp(NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes));
        //Assert(n2.getConst<Rational>() <= RMAXINT, "Exceeded LONG_MAX in string REGEXP_LOOP (2)");
        unsigned u = n2.getConst<Rational>().getNumerator().toUnsignedInt();
        if(u <= l) {
          retNode = n;
        } else {
          std::vector< Node > vec2;
          vec2.push_back(n);
          for(unsigned j=l; j<u; j++) {
            vec_nodes.push_back(r);
            n = vec_nodes.size()==1? r : prerewriteConcatRegExp(NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes));
            vec2.push_back(n);
          }
          retNode = prerewriteOrRegExp(NodeManager::currentNM()->mkNode(kind::REGEXP_UNION, vec2));
        }
      } else {
        Node rest = NodeManager::currentNM()->mkNode(kind::REGEXP_STAR, r);
        retNode = vec_nodes.size()==0? rest : prerewriteConcatRegExp( vec_nodes.size()==1?
                 NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, r, rest)
                :NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT,
                  NodeManager::currentNM()->mkNode(kind::REGEXP_CONCAT, vec_nodes), rest) );
      }
    }
    Trace("strings-lp") << "Strings::lp " << node << " => " << retNode << std::endl;
  }

  Trace("strings-prerewrite") << "Strings::preRewrite returning " << retNode << std::endl;
  return RewriteResponse(orig==retNode ? REWRITE_DONE : REWRITE_AGAIN_FULL, retNode);
}
