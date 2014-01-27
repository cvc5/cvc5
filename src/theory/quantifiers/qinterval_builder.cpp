/*********************                                                        */
/*! \file qinterval_builder.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of qinterval builder
 **/


#include "theory/quantifiers/qinterval_builder.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

//lower bound is exclusive
//upper bound is inclusive

struct QIntSort
{
  FirstOrderModelQInt * m;
  bool operator() (Node i, Node j) {
    return m->isLessThan( i, j );
  }
};

void QIntDef::init_vec( FirstOrderModelQInt * m, Node q, std::vector< Node >& l, std::vector< Node >& u ) {
  for( unsigned i=0; i<m->getOrderedNumVars( q ); i++ ){
    l.push_back( Node::null() );
    u.push_back( m->getMaximum( m->getOrderedVarType( q, i ) ) );
  }
}

void QIntDef::debugPrint( const char * c, FirstOrderModelQInt * m, Node q, std::vector< Node >& l, std::vector< Node >& u )
{
  Trace(c) << "( ";
  for( unsigned i=0; i<l.size(); i++ ){
    if( i>0 ) Trace(c) << ", ";
    //Trace(c) << l[i] << "..." << u[i];
    int lindex = l[i].isNull() ? 0 : m->getRepId( l[i] ) + 1;
    int uindex = m->getRepId( u[i] );
    Trace(c) << lindex << "..." << uindex;
  }
  Trace(c) << " )";
}


int QIntDef::getEvIndex( FirstOrderModelQInt * m, Node n, bool exc ) {
  if( n.isNull() ){
    Assert( exc );
    return 0;
  }else{
    int min = 0;
    int max = (int)(d_def_order.size()-1);
    while( min!=max ){
      int index = (min+max)/2;
      Assert( index>=0 && index<(int)d_def_order.size() );
      if( n==d_def_order[index] ){
        max = index;
        min = index;
      }else if( m->isLessThan( n, d_def_order[index] ) ){
        max = index;
      }else{
        min = index+1;
      }
    }
    if( n==d_def_order[min] && exc ){
      min++;
    }
    Assert( min>=0 && min<(int)d_def_order.size() );
    if( ( min!=0 && !m->isLessThan( d_def_order[min-1], n ) && ( !exc || d_def_order[min-1]!=n ) ) ||
        ( ( exc || d_def_order[min]!=n ) && !m->isLessThan( n, d_def_order[min] ) ) ){
      Debug("qint-error") << "ERR size : " << d_def_order.size() << ", exc : " << exc << std::endl;
      for( unsigned i=0; i<d_def_order.size(); i++ ){
        Debug("qint-error") << "ERR ch #" << i << " : " << d_def_order[i];
        Debug("qint-error") << " " << m->getRepId( d_def_order[i] ) << std::endl;
      }
      Debug("qint-error") << " : " << n << " " << min << " " << m->getRepId( n ) << std::endl;
    }

    Assert( min==0 || m->isLessThan( d_def_order[min-1], n ) || ( exc && d_def_order[min-1]==n ) );
    Assert( ( !exc && n==d_def_order[min] ) || m->isLessThan( n, d_def_order[min] ) );
    return min;
  }
}

void QIntDef::addEntry( FirstOrderModelQInt * m, Node q, std::vector< Node >& l, std::vector< Node >& u,
                        Node v, unsigned depth ) {
  if( depth==0 ){
    Trace("qint-compose-debug") << "Add entry ";
    debugPrint( "qint-compose-debug", m, q, l, u );
    Trace("qint-compose-debug") << " -> " << v << "..." << std::endl;
  }
  //Assert( false );
  if( depth==u.size() ){
    Assert( d_def_order.empty() );
    Assert( v.isNull() || v.isConst() || ( v.getType().isSort() && m->getRepId( v )!=-1 ) );
    d_def_order.push_back( v );
  }else{
    /*
    if( !d_def_order.empty() &&
        ( l[depth].isNull() || m->isLessThan( l[depth], d_def_order[d_def_order.size()-1] ) ) ){
      int startEvIndex = getEvIndex( m, l[depth], true );
      int endEvIndex;
      if( m->isLessThan( u[depth], d_def_order[d_def_order.size()-1] ) ){
        endEvIndex = getEvIndex( m, u[depth] );
      }else{
        endEvIndex = d_def_order.size()-1;
      }
      Trace("qint-compose-debug2") << this << " adding for bounds " << l[depth] << "..." << u[depth] << std::endl;
      for( int i=startEvIndex; i<=endEvIndex; i++ ){
        Trace("qint-compose-debug2") << this << " add entry " << d_def_order[i] << std::endl;
        d_def[d_def_order[i]].addEntry( m, q, l, u, v, depth+1 );
      }
    }
    if( !d_def_order.empty() &&
         d_def.find(u[depth])==d_def.end() &&
         !m->isLessThan( d_def_order[d_def_order.size()-1], u[depth] ) ){
      Trace("qint-compose-debug2") << "Bad : depth : " << depth << std::endl;
    }
    Assert( d_def_order.empty() ||
            d_def.find(u[depth])!=d_def.end() ||
            m->isLessThan( d_def_order[d_def_order.size()-1], u[depth] ) );

    if( d_def_order.empty() || m->isLessThan( d_def_order[d_def_order.size()-1], u[depth] ) ){
      Trace("qint-compose-debug2") << this << " add entry new : " << u[depth] << std::endl;
      d_def_order.push_back( u[depth] );
      d_def[u[depth]].addEntry( m, q, l, u, v, depth+1 );
    }
    */
    //%%%%%%
    bool success = true;
    int nnum = m->getVarOrder( q )->getNextNum( depth );
    Node pl;
    Node pu;
    if( nnum!=-1 ){
      Trace("qint-compose-debug2") << "...adding entry #" << depth << " is #" << nnum << std::endl;
      //Assert( l[nnum].isNull() || l[nnum]==l[depth] || m->isLessThan( l[nnum], l[depth] ) );
      //Assert( u[nnum]==u[depth] || m->isLessThan( u[depth], u[nnum] ) );
      pl = l[nnum];
      pu = u[nnum];
      if( !m->doMeet( l[nnum], u[nnum], l[depth], u[depth], l[nnum], u[nnum] ) ){
        success = false;
      }
    }
    //%%%%%%
    if( success ){
      Node r = u[depth];
      if( d_def.find( r )!=d_def.end() ){
        d_def[r].addEntry( m, q, l, u, v, depth+1 );
      }else{
        if( !d_def_order.empty() &&
            !m->isLessThan( d_def_order[d_def_order.size()-1], u[depth] ) ){
          Trace("qint-compose-debug2") << "Bad : depth : " << depth << " ";
          Trace("qint-compose-debug2") << d_def_order[d_def_order.size()-1] << " " << u[depth] << std::endl;
        }
        Assert( d_def_order.empty() || m->isLessThan( d_def_order[d_def_order.size()-1], r ) );
        d_def_order.push_back( r );
        d_def[r].addEntry( m, q, l, u, v, depth+1 );
      }
    }
    if( nnum!=-1 ){
      l[nnum] = pl;
      u[nnum] = pu;
    }
  }
}

Node QIntDef::simplify_r( FirstOrderModelQInt * m, Node q, std::vector< Node >& il, std::vector< Node >& iu,
                          unsigned depth ) {
  if( d_def.empty() ){
    if( d_def_order.size()!=0 ){
      Debug("qint-error") << "Simplify, size = " << d_def_order.size() << std::endl;
    }
    Assert( d_def_order.size()==1 );
    return d_def_order[0];
  }else{
    Assert( !d_def_order.empty() );
    std::vector< Node > newDefs;
    Node curr;
    for( unsigned i=0; i<d_def_order.size(); i++ ){
      Node n = d_def[d_def_order[i]].simplify_r( m, q, il, iu, depth+1 );
      if( i>0 ){
        if( n==curr && !n.isNull() ){
          d_def.erase( d_def_order[i-1] );
        }else{
          newDefs.push_back( d_def_order[i-1] );
        }
      }
      curr = n;
    }
    newDefs.push_back( d_def_order[d_def_order.size()-1] );
    d_def_order.clear();
    d_def_order.insert( d_def_order.end(), newDefs.begin(), newDefs.end() );
    return d_def_order.size()==1 ? curr : Node::null();
  }
}

Node QIntDef::simplify( FirstOrderModelQInt * m, Node q ) {
  std::vector< Node > l;
  std::vector< Node > u;
  if( !q.isNull() ){
    //init_vec( m, q, l, u );
  }
  return simplify_r( m, q, l, u, 0 );
}

bool QIntDef::isTotal_r( FirstOrderModelQInt * m, Node q, std::vector< Node >& l, std::vector< Node >& u,
                         unsigned depth ) {
  if( d_def_order.empty() ){
    return false;
  }else if( d_def.empty() ){
    return true;
  }else{
    //get the current maximum
    Node mx;
    if( !q.isNull() ){
      int pnum = m->getVarOrder( q )->getPrevNum( depth );
      if( pnum!=-1 ){
        mx = u[pnum];
      }
    }
    if( mx.isNull() ){
      mx = m->getMaximum( d_def_order[d_def_order.size()-1].getType() );
    }
    //if not current maximum
    if( d_def_order[d_def_order.size()-1]!=mx ){
      return false;
    }else{
      Node pu = u[depth];
      for( unsigned i=0; i<d_def_order.size(); i++ ){
        u[depth] = d_def_order[i];
        if( !d_def[d_def_order[i]].isTotal_r( m, q, l, u, depth+1 ) ){
          return false;
        }
      }
      u[depth] = pu;
      return true;
    }
  }
}

bool QIntDef::isTotal( FirstOrderModelQInt * m, Node q ) {
  std::vector< Node > l;
  std::vector< Node > u;
  if( !q.isNull() ){
    init_vec( m, q, l, u );
  }
  return isTotal_r( m, q, l, u, 0 );
}

void QIntDef::construct_compose_r( FirstOrderModelQInt * m, Node q,
                                    std::vector< Node >& l, std::vector< Node >& u,
                                    Node n, QIntDef * f,
                                    std::vector< Node >& args,
                                    std::map< unsigned, QIntDef >& children,
                                    std::map< unsigned, Node >& bchildren,
                                    QIntVarNumIndex& vindex, unsigned depth ) {
  //check for short circuit
  if( !f ){
    if( !args.empty() ){
      if( ( n.getKind()==OR && args[args.size()-1]==m->d_true ) ||
          ( n.getKind()==AND && args[args.size()-1]==m->d_false ) ){
        addEntry( m, q, l, u, args[args.size()-1] );
        return;
      }
    }
  }

  for( unsigned i=0; i<depth; i++ ) { Trace("qint-compose") << "  "; }
  Trace("qint-compose") << (f ? "U" : "I" ) << "C( ";
  for( unsigned i=0; i<l.size(); i++ ){
    if( i>0 ) Trace("qint-compose") << ", ";
    //Trace("qint-compose") << l[i] << "..." << u[i];
    int lindex = l[i].isNull() ? 0 : m->getRepId( l[i] ) + 1;
    int uindex = m->getRepId( u[i] );
    Trace( "qint-compose" ) << lindex << "..." << uindex;
  }
  Trace("qint-compose") << " )...";

  //finished?
  if( ( f && f->d_def.empty() ) || args.size()==n.getNumChildren() ){
    if( f ){
      Assert( f->d_def_order.size()==1 );
      Trace("qint-compose") << "UVALUE(" << f->d_def_order[0] << ")" << std::endl;
      addEntry( m, q, l, u, f->d_def_order[0] );
    }else{
      Node nn;
      bool nnSet = false;
      for( unsigned i=0; i<args.size(); i++ ){
        if( args[i].isNull() ){
          nnSet = true;
          break;
        }
      }
      if( !nnSet ){
        if( n.getKind()==EQUAL ){
          nn = NodeManager::currentNM()->mkConst( args[0]==args[1] );
        }else{
          //apply the operator to args
          nn = NodeManager::currentNM()->mkNode( n.getKind(), args );
          nn = Rewriter::rewrite( nn );
        }
      }
      Trace("qint-compose") << "IVALUE(" << nn << ")" << std::endl;
      addEntry( m, q, l, u, nn );
      Trace("qint-compose-debug2") << "...added entry." << std::endl;
    }
  }else{
    //if a non-simple child
    if( children.find( depth )!=children.end() ){
      //***************************
      Trace("qint-compose") << "compound child, recurse" << std::endl;
      std::vector< int > currIndex;
      std::vector< int > endIndex;
      std::vector< Node > prevL;
      std::vector< Node > prevU;
      std::vector< QIntDef * > visited;
      do{
        Assert( currIndex.size()==visited.size() );

        //populate the vectors
        while( visited.size()<m->getOrderedNumVars( q ) ){
          unsigned i = visited.size();
          QIntDef * qq = visited.empty() ? &children[depth] : visited[i-1]->getChild( currIndex[i-1] );
          visited.push_back( qq );
          Node qq_mx = qq->getMaximum();
          Trace("qint-compose-debug2") << "...Get ev indices " << i << " " << l[i] << " " << u[i] << std::endl;
          currIndex.push_back( qq->getEvIndex( m, l[i], true ) );
          Trace("qint-compose-debug2") << "...Done get curr index " << currIndex[currIndex.size()-1] << std::endl;
          if( m->isLessThan( qq_mx, u[i] ) ){
            endIndex.push_back( qq->getNumChildren()-1 );
          }else{
            endIndex.push_back( qq->getEvIndex( m, u[i] ) );
          }
          Trace("qint-compose-debug2") << "...Done get end index " << endIndex[endIndex.size()-1] << std::endl;
          prevL.push_back( l[i] );
          prevU.push_back( u[i] );
          if( !m->doMeet( prevL[i], prevU[i],
                          qq->getLower( currIndex[i] ), qq->getUpper( currIndex[i] ), l[i], u[i] ) ){
            Assert( false );
          }
        }
        for( unsigned i=0; i<depth; i++ ) { Trace("qint-compose") << "  "; }
        for( unsigned i=0; i<currIndex.size(); i++ ){
          Trace("qint-compose") << "[" << currIndex[i] << "/" << endIndex[i] << "]";
        }
        Trace("qint-compose") << std::endl;
        //consider the current
        int activeIndex = visited.size()-1;
        QIntDef * qa = visited.empty() ? &children[depth] : visited[activeIndex]->getChild( currIndex[activeIndex] );
        if( f ){
          int fIndex = f->getEvIndex( m, qa->getValue() );
          construct_compose_r( m, q, l, u, n, f->getChild( fIndex ), args, children, bchildren, vindex, depth+1 );
        }else{
          args.push_back( qa->getValue() );
          construct_compose_r( m, q, l, u, n, f, args, children, bchildren, vindex, depth+1 );
          args.pop_back();
        }

        //increment the index (if possible)
        while( activeIndex>=0 && currIndex[activeIndex]==endIndex[activeIndex] ){
          currIndex.pop_back();
          endIndex.pop_back();
          l[activeIndex] = prevL[activeIndex];
          u[activeIndex] = prevU[activeIndex];
          prevL.pop_back();
          prevU.pop_back();
          visited.pop_back();
          activeIndex--;
        }
        if( activeIndex>=0 ){
          for( unsigned i=0; i<depth; i++ ) { Trace("qint-compose") << "  "; }
          Trace("qint-compose-debug") << "Increment at " << activeIndex << std::endl;
          currIndex[activeIndex]++;
          if( !m->doMeet( prevL[activeIndex], prevU[activeIndex],
                          visited[activeIndex]->getLower( currIndex[activeIndex] ),
                          visited[activeIndex]->getUpper( currIndex[activeIndex] ),
                          l[activeIndex], u[activeIndex] ) ){
            Assert( false );
          }
        }
      }while( !visited.empty() );
      //***************************
    }else{
      Assert( bchildren.find( depth )!=bchildren.end() );
      Node v = bchildren[depth];
      if( f ){
        if( v.getKind()==BOUND_VARIABLE ){
          int vn = vindex.d_var_num[depth];
          Trace("qint-compose") << "variable #" << vn << ", recurse" << std::endl;
          //int vn = m->getOrderedVarOccurId( q, n, depth );
          Trace("qint-compose-debug") << "-process " << v << ", which is var #" << vn << std::endl;
          Node lprev = l[vn];
          Node uprev = u[vn];
          //restrict to last variable in order
          int pnum = m->getVarOrder( q )->getPrevNum( vn );
          if( pnum!=-1 ){
            Trace("qint-compose-debug") << "-restrict to var #" << pnum << " " << l[pnum] << " " << u[pnum] << std::endl;
            l[vn] = l[pnum];
            u[vn] = u[pnum];
          }
          int startIndex = f->getEvIndex( m, l[vn], true );
          int endIndex = f->getEvIndex( m, u[vn] );
          Trace("qint-compose-debug") << "--will process " << startIndex << " " << endIndex << std::endl;
          for( int i=startIndex; i<=endIndex; i++ ){
            if( m->doMeet( lprev, uprev, f->getLower( i ), f->getUpper( i ), l[vn], u[vn] ) ){
              construct_compose_r( m, q, l, u, n, f->getChild( i ), args, children, bchildren, vindex, depth+1 );
            }else{
              Assert( false );
            }
          }
          l[vn] = lprev;
          u[vn] = uprev;
        }else{
          Trace("qint-compose") << "value, recurse" << std::endl;
          //simple
          int ei = f->getEvIndex( m, v );
          construct_compose_r( m, q, l, u, n, f->getChild( ei ), args, children, bchildren, vindex, depth+1 );
        }
      }else{
        Trace("qint-compose") << "value, recurse" << std::endl;
        args.push_back( v );
        construct_compose_r( m, q, l, u, n, f, args, children, bchildren, vindex, depth+1 );
        args.pop_back();
      }
    }
  }
}


void QIntDef::construct_enum_r( FirstOrderModelQInt * m, Node q, unsigned vn, unsigned depth, Node v ) {
  if( depth==m->getOrderedNumVars( q ) ){
    Assert( !v.isNull() );
    d_def_order.push_back( v );
  }else{
    TypeNode tn = m->getOrderedVarType( q, depth );
    //int vnum = m->getVarOrder( q )->getVar( depth )==
    if( depth==vn ){
      for( unsigned i=0; i<m->d_rep_set.d_type_reps[tn].size(); i++ ){
        Node vv = m->d_rep_set.d_type_reps[tn][i];
        d_def_order.push_back( vv );
        d_def[vv].construct_enum_r( m, q, vn, depth+1, vv );
      }
    }else if( m->getVarOrder( q )->getVar( depth )==m->getVarOrder( q )->getVar( vn ) && depth>vn ){
      d_def_order.push_back( v );
      d_def[v].construct_enum_r( m, q, vn, depth+1, v );
    }else{
      Node mx = m->getMaximum( tn );
      d_def_order.push_back( mx );
      d_def[mx].construct_enum_r( m, q, vn, depth+1, v );
    }
  }
}

bool QIntDef::construct_enum( FirstOrderModelQInt * m, Node q, unsigned vn ) {
  TypeNode tn = m->getOrderedVarType( q, vn );
  if( tn.isSort() ){
    construct_enum_r( m, q, vn, 0, Node::null() );
    return true;
  }else{
    return false;
  }
}

bool QIntDef::construct_compose( FirstOrderModelQInt * m, Node q, Node n, QIntDef * f,
                                 std::map< unsigned, QIntDef >& children,
                                 std::map< unsigned, Node >& bchildren, int varChCount,
                                 QIntVarNumIndex& vindex ) {
 Trace("qint-compose") << "Do " << (f ? "uninterpreted" : "interpreted");
 Trace("qint-compose") << " compose, var count = " << varChCount << "..." << std::endl;
  std::vector< Node > l;
  std::vector< Node > u;
  init_vec( m, q, l, u );
  if( varChCount==0 || f ){
    //standard (no variable child) interpreted compose, or uninterpreted compose
    std::vector< Node > args;
    construct_compose_r( m, q, l, u, n, f, args, children, bchildren, vindex, 0 );
  }else{
    //special cases
    bool success = false;
    int varIndex = ( bchildren.find( 0 )!=bchildren.end() && bchildren[0].getKind()==BOUND_VARIABLE ) ? 0 : 1;
    if( varChCount>1 ){
      if( n.getKind()==EQUAL ){
        //make it an enumeration
        unsigned vn = vindex.d_var_num[0];
        if( children[0].construct_enum( m, q, vn ) ){
          bchildren.erase( 0 );
          varIndex = 1;
          success = true;
        }
      }
    }else{
      success = n.getKind()==EQUAL;
    }
    if( success ){
      int oIndex = varIndex==0 ? 1 : 0;
      Node v = bchildren[varIndex];
      unsigned vn = vindex.d_var_num[varIndex];
      if( children.find( oIndex )==children.end() ){
        Assert( bchildren.find( oIndex )!=bchildren.end() );
        Node at = bchildren[oIndex];
        Trace("qint-icompose") << "Basic child, " << at << " with var " << v << std::endl;
        Node prev = m->getPrev( bchildren[oIndex].getType(), bchildren[oIndex] );
        Node above = u[vn];
        if( !prev.isNull() ){
          u[vn] = prev;
          addEntry( m, q, l, u, NodeManager::currentNM()->mkConst( false ) );
        }
        l[vn] = prev;
        u[vn] = at;
        addEntry( m, q, l, u, NodeManager::currentNM()->mkConst( true ) );
        if( at!=above ){
          l[vn] = at;
          u[vn] = above;
          addEntry( m, q, l, u, NodeManager::currentNM()->mkConst( false ) );
        }
      }else{
        QIntDef * qid = &children[oIndex];
        qid->debugPrint("qint-icompose", m, q );
        Trace("qint-icompose") << " against variable..." << v << ", which is var #" << vn << std::endl;

        TypeNode tn = v.getType();
        QIntDefIter qdi( m, q, qid );
        while( !qdi.isFinished() ){
          std::vector< Node > us;
          qdi.getUppers( us );
          std::vector< Node > ls;
          qdi.getLowers( ls );
          qdi.debugPrint( "qint-icompose" );

          Node n_below = ls[vn];
          Node n_prev = m->getPrev( tn, qdi.getValue() );
          Node n_at = qdi.getValue();
          Node n_above = us[vn];
          Trace("qint-icompose") << n_below << " < " << n_prev << " < " << n_at << " < " << n_above << std::endl;
          if( n.getKind()==EQUAL ){
            bool atLtAbove = m->isLessThan( n_at, n_above );
            Node currL = n_below;
            if( n_at==n_above || atLtAbove ){
              //add for value (at-1)
              if( !n_prev.isNull() && ( n_below.isNull() || m->isLessThan( n_below, n_prev ) ) ){
                ls[vn] = currL;
                us[vn] = n_prev;
                currL = n_prev;
                Trace("qint-icompose") << "-add entry(-) at " << ls[vn] << "..." << us[vn] << std::endl;
                addEntry( m, q, ls, us, NodeManager::currentNM()->mkConst( false ) );
              }
              //add for value (at)
              if( ( n_below.isNull() || m->isLessThan( n_below, n_at ) ) && atLtAbove ){
                ls[vn] = currL;
                us[vn] = n_at;
                currL = n_at;
                Trace("qint-icompose") << "-add entry(=) at " << ls[vn] << "..." << us[vn] << std::endl;
                addEntry( m, q, ls, us, NodeManager::currentNM()->mkConst( true ) );
              }
            }
            ls[vn] = currL;
            us[vn] = n_above;
            Trace("qint-icompose") << "-add entry(+) at " << ls[vn] << "..." << us[vn] << std::endl;
            addEntry( m, q, ls, us, NodeManager::currentNM()->mkConst( n_at==n_above ) );
          }else{
            return false;
          }
          qdi.increment();

          Trace("qint-icompose-debug") << "Now : " << std::endl;
          debugPrint("qint-icompose-debug", m, q );
          Trace("qint-icompose-debug") << std::endl;
        }
      }

      Trace("qint-icompose") << "Result : " << std::endl;
      debugPrint("qint-icompose", m, q );
      Trace("qint-icompose") << std::endl;

    }else{
      return false;
    }
  }
  Trace("qint-compose") << "Done i-compose" << std::endl;
  return true;
}


void QIntDef::construct( FirstOrderModelQInt * m, std::vector< Node >& fapps, unsigned depth ) {
  d_def.clear();
  d_def_order.clear();
  Assert( !fapps.empty() );
  if( depth==fapps[0].getNumChildren() ){
    //get representative in model for this term
    Assert( fapps.size()>=1 );
    Node r = m->getUsedRepresentative( fapps[0] );
    d_def_order.push_back( r );
  }else{
    std::map< Node, std::vector< Node > > fapp_child;
    //partition based on evaluations of fapps[1][depth]....fapps[n][depth]
    for( unsigned i=0; i<fapps.size(); i++ ){
      Node r = m->getUsedRepresentative( fapps[i][depth] );
      fapp_child[r].push_back( fapps[i] );
    }
    //sort by QIntSort
    for( std::map< Node, std::vector< Node > >::iterator it = fapp_child.begin(); it != fapp_child.end(); ++it ){
      d_def_order.push_back( it->first );
    }
    QIntSort qis;
    qis.m = m;
    std::sort( d_def_order.begin(), d_def_order.end(), qis );
    //construct children
    for( unsigned i=0; i<d_def_order.size(); i++ ){
      Node n = d_def_order[i];
      if( i==d_def_order.size()-1 ){
        d_def_order[i] = m->getMaximum( d_def_order[i].getType() );
      }
      Debug("qint-model-debug2") << "Construct for " << n << ", terms = " << fapp_child[n].size() << std::endl;
      d_def[d_def_order[i]].construct( m, fapp_child[n], depth+1 );
    }
  }
}

Node QIntDef::getFunctionValue( FirstOrderModelQInt * m, std::vector< Node >& vars, unsigned depth ) {
  if( d_def.empty() ){
    Assert( d_def_order.size()==1 );
    //must convert to actual domain constant
    if( d_def_order[0].getType().isSort() ){
      return m->d_rep_set.d_type_reps[ d_def_order[0].getType() ][ m->getRepId( d_def_order[0] ) ];
    }else{
      return m->getUsedRepresentative( d_def_order[0] );
    }
  }else{
    TypeNode tn = vars[depth].getType();
    Node curr;
    int rep_id = m->d_rep_set.getNumRepresentatives( tn );
    for( int i=(int)(d_def_order.size()-1); i>=0; i-- ){
      int curr_rep_id = i==0 ? 0 : m->getRepId( d_def_order[i-1] )+1;
      Node ccurr = d_def[d_def_order[i]].getFunctionValue( m, vars, depth+1 );
      if( curr.isNull() ){
        curr = ccurr;
      }else{
        std::vector< Node > c;
        Assert( curr_rep_id<rep_id );
        for( int j=curr_rep_id; j<rep_id; j++ ){
          c.push_back( vars[depth].eqNode( m->d_rep_set.d_type_reps[tn][j] ) );
        }
        Node cond = c.size()==1 ? c[0] : NodeManager::currentNM()->mkNode( OR, c );
        curr = NodeManager::currentNM()->mkNode( ITE, cond, ccurr, curr );
      }
      rep_id = curr_rep_id;
    }
    return curr;
  }
}

Node QIntDef::evaluate_r( FirstOrderModelQInt * m, std::vector< Node >& reps, unsigned depth ) {
  if( depth==reps.size() ){
    Assert( d_def_order.size()==1 );
    return d_def_order[0];
  }else{
    if( d_def.find( reps[depth] )!=d_def.end() ){
      return d_def[reps[depth]].evaluate_r( m, reps, depth+1 );
    }else{
      int ei = getEvIndex( m, reps[depth] );
      return d_def[d_def_order[ei]].evaluate_r( m, reps, depth+1 );
    }
  }
}
Node QIntDef::evaluate_n_r( FirstOrderModelQInt * m, Node n, unsigned depth ) {
  if( depth==n.getNumChildren() ){
    Assert( d_def_order.size()==1 );
    return d_def_order[0];
  }else{
    Node r = m->getUsedRepresentative( n[depth] );
    if( d_def.find( r )!=d_def.end() ){
      return d_def[r].evaluate_n_r( m, n, depth+1 );
    }else{
      int ei = getEvIndex( m, r );
      return d_def[d_def_order[ei]].evaluate_n_r( m, n, depth+1 );
    }
  }
}



QIntDef * QIntDef::getChild( unsigned i ) {
  Assert( i<d_def_order.size() );
  Assert( d_def.find( d_def_order[i] )!=d_def.end() );
  return &d_def[ d_def_order[i] ];
}

void QIntDef::debugPrint( const char * c, FirstOrderModelQInt * m, Node q, int t ) {
  /*
  for( unsigned i=0; i<d_def_order.size(); i++ ){
    for( int j=0; j<t; j++ ) { Trace(c) << " "; }
    //Trace(c) << this << " ";
    Trace(c) << d_def_order[i] << " : " << std::endl;
    if( d_def.find( d_def_order[i] )!=d_def.end() ){
      d_def[d_def_order[i]].debugPrint( c, m, t+1 );
    }
  }
  */
  //if( t==0 ){
  QIntDefIter qdi( m, q, this );
  while( !qdi.isFinished() ){
    qdi.debugPrint( c, t );
    qdi.increment();
  }
  //}
}


QIntDefIter::QIntDefIter( FirstOrderModelQInt * m, Node q, QIntDef * qid ) : d_fm( m ), d_q( q ){
  resetIndex( qid );
}

void QIntDefIter::debugPrint( const char * c, int t ) {
  //Trace( c ) << getSize() << " " << d_index_visited.size() << " ";
  for( int j=0; j<t; j++ ) { Trace(c) << " "; }
  std::vector< Node > l;
  std::vector< Node > u;
  getLowers( l );
  getUppers( u );
  QIntDef::debugPrint( c, d_fm, d_q, l, u );
  Trace( c ) << " -> " << getValue() << std::endl;
}

void QIntDefIter::resetIndex( QIntDef * qid ){
  //std::cout << "check : " << qid << " " << qid->d_def_order.size() << " " << qid->d_def.size() << std::endl;
  if( !qid->d_def.empty() ){
    //std::cout << "add to visited " <<  qid << std::endl;
    d_index.push_back( 0 );
    d_index_visited.push_back( qid );
    resetIndex( qid->getChild( 0 ) );
  }
}

bool QIntDefIter::increment( int index ) {
  if( !isFinished() ){
    index = index==-1 ? (int)(d_index.size()-1) : index;
    while( (int)(d_index.size()-1)>index ){
      //std::cout << "remove from visit 1 " << std::endl;
      d_index.pop_back();
      d_index_visited.pop_back();
    }
    while( index>=0 && d_index[index]>=(int)(d_index_visited[index]->d_def_order.size()-1) ){
      //std::cout << "remove from visit " << d_index_visited[ d_index_visited.size()-1 ] << std::endl;
      d_index.pop_back();
      d_index_visited.pop_back();
      index--;
    }
    if( index>=0 ){
      //std::cout << "increment at index = " << index << std::endl;
      d_index[index]++;
      resetIndex( d_index_visited[index]->getChild( d_index[index] ) );
      return true;
    }else{
      d_index.clear();
      return false;
    }
  }else{
    return false;
  }
}

Node QIntDefIter::getLower( int index ) {
  if( d_index[index]==0 && !d_q.isNull() ){
    int pnum = d_fm->getVarOrder( d_q )->getPrevNum( index );
    if( pnum!=-1 ){
      return getLower( pnum );
    }
  }
  return d_index_visited[index]->getLower( d_index[index] );
}

Node QIntDefIter::getUpper( int index ) {
  return d_index_visited[index]->getUpper( d_index[index] );
}

void QIntDefIter::getLowers( std::vector< Node >& reps ) {
  for( unsigned i=0; i<getSize(); i++ ){
    bool added = false;
    if( d_index[i]==0 && !d_q.isNull() ){
      int pnum = d_fm->getVarOrder( d_q )->getPrevNum( i );
      if( pnum!=-1 ){
        added = true;
        reps.push_back( reps[pnum] );
      }
    }
    if( !added ){
      reps.push_back( getLower( i ) );
    }
  }
}

void QIntDefIter::getUppers( std::vector< Node >& reps ) {
  for( unsigned i=0; i<getSize(); i++ ){
    reps.push_back( getUpper( i ) );
  }
}

Node QIntDefIter::getValue() {
  return d_index_visited[ d_index_visited.size()-1 ]->getChild( d_index[d_index.size()-1] )->getValue();
}


//------------------------variable ordering----------------------------

QuantVarOrder::QuantVarOrder( Node q ) : d_q( q ) {
  d_var_count = 0;
  initialize( q[1], 0, d_var_occur );
}

int QuantVarOrder::initialize( Node n, int minVarIndex, QIntVarNumIndex& vindex ) {
  if( n.getKind()!=FORALL ){
    //std::vector< Node > vars;
    //std::vector< int > args;
    int procVarOn = n.getKind()==APPLY_UF ? 0 : 1;
    for( int r=0; r<=procVarOn; r++ ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( n[i].getKind()==BOUND_VARIABLE && r==procVarOn ){
          int occ_index = -1;
          for( unsigned j=0; j<d_var_to_num[n[i]].size(); j++ ){
            if( d_var_to_num[n[i]][j]>=minVarIndex ){
              occ_index = d_var_to_num[n[i]][j];
            }
          }
          if( occ_index==-1 ){
            //need to assign new
            d_num_to_var[d_var_count] = n[i];
            if( !d_var_to_num[n[i]].empty() ){
              int v = d_var_to_num[n[i]][ d_var_to_num[n[i]].size()-1 ];
              d_num_to_prev_num[ d_var_count ] = v;
              d_num_to_next_num[ v ] = d_var_count;
            }
            d_var_num_index[ d_var_count ] = d_var_to_num[n[i]].size();
            d_var_to_num[n[i]].push_back( d_var_count );
            occ_index = d_var_count;
            d_var_count++;
          }
          vindex.d_var_num[i] = occ_index;
          minVarIndex = occ_index;
        }else if( r==0 ){
          minVarIndex = initialize( n[i], minVarIndex, vindex.d_var_index[i] );
        }
      }
    }
  }
  return minVarIndex;
}

bool QuantVarOrder::getInstantiation( FirstOrderModelQInt * m, std::vector< Node >& l, std::vector< Node >& u,
                                      std::vector< Node >& inst ) {
  Debug("qint-var-order-debug2") << "Get for " << d_q << " " << l.size() << " " << u.size() << std::endl;
  for( unsigned i=0; i<d_q[0].getNumChildren(); i++ ){
    Debug("qint-var-order-debug2") << "Get for " << d_q[0][i] << " " << d_var_to_num[d_q[0][i]].size() << std::endl;
    Node ll = Node::null();
    Node uu = m->getMaximum( d_q[0][i].getType() );
    for( unsigned j=0; j<d_var_to_num[d_q[0][i]].size(); j++ ){
      Debug("qint-var-order-debug2") << "Go " << j << std::endl;
      Node cl = ll;
      Node cu = uu;
      int index = d_var_to_num[d_q[0][i]][j];
      Debug("qint-var-order-debug2") << "Do meet for " << index << "..." << std::endl;
      Debug("qint-var-order-debug2") << l[index] << " " << u[index] << " " << cl << " " << cu << std::endl;
      if( !m->doMeet( l[index], u[index], cl, cu, ll, uu ) ){
        Debug("qint-var-order-debug2") << "FAILED" << std::endl;
        return false;
      }
      Debug("qint-var-order-debug2") << "Result : " << ll << " " << uu << std::endl;
    }
    Debug("qint-var-order-debug2") << "Got " << uu << std::endl;
    inst.push_back( uu );
  }
  return true;
}

void QuantVarOrder::debugPrint( const char * c ) {
  Trace( c ) << "Variable order for " << d_q << " is : " << std::endl;
  debugPrint( c, d_q[1], d_var_occur );
  Trace( c ) << std::endl;
  for( unsigned i=0; i<d_q[0].getNumChildren(); i++ ){
    Trace( c ) << d_q[0][i] << " : ";
    for( unsigned j=0; j<d_var_to_num[d_q[0][i]].size(); j++ ){
      Trace( c ) << d_var_to_num[d_q[0][i]][j] << " ";
    }
    Trace( c ) << std::endl;
  }
}

void QuantVarOrder::debugPrint( const char * c, Node n, QIntVarNumIndex& vindex ) {
  if( n.getKind()==FORALL ){
    Trace(c) << "NESTED_QUANT";
  }else{
    Trace(c) << n.getKind() << "(";
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( i>0 ) Trace( c ) << ",";
      Trace( c ) << " ";
      if( n[i].getKind()==BOUND_VARIABLE ){
        Trace(c) << "VAR[" << vindex.d_var_num[i] << "]";
      }else{
        debugPrint( c, n[i], vindex.d_var_index[i] );
      }
      if( i==n.getNumChildren()-1 ) Trace( c ) << " ";
    }
    Trace(c) << ")";
  }
}

QIntervalBuilder::QIntervalBuilder( context::Context* c, QuantifiersEngine* qe ) :
QModelBuilder( c, qe ){
  d_true = NodeManager::currentNM()->mkConst( true );
}


//------------------------model construction----------------------------

void QIntervalBuilder::processBuildModel(TheoryModel* m, bool fullModel) {
  Trace("fmf-qint-debug") << "process build model " << fullModel << std::endl;
  FirstOrderModel* f = (FirstOrderModel*)m;
  FirstOrderModelQInt* fm = f->asFirstOrderModelQInt();
  if( fullModel ){
    Trace("qint-model") << "Construct model representation..." << std::endl;
    //make function values
    for( std::map<Node, QIntDef * >::iterator it = fm->d_models.begin(); it != fm->d_models.end(); ++it ) {
      if( it->first.getType().getNumChildren()>1 ){
        Trace("qint-model") << "Construct for " << it->first << "..." << std::endl;
        m->d_uf_models[ it->first ] = fm->getFunctionValue( it->first, "$x" );
      }
    }
    TheoryEngineModelBuilder::processBuildModel( m, fullModel );
    //mark that the model has been set
    fm->markModelSet();
    //debug the model
    debugModel( fm );
  }else{
    fm->initialize( d_considerAxioms );
    //process representatives
    fm->d_rep_id.clear();
    fm->d_max.clear();
    fm->d_min.clear();
    Trace("qint-model") << std::endl << "Making representatives..." << std::endl;
    for( std::map< TypeNode, std::vector< Node > >::iterator it = fm->d_rep_set.d_type_reps.begin();
         it != fm->d_rep_set.d_type_reps.end(); ++it ){
      if( it->first.isSort() ){
        if( it->second.empty() ){
          std::cout << "Empty rep for " << it->first << std::endl;
          exit(0);
        }
        Trace("qint-model") << "Representatives for " << it->first << " : " << std::endl;
        for( unsigned i=0; i<it->second.size(); i++ ){
          Trace("qint-model") << i << " : " << it->second[i] << std::endl;
          fm->d_rep_id[it->second[i]] = i;
        }
        fm->d_min[it->first] = it->second[0];
        fm->d_max[it->first] = it->second[it->second.size()-1];
      }else{
        //TODO: enumerate?
      }
    }
    Trace("qint-model") << std::endl << "Making function definitions..." << std::endl;
    //construct the models for functions
    for( std::map<Node, QIntDef * >::iterator it = fm->d_models.begin(); it != fm->d_models.end(); ++it ) {
      Node f = it->first;
      Trace("qint-model-debug") << "Building Model for " << f << std::endl;
      //reset the model
      //get all (non-redundant) f-applications
      std::vector< Node > fapps;
      Trace("qint-model-debug") << "Initial terms: " << std::endl;
      for( size_t i=0; i<fm->d_uf_terms[f].size(); i++ ){
        Node n = fm->d_uf_terms[f][i];
        if( !n.getAttribute(NoMatchAttribute()) ){
          Trace("qint-model-debug") << "  " << n << std::endl;
          fapps.push_back( n );
        }
      }
      if( fapps.empty() ){
        //choose arbitrary value
        Node mbt = d_qe->getTermDatabase()->getModelBasisOpTerm(f);
        Trace("qint-model-debug") << "Initial terms empty, add " << mbt << std::endl;
        fapps.push_back( mbt );
      }
      //construct the interval model
      it->second->construct( fm, fapps );
      Trace("qint-model-debug") << "Definition for " << f << " : " << std::endl;
      it->second->debugPrint("qint-model-debug", fm, Node::null() );

      it->second->simplify( fm, Node::null() );
      Trace("qint-model") << "(Simplified) definition for " << f << " : " << std::endl;
      it->second->debugPrint("qint-model", fm, Node::null() );

      if( Debug.isOn("qint-model-debug") ){
        for( size_t i=0; i<fm->d_uf_terms[f].size(); i++ ){
          Node e = it->second->evaluate_n( fm, fm->d_uf_terms[f][i] );
          Debug("qint-model-debug") << fm->d_uf_terms[f][i] << " evaluates to " << e << std::endl;
          Assert( fm->areEqual( e, fm->d_uf_terms[f][i] ) );
        }
      }
    }
  }
}


//--------------------model checking---------------------------------------

//do exhaustive instantiation
bool QIntervalBuilder::doExhaustiveInstantiation( FirstOrderModel * fm, Node q, int effort ) {
  Trace("qint-check") << "exhaustive instantiation " << q << " " << effort << std::endl;
  if (effort==0) {

    FirstOrderModelQInt * fmqint = fm->asFirstOrderModelQInt();
    QIntDef qid;
    doCheck( fmqint, q, qid, q[1], fmqint->d_var_order[q]->d_var_occur );
    //now process entries
    Trace("qint-inst") << "Interpretation for " << q << " is : " << std::endl;
    qid.debugPrint( "qint-inst", fmqint, q );
    Trace("qint-inst") << std::endl;
    Debug("qint-check-debug2") << "Make iterator..." << std::endl;
    QIntDefIter qdi( fmqint, q, &qid );
    while( !qdi.isFinished() ){
      if( qdi.getValue()!=d_true ){
        Debug("qint-check-debug2") << "Set up vectors..." << std::endl;
        std::vector< Node > l;
        std::vector< Node > u;
        std::vector< Node > inst;
        qdi.getLowers( l );
        qdi.getUppers( u );
        Debug("qint-check-debug2") << "Get instantiation..." << std::endl;
        if( fmqint->d_var_order[q]->getInstantiation( fmqint, l, u, inst ) ){
          Trace("qint-inst") << "** Instantiate with ";
          //just add the instance
          for( unsigned j=0; j<inst.size(); j++) {
            Trace("qint-inst") << inst[j] << " ";
          }
          Trace("qint-inst") << std::endl;
          d_triedLemmas++;
          if( d_qe->addInstantiation( q, inst ) ){
            Trace("qint-inst") << "   ...added instantiation." << std::endl;
            d_addedLemmas++;
          }else{
            Trace("qint-inst") << "   ...duplicate instantiation" << std::endl;
            //verify that instantiation is witness for current entry
            if( Debug.isOn("qint-check-debug2") ){
              Debug("qint-check-debug2") << "Check if : ";
              std::vector< Node > exp_inst;
              for( unsigned i=0; i<fmqint->getOrderedNumVars( q ); i++ ){
                int index = fmqint->getOrderedVarNumToVarNum( q, i );
                exp_inst.push_back( inst[ index ] );
                Debug("qint-check-debug2") << inst[index] << " ";
              }
              Debug("qint-check-debug2") << " evaluates to " << qdi.getValue() << std::endl;
              Assert( qid.evaluate( fmqint, exp_inst )==qdi.getValue() );
            }
          }
        }else{
          Trace("qint-inst") << "** Spurious instantiation." << std::endl;
        }
      }
      qdi.increment();
    }
  }
  return true;
}

bool QIntervalBuilder::doCheck( FirstOrderModelQInt * m, Node q, QIntDef & qid, Node n,
                                QIntVarNumIndex& vindex ) {
  Assert( n.getKind()!=FORALL );
  std::map< unsigned, QIntDef > children;
  std::map< unsigned, Node > bchildren;
  int varChCount = 0;
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if( n[i].getKind()==FORALL ){
      bchildren[i] = Node::null();
    }else if( n[i].getKind() == BOUND_VARIABLE ){
      varChCount++;
      bchildren[i] = n[i];
    }else if( m->hasTerm( n[i] ) ){
      bchildren[i] = m->getUsedRepresentative( n[i] );
    }else{
      if( !doCheck( m, q, children[i], n[i], vindex.d_var_index[i] ) ){
        bchildren[i] = Node::null();
      }
    }
  }
  Trace("qint-check-debug") << "Compute Interpretation of " << n << " " << n.getKind() << std::endl;
  if( n.getKind() == APPLY_UF || n.getKind() == VARIABLE || n.getKind() == SKOLEM ){
    Node op = n.getKind() == APPLY_UF ? n.getOperator() : n;
    //uninterpreted compose
    qid.construct_compose( m, q, n, m->d_models[op], children, bchildren, varChCount, vindex );
  }else if( !qid.construct_compose( m, q, n, NULL, children, bchildren, varChCount, vindex ) ){
    Trace("qint-check-debug") << "** Cannot produce definition for " << n << std::endl;
    return false;
  }
  Trace("qint-check-debug2") << "Definition for " << n << " is : " << std::endl;
  qid.debugPrint("qint-check-debug2", m, q);
  qid.simplify( m, q );
  Trace("qint-check-debug") << "(Simplified) Definition for " << n << " is : " << std::endl;
  qid.debugPrint("qint-check-debug", m, q);
  Trace("qint-check-debug") << std::endl;
  Assert( qid.isTotal( m, q ) );
  return true;
}
