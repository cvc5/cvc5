/*********************                                                        */
/*! \file ambqi_builder.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of abstract MBQI builder
 **/


#include "theory/quantifiers/ambqi_builder.h"
#include "theory/quantifiers/term_database.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

void AbsDef::construct_func( FirstOrderModelAbs * m, std::vector< TNode >& fapps, unsigned depth ) {
  d_def.clear();
  Assert( !fapps.empty() );
  if( depth==fapps[0].getNumChildren() ){
    //get representative in model for this term
    Assert( fapps.size()==1 );
    d_value = m->getRepresentativeId( fapps[0] );
    Assert( d_value!=-1 );
  }else{
    TypeNode tn = fapps[0][depth].getType();
    std::map< unsigned, std::vector< TNode > > fapp_child;

    //partition based on evaluations of fapps[1][depth]....fapps[n][depth]
    for( unsigned i=0; i<fapps.size(); i++ ){
      unsigned r = m->getRepresentativeId( fapps[i][depth] );
      Assert( r < 32 );
      fapp_child[r].push_back( fapps[i] );
    }

    //do completion
    std::map< unsigned, unsigned > fapp_child_index;
    unsigned def = m->d_domain[ tn ];
    unsigned minSize = fapp_child.begin()->second.size();
    unsigned minSizeIndex = fapp_child.begin()->first;
    for( std::map< unsigned, std::vector< TNode > >::iterator it = fapp_child.begin(); it != fapp_child.end(); ++it ){
      fapp_child_index[it->first] = ( 1 << it->first );
      def = def & ~( 1 << it->first );
      if( it->second.size()<minSize ){
        minSize = it->second.size();
        minSizeIndex = it->first;
      }
    }
    fapp_child_index[minSizeIndex] |= def;
    d_default = fapp_child_index[minSizeIndex];

    //construct children
    for( std::map< unsigned, std::vector< TNode > >::iterator it = fapp_child.begin(); it != fapp_child.end(); ++it ){
      Trace("abs-model-debug") << "Construct " << it->first << " : " << fapp_child_index[it->first] << " : ";
      debugPrintUInt( "abs-model-debug", m->d_rep_set.d_type_reps[tn].size(), fapp_child_index[it->first] );
      Trace("abs-model-debug") << " : " << it->second.size() << " terms." << std::endl;
      d_def[fapp_child_index[it->first]].construct_func( m, it->second, depth+1 );
    }
  }
}

void AbsDef::simplify( FirstOrderModelAbs * m, Node q, unsigned depth ) {
  if( d_value==-1 ){
    //process the default
    std::map< unsigned, AbsDef >::iterator defd = d_def.find( d_default );
    unsigned newDef = d_default;
    std::vector< unsigned > to_erase;
    defd->second.simplify( m, q, depth+1 );
    bool isConstant = ( defd->second.d_value!=-1 );
    //process each child
    for( std::map< unsigned, AbsDef >::iterator it = d_def.begin(); it != d_def.end(); ++it ){
      if( it->first!=d_default ){
        it->second.simplify( m, q, depth+1 );
        if( it->second.d_value==defd->second.d_value && it->second.d_value!=-1 ){
          newDef = d_default | it->first;
          to_erase.push_back( it->first );
        }else{
          isConstant = false;
        }
      }
    }
    if( !to_erase.empty() ){
      //erase old default
      int defVal = defd->second.d_value;
      d_def.erase( d_default );
      //set new default
      d_default = newDef;
      d_def[d_default].construct_def_entry( m, q, defVal, depth+1 );
      //erase redundant entries
      for( unsigned i=0; i<to_erase.size(); i++ ){
        d_def.erase( to_erase[i] );
      }
    }
    //if constant, propagate the value upwards
    if( isConstant ){
      d_value = defd->second.d_value;
    }
  }
}

void AbsDef::debugPrintUInt( const char * c, unsigned dSize, unsigned u ) {
  for( unsigned i=0; i<dSize; i++ ){
    Trace(c) << ( ( u & ( 1 << i ) )!=0 ? "1" : "0");
  }
}

void AbsDef::debugPrint( const char * c, FirstOrderModelAbs * m, Node f, unsigned depth ) {
  if( Trace.isOn(c) ){
    if( depth==f.getNumChildren() ){
      for( unsigned i=0; i<depth; i++ ){ Trace(c) << "  ";}
      Trace(c) << "V[" << d_value << "]" << std::endl;
    }else{
      TypeNode tn = f[depth].getType();
      unsigned dSize = m->d_rep_set.d_type_reps[tn].size();
      Assert( dSize<32 );
      for( std::map< unsigned, AbsDef >::iterator it = d_def.begin(); it != d_def.end(); ++it ){
        for( unsigned i=0; i<depth; i++ ){ Trace(c) << "  ";}
        debugPrintUInt( c, dSize, it->first );
        if( it->first==d_default ){
          Trace(c) << "*";
        }
        if( it->second.d_value!=-1 ){
          Trace(c) << " -> V[" << it->second.d_value << "]";
        }
        Trace(c) << std::endl;
        it->second.debugPrint( c, m, f, depth+1 );
      }
    }
  }
}

int AbsDef::addInstantiations( FirstOrderModelAbs * m, QuantifiersEngine * qe, Node q, std::vector< Node >& terms, unsigned depth ) {
  if( depth==q[0].getNumChildren() ){
    if( d_value!=1 ){
      if( qe->addInstantiation( q, terms ) ){
        return 1;
      }
    }
    return 0;
  }else{
    int sum = 0;
    TypeNode tn = q[0][depth].getType();
    for( std::map< unsigned, AbsDef >::iterator it = d_def.begin(); it != d_def.end(); ++it ){
      //get witness term
      int index = getId( it->first );
      terms.push_back( m->d_rep_set.d_type_reps[tn][index] );
      sum += it->second.addInstantiations( m, qe, q, terms, depth+1 );
      terms.pop_back();
    }
    return sum;
  }
}

void AbsDef::construct_entry( std::vector< unsigned >& entry, std::vector< bool >& entry_def, int v, unsigned depth ) {
  if( depth==entry.size() ){
    d_value = v;
  }else{
    d_def[entry[depth]].construct_entry( entry, entry_def, v, depth+1 );
    if( entry_def[depth] ){
      d_default = entry[depth];
    }
  }
}

void AbsDef::construct_def_entry( FirstOrderModelAbs * m, Node q, int v, unsigned depth ) {
  if( depth==q[0].getNumChildren() ){
    d_value = v;
  }else{
    unsigned dom = m->d_domain[q[0][depth].getType()];
    d_def[dom].construct_def_entry( m, q, v, depth+1 );
    d_default = dom;
  }
}

void AbsDef::apply_ucompose( std::vector< unsigned >& entry, std::vector< bool >& entry_def,
                             std::vector< int >& terms, std::map< unsigned, int >& vchildren,
                             AbsDef * a, unsigned depth ) {
  if( depth==terms.size() ){
    a->construct_entry( entry, entry_def, d_value );
  }else{
    unsigned id;
    if( terms[depth]==-1 ){
      //a variable
      std::map< unsigned, int >::iterator itv = vchildren.find( depth );
      Assert( itv!=vchildren.end() );
      unsigned prev_v = entry[itv->second];
      bool prev_vd = entry_def[itv->second];
      for( std::map< unsigned, AbsDef >::iterator it = d_def.begin(); it != d_def.end(); ++it ){
        entry[itv->second] = it->first & prev_v;
        entry_def[itv->second] = ( it->first==d_default ) && prev_vd;
        if( entry[itv->second]!=0 ){
          it->second.apply_ucompose( entry, entry_def, terms, vchildren, a, depth+1 );
        }
      }
      entry[itv->second] = prev_v;
      entry_def[itv->second] = prev_vd;
    }else{
      id = (unsigned)terms[depth];
      Assert( id<32 );
      unsigned fid = 1 << id;
      std::map< unsigned, AbsDef >::iterator it = d_def.find( fid );
      if( it!=d_def.end() ){
        it->second.apply_ucompose( entry, entry_def, terms, vchildren, a, depth+1 );
      }else{
        d_def[d_default].apply_ucompose( entry, entry_def, terms, vchildren, a, depth+1 );
      }
    }
  }
}

void AbsDef::construct_var_eq( FirstOrderModelAbs * m, Node q, unsigned v1, unsigned v2, int curr, int currv, unsigned depth ) {
  if( depth==q[0].getNumChildren() ){
    Assert( currv!=-1 );
    d_value = currv;
  }else{
    TypeNode tn = q[0][depth].getType();
    unsigned dom = m->d_domain[tn];
    int vindex = depth==v1 ? 0 : ( depth==v2 ? 1 : -1 );
    if( vindex==-1 ){
      d_def[dom].construct_var_eq( m, q, v1, v2, curr, currv, depth+1 );
      d_default = dom;
    }else{
      Assert( currv==-1 );
      if( curr==-1 ){
        unsigned numReps = m->d_rep_set.d_type_reps[tn].size();
        Assert( numReps < 32 );
        for( unsigned i=0; i<numReps; i++ ){
          curr = 1 << i;
          d_def[curr].construct_var_eq( m, q, v1, v2, curr, currv, depth+1 );
        }
        d_default = curr;
      }else{
        d_def[curr].construct_var_eq( m, q, v1, v2, curr, 1, depth+1 );
        dom = dom & ~curr;
        d_def[dom].construct_var_eq( m, q, v1, v2, curr, 0, depth+1 );
        d_default = dom;
      }
    }
  }
}

void AbsDef::construct_var( FirstOrderModelAbs * m, Node q, unsigned v, int currv, unsigned depth ) {
  if( depth==q[0].getNumChildren() ){
    Assert( currv!=-1 );
    d_value = currv;
  }else{
    TypeNode tn = q[0][depth].getType();
    if( v==depth ){
      unsigned numReps = m->d_rep_set.d_type_reps[tn].size();
      Assert( numReps>0 && numReps < 32 );
      for( unsigned i=0; i<numReps; i++ ){
        d_def[ 1 << i ].construct_var( m, q, v, i, depth+1 );
      }
      d_default = 1 << (numReps-1);
    }else{
      unsigned dom = m->d_domain[tn];
      d_def[dom].construct_var( m, q, v, currv, depth+1 );
      d_default = dom;
    }
  }
}

void AbsDef::construct_compose( FirstOrderModelAbs * m, Node q, Node n, AbsDef * f,
                                std::map< unsigned, AbsDef * >& children,
                                std::map< unsigned, int >& bchildren, std::map< unsigned, int >& vchildren,
                                std::vector< unsigned >& entry, std::vector< bool >& entry_def,
                                bool incomplete ) {
  if( Trace.isOn("ambqi-check-debug2") ){
    for( unsigned i=0; i<entry.size(); i++ ){ Trace("ambqi-check-debug2") << "  "; }
  }
  if( n.getKind()==OR || n.getKind()==AND ){
    // short circuiting
    for( std::map< unsigned, AbsDef * >::iterator it = children.begin(); it != children.end(); ++it ){
      if( ( it->second->d_value==0 && n.getKind()==AND ) ||
          ( it->second->d_value==1 && n.getKind()==OR ) ){
        construct_entry( entry, entry_def, it->second->d_value );
        return;
      }
    }
  }
  if( entry.size()==q[0].getNumChildren() ){
    if( incomplete ){
      //if a child is unknown, we must return unknown
      construct_entry( entry, entry_def, -1 );
    }else{
      if( f ){
        Trace("ambqi-check-debug2") << "Evaluate uninterpreted function entry..." << std::endl;
        //we are composing with an uninterpreted function
        std::vector< int > values;
        values.resize( n.getNumChildren(), -1 );
        for( std::map< unsigned, AbsDef * >::iterator it = children.begin(); it != children.end(); ++it ){
          values[it->first] = it->second->d_value;
        }
        for( std::map< unsigned, int >::iterator it = bchildren.begin(); it != bchildren.end(); ++it ){
          values[it->first] = it->second;
        }
        //look up value(s)
        f->apply_ucompose( entry, entry_def, values, vchildren, this );
      }else{
        //we are composing with an interpreted function
        std::vector< TNode > values;
        values.resize( n.getNumChildren(), TNode::null() );
        for( std::map< unsigned, AbsDef * >::iterator it = children.begin(); it != children.end(); ++it ){
          Assert( it->second->d_value>=0 && it->second->d_value<(int)m->d_rep_set.d_type_reps[n[it->first].getType()].size() );
          values[it->first] = m->d_rep_set.d_type_reps[n[it->first].getType()][it->second->d_value];
          Trace("ambqi-check-debug2") << it->first << " : " << it->second->d_value << " ->> " << values[it->first] << std::endl;
        }
        for( std::map< unsigned, int >::iterator it = bchildren.begin(); it != bchildren.end(); ++it ){
          Assert( it->second>=0 && it->second<(int)m->d_rep_set.d_type_reps[n[it->first].getType()].size() );
          values[it->first] = m->d_rep_set.d_type_reps[n[it->first].getType()][it->second];
          Trace("ambqi-check-debug2") << it->first << " : " << it->second << " ->> " << values[it->first] << std::endl;
        }
        Assert( vchildren.empty() );
        if( Trace.isOn("ambqi-check-debug2") ){
          Trace("ambqi-check-debug2") << "Evaluate interpreted function entry ( ";
          for( unsigned i=0; i<values.size(); i++ ){
            Trace("ambqi-check-debug2") << values[i] << " ";
          }
          Trace("ambqi-check-debug2") << ")..." << std::endl;
        }
        //evaluate
        Node vv = NodeManager::currentNM()->mkNode( n.getKind(), values );
        vv = Rewriter::rewrite( vv );
        int v = m->getRepresentativeId( vv );
        construct_entry( entry, entry_def, v );
      }
    }
  }else{
    //take product of arguments
    TypeNode tn = q[0][entry.size()].getType();
    unsigned def = m->d_domain[tn];
    Trace("ambqi-check-debug2") << "Take product of arguments" << std::endl;
    for( std::map< unsigned, AbsDef * >::iterator it = children.begin(); it != children.end(); ++it ){
      //process each child
      for( std::map< unsigned, AbsDef >::iterator itd = it->second->d_def.begin(); itd != it->second->d_def.end(); ++itd ){
        if( itd->first!=it->second->d_default && ( def & itd->first )!=0 ){
          def &= ~( itd->first );
          //process this value
          std::map< unsigned, AbsDef * > cchildren;
          for( std::map< unsigned, AbsDef * >::iterator it2 = children.begin(); it2 != children.end(); ++it2 ){
            std::map< unsigned, AbsDef >::iterator itdf = it->second->d_def.find( itd->first );
            if( itdf!=it->second->d_def.end() ){
              cchildren[it->first] = &itdf->second;
            }else{
              cchildren[it->first] = it2->second->getDefault();
            }
          }
          if( Trace.isOn("ambqi-check-debug2") ){
            for( unsigned i=0; i<entry.size(); i++ ){ Trace("ambqi-check-debug2") << "  "; }
            Trace("ambqi-check-debug2") << "...process : ";
            debugPrintUInt("ambqi-check-debug2", m->d_rep_set.d_type_reps[tn].size(), itd->first );
            Trace("ambqi-check-debug2") << std::endl;
          }
          entry.push_back( itd->first );
          entry_def.push_back( def==0 );
          construct_compose( m, q, n, f, cchildren, bchildren, vchildren, entry, entry_def, incomplete );
          entry_def.pop_back();
          entry.pop_back();
          if( def==0 ){
            break;
          }
        }
      }
      if( def==0 ){
        break;
      }
    }
    if( def!=0 ){
      std::map< unsigned, AbsDef * > cdchildren;
      for( std::map< unsigned, AbsDef * >::iterator it = children.begin(); it != children.end(); ++it ){
        cdchildren[it->first] = it->second->getDefault();
      }
      if( Trace.isOn("ambqi-check-debug2") ){
        for( unsigned i=0; i<entry.size(); i++ ){ Trace("ambqi-check-debug2") << "  "; }
        Trace("ambqi-check-debug2") << "...process default : ";
        debugPrintUInt("ambqi-check-debug2", m->d_rep_set.d_type_reps[tn].size(), def );
        Trace("ambqi-check-debug2") << std::endl;
      }
      entry.push_back( def );
      entry_def.push_back( true );
      construct_compose( m, q, n, f, cdchildren, bchildren, vchildren, entry, entry_def, incomplete );
      entry_def.pop_back();
      entry.pop_back();
    }
  }
}

bool AbsDef::construct( FirstOrderModelAbs * m, Node q, Node n, AbsDef * f,
                        std::map< unsigned, AbsDef * >& children,
                        std::map< unsigned, int >& bchildren, std::map< unsigned, int >& vchildren,
                        int varChCount, bool incomplete ) {
  if( varChCount==0 || f ){
    //short-circuit
    if( n.getKind()==AND || n.getKind()==OR ){
      for( std::map< unsigned, int >::iterator it = bchildren.begin(); it !=bchildren.end(); ++it ){
        if( ( it->second==0 && n.getKind()==AND ) ||
            ( it->second==1 && n.getKind()==OR ) ){
          construct_def_entry( m, q, it->second );
          return true;
        }
      }
    }
    Trace("ambqi-check-debug2") << "Construct compose..." << std::endl;
    std::vector< unsigned > entry;
    std::vector< bool > entry_def;
    construct_compose( m, q, n, f, children, bchildren, vchildren, entry, entry_def, incomplete );
    return true;
  }else if( varChCount==1 && n.getKind()==EQUAL ){
    Trace("ambqi-check-debug2") << "Expand variable child..." << std::endl;
    //expand the variable based on its finite domain
    AbsDef a;
    a.construct_var( m, q, vchildren.begin()->second, -1 );
    children[vchildren.begin()->first] = &a;
    vchildren.clear();
    std::vector< unsigned > entry;
    std::vector< bool > entry_def;
    Trace("ambqi-check-debug2") << "Construct compose with variable..." << std::endl;
    construct_compose( m, q, n, f, children, bchildren, vchildren, entry, entry_def, incomplete );
    return true;
  }else if( varChCount==2 && n.getKind()==EQUAL ){
    Trace("ambqi-check-debug2") << "Construct variable equality..." << std::endl;
    //efficient expansion of the equality
    construct_var_eq( m, q, vchildren[0], vchildren[1], -1, -1 );
    return true;
  }else{
    return false;
  }
}

Node AbsDef::getFunctionValue( FirstOrderModelAbs * m, TNode op, std::vector< Node >& vars, unsigned depth ) {
  if( depth==vars.size() ){
    TypeNode tn = op.getType();
    if( tn.getNumChildren()>0 ){
      tn = tn[tn.getNumChildren()-1];
    }
    if( d_value>=0 ){
      Assert( d_value<(int)m->d_rep_set.d_type_reps[tn].size() );
      if( tn.isBoolean() ){
        return NodeManager::currentNM()->mkConst( d_value==1 );
      }else{
        return m->d_rep_set.d_type_reps[tn][d_value];
      }
    }else{
      return Node::null();
    }
  }else{
    TypeNode tn = vars[depth].getType();
    Node curr;
    curr = d_def[d_default].getFunctionValue( m, op, vars, depth+1 );
    for( std::map< unsigned, AbsDef >::iterator it = d_def.begin(); it != d_def.end(); ++it ){
      if( it->first!=d_default ){
        unsigned id = getId( it->first );
        Assert( id<m->d_rep_set.d_type_reps[tn].size() );
        TNode n = m->d_rep_set.d_type_reps[tn][id];
        Node fv = it->second.getFunctionValue( m, op, vars, depth+1 );
        if( !curr.isNull() && !fv.isNull() ){
          curr = NodeManager::currentNM()->mkNode( ITE, vars[depth].eqNode( n ), fv, curr );
        }else{
          curr = Node::null();
        }
      }
    }
    return curr;
  }
}

unsigned AbsDef::getId( unsigned n ) {
  Assert( n!=0 );
  unsigned index = 0;
  while( (n & ( 1 << index )) == 0 ){
    index++;
  }
  return index;
}

Node AbsDef::evaluate( FirstOrderModelAbs * m, TypeNode retTyp, std::vector< Node >& args ) {
  std::vector< unsigned > iargs;
  for( unsigned i=0; i<args.size(); i++ ){
    unsigned v = 1 << m->getRepresentativeId( args[i] );
    iargs.push_back( v );
  }
  return evaluate( m, retTyp, iargs, 0 );
}

Node AbsDef::evaluate( FirstOrderModelAbs * m, TypeNode retTyp, std::vector< unsigned >& iargs, unsigned depth ) {
  if( d_value!=-1 ){
    Assert( d_value>=0 && d_value<(int)m->d_rep_set.d_type_reps[retTyp].size() );
    return m->d_rep_set.d_type_reps[retTyp][d_value];
  }else{
    std::map< unsigned, AbsDef >::iterator it = d_def.find( iargs[depth] );
    if( it==d_def.end() ){
      return d_def[d_default].evaluate( m, retTyp, iargs, depth+1 );
    }else{
      return it->second.evaluate( m, retTyp, iargs, depth+1 );
    }
  }
}

AbsMbqiBuilder::AbsMbqiBuilder( context::Context* c, QuantifiersEngine* qe ) :
QModelBuilder( c, qe ){
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}


//------------------------model construction----------------------------

void AbsMbqiBuilder::processBuildModel(TheoryModel* m, bool fullModel) {
  Trace("ambqi-debug") << "process build model " << fullModel << std::endl;
  FirstOrderModel* f = (FirstOrderModel*)m;
  FirstOrderModelAbs* fm = f->asFirstOrderModelAbs();
  if( fullModel ){
    Trace("ambqi-model") << "Construct model representation..." << std::endl;
    //make function values
    for( std::map<Node, AbsDef * >::iterator it = fm->d_models.begin(); it != fm->d_models.end(); ++it ) {
      if( it->first.getType().getNumChildren()>1 ){
        Trace("ambqi-model") << "Construct for " << it->first << "..." << std::endl;
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
    fm->d_domain.clear();

    //initialize boolean sort
    TypeNode b = d_true.getType();
    fm->d_rep_set.d_type_reps[b].clear();
    fm->d_rep_set.d_type_reps[b].push_back( d_false );
    fm->d_rep_set.d_type_reps[b].push_back( d_true );
    fm->d_rep_id[d_false] = 0;
    fm->d_rep_id[d_true] = 1;

    //initialize unintpreted sorts
    Trace("ambqi-model") << std::endl << "Making representatives..." << std::endl;
    for( std::map< TypeNode, std::vector< Node > >::iterator it = fm->d_rep_set.d_type_reps.begin();
         it != fm->d_rep_set.d_type_reps.end(); ++it ){
      if( it->first.isSort() ){
        Assert( !it->second.empty() );
        //set the domain
        fm->d_domain[it->first] = 0;
        Trace("ambqi-model") << "Representatives for " << it->first << " : " << std::endl;
        for( unsigned i=0; i<it->second.size(); i++ ){
          if( i<32 ){
            fm->d_domain[it->first] |= ( 1 << i );
          }
          Trace("ambqi-model") << i << " : " << it->second[i] << std::endl;
          fm->d_rep_id[it->second[i]] = i;
        }
        if( it->second.size()>=32 ){
          fm->d_domain.erase( it->first );
        }
      }
    }

    Trace("ambqi-model") << std::endl << "Making function definitions..." << std::endl;
    //construct the models for functions
    for( std::map<Node, AbsDef * >::iterator it = fm->d_models.begin(); it != fm->d_models.end(); ++it ) {
      Node f = it->first;
      Trace("ambqi-model-debug") << "Building Model for " << f << std::endl;
      //reset the model
      //get all (non-redundant) f-applications
      std::vector< TNode > fapps;
      Trace("ambqi-model-debug") << "Initial terms: " << std::endl;
      for( size_t i=0; i<fm->d_uf_terms[f].size(); i++ ){
        Node n = fm->d_uf_terms[f][i];
        if( !n.getAttribute(NoMatchAttribute()) ){
          Trace("ambqi-model-debug") << "  " << n << " -> " << fm->getRepresentativeId( n ) << std::endl;
          fapps.push_back( n );
        }
      }
      if( fapps.empty() ){
        //choose arbitrary value
        Node mbt = d_qe->getTermDatabase()->getModelBasisOpTerm(f);
        Trace("ambqi-model-debug") << "Initial terms empty, add " << mbt << std::endl;
        fapps.push_back( mbt );
      }
      bool fValid = true;
      for( unsigned i=0; i<fapps[0].getNumChildren(); i++ ){
        if( fm->d_domain.find( fapps[0][i].getType() )==fm->d_domain.end() ){
          Trace("ambqi-model") << "Interpretation of " << f << " is not valid.";
          Trace("ambqi-model") << " (domain for " << fapps[0][i].getType() << " is too large)." << std::endl;
          fValid = false;
          break;
        }
      }
      fm->d_models_valid[f] = fValid;
      if( fValid ){
        //construct the ambqi model
        it->second->construct_func( fm, fapps );
        Trace("ambqi-model-debug") << "Interpretation of " << f << " : " << std::endl;
        it->second->debugPrint("ambqi-model-debug", fm, fapps[0] );

        it->second->simplify( fm, Node::null() );
        Trace("ambqi-model") << "(Simplified) interpretation of " << f << " : " << std::endl;
        it->second->debugPrint("ambqi-model", fm, fapps[0] );

/*
        if( Debug.isOn("ambqi-model-debug") ){
          for( size_t i=0; i<fm->d_uf_terms[f].size(); i++ ){
            Node e = it->second->evaluate_n( fm, fm->d_uf_terms[f][i] );
            Debug("ambqi-model-debug") << fm->d_uf_terms[f][i] << " evaluates to " << e << std::endl;
            Assert( fm->areEqual( e, fm->d_uf_terms[f][i] ) );
          }
        }
*/
      }
    }
  }
}


//--------------------model checking---------------------------------------

//do exhaustive instantiation
bool AbsMbqiBuilder::doExhaustiveInstantiation( FirstOrderModel * fm, Node q, int effort ) {
  Trace("ambqi-check") << "exhaustive instantiation " << q << " " << effort << std::endl;
  if (effort==0) {
    FirstOrderModelAbs * fma = fm->asFirstOrderModelAbs();
    bool quantValid = true;
    for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
      if( !fma->isValidType( q[0][i].getType() ) ){
        quantValid = false;
        Trace("ambqi-inst") << "Interpretation of " << q << " is not valid because of type " << q[0][i].getType() << std::endl;
        break;
      }
    }
    if( quantValid ){
      AbsDef ad;
      doCheck( fma, q, ad, q[1] );
      //now process entries
      Trace("ambqi-inst") << "Interpretation of " << q << " is : " << std::endl;
      ad.debugPrint( "ambqi-inst", fma, q );
      Trace("ambqi-inst") << std::endl;
      int lem = ad.addInstantiations( fma, d_qe, q );
      Trace("ambqi-inst") << "...Added " << lem << " lemmas." << std::endl;
      d_addedLemmas += lem;
    }
    return quantValid;
  }
  return true;
}

bool AbsMbqiBuilder::doCheck( FirstOrderModelAbs * m, TNode q, AbsDef & ad, TNode n ) {
  Assert( n.getKind()!=FORALL );
  std::map< unsigned, AbsDef > children;
  std::map< unsigned, int > bchildren;
  std::map< unsigned, int > vchildren;
  bool incomplete = false;
  int varChCount = 0;
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if( n[i].getKind()==FORALL ){
      bchildren[i] = -1;
      incomplete = true;
    }else if( n[i].getKind() == BOUND_VARIABLE ){
      varChCount++;
      vchildren[i] = m->getVariableId( q, n[i] );
    }else if( m->hasTerm( n[i] ) ){
      bchildren[i] = m->getRepresentativeId( n[i] );
    }else{
      if( !doCheck( m, q, children[i], n[i] ) ){
        bchildren[i] = -1;
        incomplete = true;
      }
    }
  }
  //convert to pointers
  std::map< unsigned, AbsDef * > pchildren;
  for( std::map< unsigned, AbsDef >::iterator it = children.begin(); it != children.end(); ++it ){
    pchildren[it->first] = &it->second;
  }
  //construct the interpretation
  Trace("ambqi-check-debug") << "Compute Interpretation of " << n << " " << n.getKind() << std::endl;
  if( n.getKind() == APPLY_UF || n.getKind() == VARIABLE || n.getKind() == SKOLEM ){
    Node op;
    if( n.getKind() == APPLY_UF ){
      op = n.getOperator();
    }else{
      op = n;
    }
    //uninterpreted compose
    if( m->d_models_valid[op] ){
      ad.construct( m, q, n, m->d_models[op], pchildren, bchildren, vchildren, varChCount, incomplete );
    }else{
      Trace("ambqi-check-debug") << "** Cannot produce interpretation for " << n << " (no function model)" << std::endl;
      return false;
    }
  }else if( !ad.construct( m, q, n, NULL, pchildren, bchildren, vchildren, varChCount, incomplete ) ){
    Trace("ambqi-check-debug") << "** Cannot produce interpretation for " << n << " (variables are children of interpreted symbol)" << std::endl;
    return false;
  }
  Trace("ambqi-check-debug2") << "Interpretation for " << n << " is : " << std::endl;
  ad.debugPrint("ambqi-check-debug2", m, q[0] );
  ad.simplify( m, q );
  Trace("ambqi-check-debug") << "(Simplified) Interpretation for " << n << " is : " << std::endl;
  ad.debugPrint("ambqi-check-debug", m, q[0] );
  Trace("ambqi-check-debug") << std::endl;
  return true;
}
