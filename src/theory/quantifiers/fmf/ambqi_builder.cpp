/*********************                                                        */
/*! \file ambqi_builder.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of abstract MBQI builder
 **/

#include "theory/quantifiers/fmf/ambqi_builder.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {


void AbsDef::construct_func( FirstOrderModelAbs * m, std::vector< TNode >& fapps, unsigned depth ) {
  d_def.clear();
  Assert( !fapps.empty() );
  if( depth==fapps[0].getNumChildren() ){
    //if( fapps.size()>1 ){
    //  for( unsigned i=0; i<fapps.size(); i++ ){
    //    std::cout << "...." << fapps[i] << " -> " << m->getRepresentativeId( fapps[i] ) << std::endl;
    //  }
    //}
    //get representative in model for this term
    d_value = m->getRepresentativeId( fapps[0] );
    Assert( d_value!=val_none );
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
      const RepSet* rs = m->getRepSet();
      debugPrintUInt("abs-model-debug",
                     rs->getNumRepresentatives(tn),
                     fapp_child_index[it->first]);
      Trace("abs-model-debug") << " : " << it->second.size() << " terms." << std::endl;
      d_def[fapp_child_index[it->first]].construct_func( m, it->second, depth+1 );
    }
  }
}

void AbsDef::simplify( FirstOrderModelAbs * m, TNode q, TNode n, unsigned depth ) {
  if( d_value==val_none && !d_def.empty() ){
    //process the default
    std::map< unsigned, AbsDef >::iterator defd = d_def.find( d_default );
    Assert( defd!=d_def.end() );
    unsigned newDef = d_default;
    std::vector< unsigned > to_erase;
    defd->second.simplify( m, q, n, depth+1 );
    int defVal = defd->second.d_value;
    bool isConstant = ( defVal!=val_none );
    //process each child
    for( std::map< unsigned, AbsDef >::iterator it = d_def.begin(); it != d_def.end(); ++it ){
      if( it->first!=d_default ){
        it->second.simplify( m, q, n, depth+1 );
        if( it->second.d_value==defVal && it->second.d_value!=val_none ){
          newDef = newDef | it->first;
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
      d_def[d_default].construct_def_entry( m, q, n, defVal, depth+1 );
      //erase redundant entries
      for( unsigned i=0; i<to_erase.size(); i++ ){
        d_def.erase( to_erase[i] );
      }
    }
    //if constant, propagate the value upwards
    if( isConstant ){
      d_value = defVal;
    }else{
      d_value = val_none;
    }
  }
}

void AbsDef::debugPrintUInt( const char * c, unsigned dSize, unsigned u ) const{
  for( unsigned i=0; i<dSize; i++ ){
    Trace(c) << ( ( u & ( 1 << i ) )!=0 ? "1" : "0");
  }
  //Trace(c) << "(";
  //for( unsigned i=0; i<32; i++ ){
  //  Trace(c) << ( ( u & ( 1 << i ) )!=0 ? "1" : "0");
  //}
  //Trace(c) << ")";
}

void AbsDef::debugPrint( const char * c, FirstOrderModelAbs * m, TNode f, unsigned depth ) const{
  if( Trace.isOn(c) ){
    if( depth==f.getNumChildren() ){
      for( unsigned i=0; i<depth; i++ ){ Trace(c) << "  ";}
      Trace(c) << "V[" << d_value << "]" << std::endl;
    }else{
      TypeNode tn = f[depth].getType();
      const RepSet* rs = m->getRepSet();
      unsigned dSize = rs->getNumRepresentatives(tn);
      Assert( dSize<32 );
      for( std::map< unsigned, AbsDef >::const_iterator it = d_def.begin(); it != d_def.end(); ++it ){
        for( unsigned i=0; i<depth; i++ ){ Trace(c) << "  ";}
        debugPrintUInt( c, dSize, it->first );
        if( it->first==d_default ){
          Trace(c) << "*";
        }
        if( it->second.d_value!=val_none ){
          Trace(c) << " -> V[" << it->second.d_value << "]";
        }
        Trace(c) << std::endl;
        it->second.debugPrint( c, m, f, depth+1 );
      }
    }
  }
}

bool AbsDef::addInstantiations( FirstOrderModelAbs * m, QuantifiersEngine * qe, TNode q, std::vector< Node >& terms, int& inst, unsigned depth ) {
  if( inst==0 || !options::fmfOneInstPerRound() ){
    if( d_value==1 ){
      //instantiations are all true : ignore this
      return true;
    }else{
      if( depth==q[0].getNumChildren() ){
        if (qe->getInstantiate()->addInstantiation(q, terms, true))
        {
          Trace("ambqi-inst-debug") << "-> Added instantiation." << std::endl;
          inst++;
          return true;
        }else{
          Trace("ambqi-inst-debug") << "-> Failed to add instantiation." << std::endl;
          //we are incomplete
          return false;
        }
      }else{
        bool osuccess = true;
        TypeNode tn = m->getVariable( q, depth ).getType();
        for( std::map< unsigned, AbsDef >::iterator it = d_def.begin(); it != d_def.end(); ++it ){
          //get witness term
          unsigned index = 0;
          bool success;
          do {
            success = false;
            index = getId( it->first, index );
            if( index<32 ){
              const RepSet* rs = m->getRepSet();
              Assert(index < rs->getNumRepresentatives(tn));
              terms[m->d_var_order[q][depth]] =
                  rs->getRepresentative(tn, index);
              if( !it->second.addInstantiations( m, qe, q, terms, inst, depth+1 ) && inst==0 ){
                //if we are incomplete, and have not yet added an instantiation, keep trying
                index++;
                Trace("ambqi-inst-debug") << "At depth " << depth << ", failed branch, no instantiations and incomplete, increment index : " << index << std::endl;
              }else{
                success = true;
              }
            }
          }while( !qe->inConflict() && !success && index<32 );
          //mark if we are incomplete
          osuccess = osuccess && success;
        }
        return osuccess;
      }
    }
  }else{
    return true;
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

void AbsDef::get_defs( unsigned u, std::vector< AbsDef * >& defs ) {
  for( std::map< unsigned, AbsDef >::iterator it = d_def.begin(); it != d_def.end(); ++it ){
    if( ( u & it->first )!=0 ){
      Assert( (u & it->first)==u );
      defs.push_back( &it->second );
    }
  }
}

void AbsDef::construct_normalize( FirstOrderModelAbs * m, TNode q, std::vector< AbsDef * >& defs, unsigned depth ) {
  if( depth==q[0].getNumChildren() ){
    Assert( defs.size()==1 );
    d_value = defs[0]->d_value;
  }else{
    TypeNode tn = m->getVariable( q, depth ).getType();
    unsigned def = m->d_domain[tn];
    for( unsigned i=0; i<defs.size(); i++ ){
      //process each simple child
      for( std::map< unsigned, AbsDef >::iterator itd = defs[i]->d_def.begin(); itd != defs[i]->d_def.end(); ++itd ){
        if( isSimple( itd->first ) && ( def & itd->first )!=0 ){
          def &= ~( itd->first );
          //process this value
          std::vector< AbsDef * > cdefs;
          for( unsigned j=0; j<defs.size(); j++ ){
            defs[j]->get_defs( itd->first, cdefs );
          }
          d_def[itd->first].construct_normalize( m, q, cdefs, depth+1 );
          if( def==0 ){
            d_default = itd->first;
            break;
          }
        }
      }
      if( def==0 ){
        break;
      }
    }
    if( def!=0 ){
      d_default = def;
      //process the default
      std::vector< AbsDef * > cdefs;
      for( unsigned j=0; j<defs.size(); j++ ){
        defs[j]->get_defs( d_default, cdefs );
      }
      d_def[d_default].construct_normalize( m, q, cdefs, depth+1 );
    }
  }
}

void AbsDef::construct_def_entry( FirstOrderModelAbs * m, TNode q, TNode n, int v, unsigned depth ) {
  d_value = v;
  if( depth<n.getNumChildren() ){
    TypeNode tn = q.isNull() ? n[depth].getType() : m->getVariable( q, depth ).getType();
    unsigned dom = m->d_domain[tn] ;
    d_def[dom].construct_def_entry( m, q, n, v, depth+1 );
    d_default = dom;
  }
}

void AbsDef::apply_ucompose( FirstOrderModelAbs * m, TNode q,
                             std::vector< unsigned >& entry, std::vector< bool >& entry_def,
                             std::vector< int >& terms, std::map< unsigned, int >& vchildren,
                             AbsDef * a, unsigned depth ) {
  if( depth==terms.size() ){
    if( Trace.isOn("ambqi-check-debug2") ){
      Trace("ambqi-check-debug2") << "Add entry ( ";
      const RepSet* rs = m->getRepSet();
      for( unsigned i=0; i<entry.size(); i++ ){
        unsigned dSize =
            rs->getNumRepresentatives(m->getVariable(q, i).getType());
        debugPrintUInt( "ambqi-check-debug2", dSize, entry[i] );
        Trace("ambqi-check-debug2") << " ";
      }
      Trace("ambqi-check-debug2") << ")" << std::endl;
    }
    a->construct_entry( entry, entry_def, d_value );
  }else{
    unsigned id;
    if( terms[depth]==val_none ){
      //a variable
      std::map< unsigned, int >::iterator itv = vchildren.find( depth );
      Assert( itv!=vchildren.end() );
      unsigned prev_v = entry[itv->second];
      bool prev_vd = entry_def[itv->second];
      for( std::map< unsigned, AbsDef >::iterator it = d_def.begin(); it != d_def.end(); ++it ){
        entry[itv->second] = it->first & prev_v;
        entry_def[itv->second] = ( it->first==d_default ) && prev_vd;
        if( entry[itv->second]!=0 ){
          it->second.apply_ucompose( m, q, entry, entry_def, terms, vchildren, a, depth+1 );
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
        it->second.apply_ucompose( m, q, entry, entry_def, terms, vchildren, a, depth+1 );
      }else{
        d_def[d_default].apply_ucompose( m, q, entry, entry_def, terms, vchildren, a, depth+1 );
      }
    }
  }
}

void AbsDef::construct_var_eq( FirstOrderModelAbs * m, TNode q, unsigned v1, unsigned v2, int curr, int currv, unsigned depth ) {
  if( depth==q[0].getNumChildren() ){
    Assert( currv!=val_none );
    d_value = currv;
  }else{
    TypeNode tn = m->getVariable( q, depth ).getType();
    unsigned dom = m->d_domain[tn];
    int vindex = depth==v1 ? 0 : ( depth==v2 ? 1 : val_none );
    if( vindex==val_none ){
      d_def[dom].construct_var_eq( m, q, v1, v2, curr, currv, depth+1 );
      d_default = dom;
    }else{
      Assert( currv==val_none );
      if( curr==val_none ){
        unsigned numReps = m->getRepSet()->getNumRepresentatives(tn);
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

void AbsDef::construct_var( FirstOrderModelAbs * m, TNode q, unsigned v, int currv, unsigned depth ) {
  if( depth==q[0].getNumChildren() ){
    Assert( currv!=val_none );
    d_value = currv;
  }else{
    TypeNode tn = m->getVariable( q, depth ).getType();
    if( v==depth ){
      unsigned numReps = m->getRepSet()->getNumRepresentatives(tn);
      Assert( numReps>0 && numReps < 32 );
      for( unsigned i=0; i<numReps; i++ ){
        d_def[ 1 << i ].construct_var( m, q, v, i, depth+1 );
      }
      d_default = 1 << (numReps - 1);
    }else{
      unsigned dom = m->d_domain[tn];
      d_def[dom].construct_var( m, q, v, currv, depth+1 );
      d_default = dom;
    }
  }
}

void AbsDef::construct_compose( FirstOrderModelAbs * m, TNode q, TNode n, AbsDef * f,
                                std::map< unsigned, AbsDef * >& children,
                                std::map< unsigned, int >& bchildren, std::map< unsigned, int >& vchildren,
                                std::vector< unsigned >& entry, std::vector< bool >& entry_def ) {
  const RepSet* rs = m->getRepSet();
  if( n.getKind()==OR || n.getKind()==AND ){
    // short circuiting
    for( std::map< unsigned, AbsDef * >::iterator it = children.begin(); it != children.end(); ++it ){
      if( ( it->second->d_value==0 && n.getKind()==AND ) ||
          ( it->second->d_value==1 && n.getKind()==OR ) ){
        //std::cout << "Short circuit " << it->second->d_value << " " << entry.size() << "/" << q[0].getNumChildren() << std::endl;
        unsigned count = q[0].getNumChildren() - entry.size();
        for( unsigned i=0; i<count; i++ ){
          entry.push_back( m->d_domain[m->getVariable( q, entry.size() ).getType()] );
          entry_def.push_back( true );
        }
        construct_entry( entry, entry_def, it->second->d_value );
        for( unsigned i=0; i<count; i++ ){
          entry.pop_back();
          entry_def.pop_back();
        }
        return;
      }
    }
  }
  if( entry.size()==q[0].getNumChildren() ){
    if( f ){
      if( Trace.isOn("ambqi-check-debug2") ){
        for( unsigned i=0; i<entry.size(); i++ ){ Trace("ambqi-check-debug2") << "  "; }
        Trace("ambqi-check-debug2") << "Evaluate uninterpreted function entry..." << std::endl;
      }
      //we are composing with an uninterpreted function
      std::vector< int > values;
      values.resize( n.getNumChildren(), val_none );
      for( std::map< unsigned, AbsDef * >::iterator it = children.begin(); it != children.end(); ++it ){
        values[it->first] = it->second->d_value;
      }
      for( std::map< unsigned, int >::iterator it = bchildren.begin(); it != bchildren.end(); ++it ){
        values[it->first] = it->second;
      }
      //look up value(s)
      f->apply_ucompose( m, q, entry, entry_def, values, vchildren, this );
    }else{
      bool incomplete = false;
      //we are composing with an interpreted function
      std::vector< TNode > values;
      values.resize( n.getNumChildren(), TNode::null() );
      for( std::map< unsigned, AbsDef * >::iterator it = children.begin(); it != children.end(); ++it ){
        Trace("ambqi-check-debug2") << "composite : " << it->first << " : " << it->second->d_value;
        if( it->second->d_value>=0 ){
          if (it->second->d_value
              >= (int)rs->getNumRepresentatives(n[it->first].getType()))
          {
            std::cout << it->second->d_value << " " << n[it->first] << " "
                      << n[it->first].getType() << " "
                      << rs->getNumRepresentatives(n[it->first].getType())
                      << std::endl;
          }
          Assert(it->second->d_value
                 < (int)rs->getNumRepresentatives(n[it->first].getType()));
          values[it->first] = rs->getRepresentative(n[it->first].getType(),
                                                    it->second->d_value);
        }else{
          incomplete = true;
        }
        Trace("ambqi-check-debug2") << " ->> " << values[it->first] << std::endl;
      }
      for( std::map< unsigned, int >::iterator it = bchildren.begin(); it != bchildren.end(); ++it ){
        Trace("ambqi-check-debug2") << "   basic :  " << it->first << " : " << it->second;
        if( it->second>=0 ){
          Assert(it->second
                 < (int)rs->getNumRepresentatives(n[it->first].getType()));
          values[it->first] =
              rs->getRepresentative(n[it->first].getType(), it->second);
        }else{
          incomplete = true;
        }
        Trace("ambqi-check-debug2") << " ->> " << values[it->first] << std::endl;
      }
      Assert( vchildren.empty() );
      if( incomplete ){
        Trace("ambqi-check-debug2") << "Construct incomplete entry." << std::endl;

        //if a child is unknown, we must return unknown
        construct_entry( entry, entry_def, val_unk );
      }else{
        if( Trace.isOn("ambqi-check-debug2") ){
          for( unsigned i=0; i<entry.size(); i++ ){ Trace("ambqi-check-debug2") << "  "; }
          Trace("ambqi-check-debug2") << "Evaluate interpreted function entry ( ";
          for( unsigned i=0; i<values.size(); i++ ){
            Assert( !values[i].isNull() );
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
    TypeNode tn = m->getVariable( q, entry.size() ).getType();
    Assert( m->isValidType( tn ) );
    unsigned def = m->d_domain[tn];
    if( Trace.isOn("ambqi-check-debug2") ){
      for( unsigned i=0; i<entry.size(); i++ ){ Trace("ambqi-check-debug2") << "  "; }
      Trace("ambqi-check-debug2") << "Take product of arguments" << std::endl;
    }
    for( std::map< unsigned, AbsDef * >::iterator it = children.begin(); it != children.end(); ++it ){
      Assert( it->second!=NULL );
      //process each child
      for( std::map< unsigned, AbsDef >::iterator itd = it->second->d_def.begin(); itd != it->second->d_def.end(); ++itd ){
        if( itd->first!=it->second->d_default && ( def & itd->first )!=0 ){
          def &= ~( itd->first );
          //process this value
          std::map< unsigned, AbsDef * > cchildren;
          for( std::map< unsigned, AbsDef * >::iterator it2 = children.begin(); it2 != children.end(); ++it2 ){
            Assert( it2->second!=NULL );
            std::map< unsigned, AbsDef >::iterator itdf = it2->second->d_def.find( itd->first );
            if( itdf!=it2->second->d_def.end() ){
              cchildren[it2->first] = &itdf->second;
            }else{
              Assert( it2->second->getDefault()!=NULL );
              cchildren[it2->first] = it2->second->getDefault();
            }
          }
          if( Trace.isOn("ambqi-check-debug2") ){
            for( unsigned i=0; i<entry.size(); i++ ){ Trace("ambqi-check-debug2") << "  "; }
            Trace("ambqi-check-debug2") << "...process : ";
            debugPrintUInt("ambqi-check-debug2",
                           rs->getNumRepresentatives(tn),
                           itd->first);
            Trace("ambqi-check-debug2") << " " << children.size() << " " << cchildren.size() << std::endl;
          }
          entry.push_back( itd->first );
          entry_def.push_back( def==0 );
          construct_compose( m, q, n, f, cchildren, bchildren, vchildren, entry, entry_def );
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
      if( Trace.isOn("ambqi-check-debug2") ){
        for( unsigned i=0; i<entry.size(); i++ ){ Trace("ambqi-check-debug2") << "  "; }
        Trace("ambqi-check-debug2") << "Make default argument" << std::endl;
      }
      std::map< unsigned, AbsDef * > cdchildren;
      for( std::map< unsigned, AbsDef * >::iterator it = children.begin(); it != children.end(); ++it ){
        Assert( it->second->getDefault()!=NULL );
        cdchildren[it->first] = it->second->getDefault();
      }
      if( Trace.isOn("ambqi-check-debug2") ){
        for( unsigned i=0; i<entry.size(); i++ ){ Trace("ambqi-check-debug2") << "  "; }
        Trace("ambqi-check-debug2") << "...process default : ";
        debugPrintUInt(
            "ambqi-check-debug2", rs->getNumRepresentatives(tn), def);
        Trace("ambqi-check-debug2") << " " << children.size() << " " << cdchildren.size() << std::endl;
      }
      entry.push_back( def );
      entry_def.push_back( true );
      construct_compose( m, q, n, f, cdchildren, bchildren, vchildren, entry, entry_def );
      entry_def.pop_back();
      entry.pop_back();
    }
  }
}

bool AbsDef::construct( FirstOrderModelAbs * m, TNode q, TNode n, AbsDef * f,
                        std::map< unsigned, AbsDef * >& children,
                        std::map< unsigned, int >& bchildren, std::map< unsigned, int >& vchildren,
                        int varChCount ) {
  if( Trace.isOn("ambqi-check-debug3") ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      Trace("ambqi-check-debug3") << i << " : ";
      Trace("ambqi-check-debug3") << ((children.find( i )!=children.end()) ? "X" : ".");
      if( bchildren.find( i )!=bchildren.end() ){
        Trace("ambqi-check-debug3") << bchildren[i];
      }else{
        Trace("ambqi-check-debug3") << ".";
      }
      if( vchildren.find( i )!=vchildren.end() ){
        Trace("ambqi-check-debug3") << vchildren[i];
      }else{
        Trace("ambqi-check-debug3") << ".";
      }
      Trace("ambqi-check-debug3") << std::endl;
    }
    Trace("ambqi-check-debug3") << "varChCount : " << varChCount << std::endl;
  }
  if( varChCount==0 || f ){
    //short-circuit
    if( n.getKind()==AND || n.getKind()==OR ){
      for( std::map< unsigned, int >::iterator it = bchildren.begin(); it !=bchildren.end(); ++it ){
        if( ( it->second==0 && n.getKind()==AND ) ||
            ( it->second==1 && n.getKind()==OR ) ){
          construct_def_entry( m, q, q[0], it->second );
          return true;
        }
      }
    }
    Trace("ambqi-check-debug2") << "Construct compose..." << std::endl;
    std::vector< unsigned > entry;
    std::vector< bool > entry_def;
    if( f && varChCount>0 ){
      AbsDef unorm;
      unorm.construct_compose( m, q, n, f, children, bchildren, vchildren, entry, entry_def );
      //normalize
      std::vector< AbsDef* > defs;
      defs.push_back( &unorm );
      construct_normalize( m, q, defs );
    }else{
      construct_compose( m, q, n, f, children, bchildren, vchildren, entry, entry_def );
    }
    Assert( is_normalized() );
    //if( !is_normalized() ){
    //  std::cout << "NON NORMALIZED DEFINITION" << std::endl;
    //  exit( 10 );
    //}
    return true;
  }else if( varChCount==1 && ( n.getKind()==EQUAL && !n[0].getType().isBoolean() ) ){
    Trace("ambqi-check-debug2") << "Expand variable child..." << std::endl;
    //expand the variable based on its finite domain
    AbsDef a;
    a.construct_var( m, q, vchildren.begin()->second, val_none );
    children[vchildren.begin()->first] = &a;
    vchildren.clear();
    std::vector< unsigned > entry;
    std::vector< bool > entry_def;
    Trace("ambqi-check-debug2") << "Construct compose with variable..." << std::endl;
    construct_compose( m, q, n, f, children, bchildren, vchildren, entry, entry_def );
    return true;
  }else if( varChCount==2 && ( n.getKind()==EQUAL && !n[0].getType().isBoolean() ) ){
    Trace("ambqi-check-debug2") << "Construct variable equality..." << std::endl;
    //efficient expansion of the equality
    construct_var_eq( m, q, vchildren[0], vchildren[1], val_none, val_none );
    return true;
  }else{
    return false;
  }
}

void AbsDef::negate() {
  for( std::map< unsigned, AbsDef >::iterator it = d_def.begin(); it != d_def.end(); ++it ){
    it->second.negate();
  }
  if( d_value==0 ){
    d_value = 1;
  }else if( d_value==1 ){
    d_value = 0;
  }
}

Node AbsDef::getFunctionValue( FirstOrderModelAbs * m, TNode op, std::vector< Node >& vars, unsigned depth ) {
  const RepSet* rs = m->getRepSet();
  if( depth==vars.size() ){
    TypeNode tn = op.getType();
    if( tn.getNumChildren()>0 ){
      tn = tn[tn.getNumChildren() - 1];
    }
    if( d_value>=0 ){
      Assert(d_value < (int)rs->getNumRepresentatives(tn));
      if( tn.isBoolean() ){
        return NodeManager::currentNM()->mkConst( d_value==1 );
      }else{
        return rs->getRepresentative(tn, d_value);
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
        Assert(id < rs->getNumRepresentatives(tn));
        TNode n = rs->getRepresentative(tn, id);
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

bool AbsDef::isSimple( unsigned n ) {
  return (n & (n - 1))==0;
}

unsigned AbsDef::getId( unsigned n, unsigned start, unsigned end ) {
  Assert( n!=0 );
  while( (n & ( 1 << start )) == 0 ){
    start++;
    if( start==end ){
      return start;
    }
  }
  return start;
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
  if( d_value!=val_none ){
    if( d_value==val_unk ){
      return Node::null();
    }else{
      const RepSet* rs = m->getRepSet();
      Assert(d_value >= 0 && d_value < (int)rs->getNumRepresentatives(retTyp));
      return rs->getRepresentative(retTyp, d_value);
    }
  }else{
    std::map< unsigned, AbsDef >::iterator it = d_def.find( iargs[depth] );
    if( it==d_def.end() ){
      return d_def[d_default].evaluate( m, retTyp, iargs, depth+1 );
    }else{
      return it->second.evaluate( m, retTyp, iargs, depth+1 );
    }
  }
}

bool AbsDef::is_normalized() {
  for( std::map< unsigned, AbsDef >::iterator it1 = d_def.begin(); it1 != d_def.end(); ++it1 ){
    if( !it1->second.is_normalized() ){
      return false;
    }
    for( std::map< unsigned, AbsDef >::iterator it2 = d_def.begin(); it2 != d_def.end(); ++it2 ){
      if( it1->first!=it2->first && (( it1->first & it2->first )!=0) ){
        return false;
      }
    }
  }
  return true;
}

AbsMbqiBuilder::AbsMbqiBuilder( context::Context* c, QuantifiersEngine* qe ) :
QModelBuilder( c, qe ){
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}


//------------------------model construction----------------------------

bool AbsMbqiBuilder::processBuildModel(TheoryModel* m) {
  Trace("ambqi-debug") << "process build model " << std::endl;
  FirstOrderModel* f = (FirstOrderModel*)m;
  FirstOrderModelAbs* fm = f->asFirstOrderModelAbs();
  RepSet* rs = m->getRepSetPtr();
  fm->initialize();
  //process representatives
  fm->d_rep_id.clear();
  fm->d_domain.clear();

  //initialize boolean sort
  TypeNode b = d_true.getType();
  rs->d_type_reps[b].clear();
  rs->d_type_reps[b].push_back(d_false);
  rs->d_type_reps[b].push_back(d_true);
  fm->d_rep_id[d_false] = 0;
  fm->d_rep_id[d_true] = 1;

  //initialize unintpreted sorts
  Trace("ambqi-model") << std::endl << "Making representatives..." << std::endl;
  for (std::map<TypeNode, std::vector<Node> >::iterator it =
           rs->d_type_reps.begin();
       it != rs->d_type_reps.end();
       ++it)
  {
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
    it->second->clear();
    //get all (non-redundant) f-applications
    std::vector< TNode > fapps;
    Trace("ambqi-model-debug") << "Initial terms: " << std::endl;
    std::map< Node, std::vector< Node > >::iterator itut = fm->d_uf_terms.find( f );
    if( itut!=fm->d_uf_terms.end() ){
      for( size_t i=0; i<itut->second.size(); i++ ){
        Node n = itut->second[i];
        // only consider unique up to congruence (in model equality engine)?
        Trace("ambqi-model-debug") << "  " << n << " -> " << fm->getRepresentativeId( n ) << std::endl;
        fapps.push_back( n );
      }
    }
    if( fapps.empty() ){
      //choose arbitrary value
      Node mbt = fm->getModelBasisOpTerm(f);
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
      Trace("ambqi-model-debug") << "Simplifying " << f << "..." << std::endl;
      it->second->simplify( fm, TNode::null(), fapps[0] );
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
  Trace("ambqi-model") << "Construct model representation..." << std::endl;
  //make function values
  for( std::map<Node, AbsDef * >::iterator it = fm->d_models.begin(); it != fm->d_models.end(); ++it ) {
    if( it->first.getType().getNumChildren()>1 ){
      Trace("ambqi-model") << "Construct for " << it->first << "..." << std::endl;
      Node f_def = fm->getFunctionValue( it->first, "$x" );
      m->assignFunctionDefinition( it->first, f_def );
    }
  }
  Assert( d_addedLemmas==0 );
  return TheoryEngineModelBuilder::processBuildModel( m );
}


//--------------------model checking---------------------------------------

//do exhaustive instantiation
int AbsMbqiBuilder::doExhaustiveInstantiation( FirstOrderModel * fm, Node q, int effort ) {
  Trace("ambqi-check") << "Exhaustive instantiation " << q << " " << effort << std::endl;
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
      Trace("ambqi-check") << "Compute interpretation..." << std::endl;
      AbsDef ad;
      doCheck( fma, q, ad, q[1] );
      //now process entries
      Trace("ambqi-inst-debug") << "...Current : " << d_addedLemmas << std::endl;
      Trace("ambqi-inst") << "Interpretation of " << q << " is : " << std::endl;
      ad.debugPrint( "ambqi-inst", fma, q[0] );
      Trace("ambqi-inst") << std::endl;
      Trace("ambqi-check") << "Add instantiations..." << std::endl;
      int lem = 0;
      quantValid = ad.addInstantiations( fma, d_qe, q, lem );
      Trace("ambqi-inst") << "...Added " << lem << " lemmas." << std::endl;
      if( lem>0 ){
        //if we were incomplete but added at least one lemma, we are ok
        quantValid = true;
      }
      d_addedLemmas += lem;
      Trace("ambqi-inst-debug") << "...Total : " << d_addedLemmas << std::endl;
    }
    return quantValid ? 1 : 0;
  }else{
    return 1;
  }
}

bool AbsMbqiBuilder::doCheck( FirstOrderModelAbs * m, TNode q, AbsDef & ad, TNode n ) {
  Assert( n.getKind()!=FORALL );
  if( n.getKind()==NOT && n[0].getKind()!=FORALL ){
    doCheck( m, q, ad, n[0] );
    ad.negate();
    return true;
  }else{
    std::map< unsigned, AbsDef > children;
    std::map< unsigned, int > bchildren;
    std::map< unsigned, int > vchildren;
    int varChCount = 0;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( n[i].getKind()==FORALL ){
        bchildren[i] = AbsDef::val_unk;
      }else if( n[i].getKind() == BOUND_VARIABLE ){
        varChCount++;
        vchildren[i] = m->d_var_index[q][ m->getVariableId( q, n[i] ) ];
        //vchildren[i] = m->getVariableId( q, n[i] );
      }else if( m->hasTerm( n[i] ) ){
        bchildren[i] = m->getRepresentativeId( n[i] );
      }else{
        if( !doCheck( m, q, children[i], n[i] ) ){
          bchildren[i] = AbsDef::val_unk;
          children.erase( i );
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
        ad.construct( m, q, n, m->d_models[op], pchildren, bchildren, vchildren, varChCount );
      }else{
        Trace("ambqi-check-debug") << "** Cannot produce interpretation for " << n << " (no function model)" << std::endl;
        return false;
      }
    }else if( !ad.construct( m, q, n, NULL, pchildren, bchildren, vchildren, varChCount ) ){
      Trace("ambqi-check-debug") << "** Cannot produce interpretation for " << n << " (variables are children of interpreted symbol)" << std::endl;
      return false;
    }
    Trace("ambqi-check-try") << "Interpretation for " << n << " is : " << std::endl;
    ad.debugPrint("ambqi-check-try", m, q[0] );
    ad.simplify( m, q, q[0] );
    Trace("ambqi-check-debug") << "(Simplified) Interpretation for " << n << " is : " << std::endl;
    ad.debugPrint("ambqi-check-debug", m, q[0] );
    Trace("ambqi-check-debug") << std::endl;
    return true;
  }
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
