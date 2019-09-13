/*********************                                                        */
/*! \file full_model_check.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of full model check class
 **/

#include "theory/quantifiers/fmf/full_model_check.h"

#include "options/quantifiers_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_rep_bound_ext.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::inst;
using namespace CVC4::theory::quantifiers::fmcheck;

struct ModelBasisArgSort
{
  std::vector< Node > d_terms;
  // number of arguments that are model-basis terms
  std::unordered_map<Node, unsigned, NodeHashFunction> d_mba_count;
  bool operator() (int i,int j) {
    return (d_mba_count[d_terms[i]] < d_mba_count[d_terms[j]]);
  }
};

bool EntryTrie::hasGeneralization( FirstOrderModelFmc * m, Node c, int index ) {
  if (index==(int)c.getNumChildren()) {
    return d_data!=-1;
  }else{
    TypeNode tn = c[index].getType();
    Node st = m->getStar(tn);
    if(d_child.find(st)!=d_child.end()) {
      if( d_child[st].hasGeneralization(m, c, index+1) ){
        return true;
      }
    }
    if( c[index]!=st && d_child.find( c[index] )!=d_child.end() ){
      if( d_child[ c[index] ].hasGeneralization(m, c, index+1) ){
        return true;
      }
    }
    if( c[index].getType().isSort() ){
      //for star: check if all children are defined and have generalizations
      if( c[index]==st ){     ///options::fmfFmcCoverSimplify()
        //check if all children exist and are complete
        unsigned num_child_def =
            d_child.size() - (d_child.find(st) != d_child.end() ? 1 : 0);
        if (num_child_def == m->getRepSet()->getNumRepresentatives(tn))
        {
          bool complete = true;
          for ( std::map<Node,EntryTrie>::iterator it = d_child.begin(); it != d_child.end(); ++it ){
            if( !m->isStar(it->first) ){
              if( !it->second.hasGeneralization(m, c, index+1) ){
                complete = false;
                break;
              }
            }
          }
          if( complete ){
            return true;
          }
        }
      }
    }

    return false;
  }
}

int EntryTrie::getGeneralizationIndex( FirstOrderModelFmc * m, std::vector<Node> & inst, int index ) {
  Debug("fmc-entry-trie") << "Get generalization index " << inst.size() << " " << index << std::endl;
  if (index==(int)inst.size()) {
    return d_data;
  }else{
    int minIndex = -1;
    Node st = m->getStar(inst[index].getType());
    if (d_child.find(st) != d_child.end())
    {
      minIndex = d_child[st].getGeneralizationIndex(m, inst, index + 1);
    }
    Node cc = inst[index];
    if (cc != st && d_child.find(cc) != d_child.end())
    {
      int gindex = d_child[cc].getGeneralizationIndex(m, inst, index + 1);
      if (minIndex == -1 || (gindex != -1 && gindex < minIndex))
      {
        minIndex = gindex;
      }
    }
    return minIndex;
  }
}

void EntryTrie::addEntry( FirstOrderModelFmc * m, Node c, Node v, int data, int index ) {
  if (index==(int)c.getNumChildren()) {
    if(d_data==-1) {
      d_data = data;
    }
  }
  else {
    d_child[ c[index] ].addEntry(m,c,v,data,index+1);
    if( d_complete==0 ){
      d_complete = -1;
    }
  }
}

void EntryTrie::getEntries( FirstOrderModelFmc * m, Node c, std::vector<int> & compat, std::vector<int> & gen, int index, bool is_gen ) {
  if (index==(int)c.getNumChildren()) {
    if( d_data!=-1) {
      if( is_gen ){
        gen.push_back(d_data);
      }
      compat.push_back(d_data);
    }
  }else{
    if (m->isStar(c[index])) {
      for ( std::map<Node,EntryTrie>::iterator it = d_child.begin(); it != d_child.end(); ++it ){
        it->second.getEntries(m, c, compat, gen, index+1, is_gen );
      }
    }else{
      Node st = m->getStar(c[index].getType());
      if(d_child.find(st)!=d_child.end()) {
        d_child[st].getEntries(m, c, compat, gen, index+1, false);
      }
      if( d_child.find( c[index] )!=d_child.end() ){
        d_child[ c[index] ].getEntries(m, c, compat, gen, index+1, is_gen);
      }
    }

  }
}

bool Def::addEntry( FirstOrderModelFmc * m, Node c, Node v) {
  if (d_et.hasGeneralization(m, c)) {
    Trace("fmc-debug") << "Already has generalization, skip." << std::endl;
    return false;
  }
  int newIndex = (int)d_cond.size();
  if (!d_has_simplified) {
    std::vector<int> compat;
    std::vector<int> gen;
    d_et.getEntries(m, c, compat, gen);
    for( unsigned i=0; i<compat.size(); i++) {
      if( d_status[compat[i]]==status_unk ){
        if( d_value[compat[i]]!=v ){
          d_status[compat[i]] = status_non_redundant;
        }
      }
    }
    for( unsigned i=0; i<gen.size(); i++) {
      if( d_status[gen[i]]==status_unk ){
        if( d_value[gen[i]]==v ){
          d_status[gen[i]] = status_redundant;
        }
      }
    }
    d_status.push_back( status_unk );
  }
  d_et.addEntry(m, c, v, newIndex);
  d_cond.push_back(c);
  d_value.push_back(v);
  return true;
}

Node Def::evaluate( FirstOrderModelFmc * m, std::vector<Node>& inst ) {
  int gindex = d_et.getGeneralizationIndex(m, inst);
  if (gindex!=-1) {
    return d_value[gindex];
  }else{
    Trace("fmc-warn") << "Warning : evaluation came up null!" << std::endl;
    return Node::null();
  }
}

int Def::getGeneralizationIndex( FirstOrderModelFmc * m, std::vector<Node>& inst ) {
  return d_et.getGeneralizationIndex(m, inst);
}

void Def::basic_simplify( FirstOrderModelFmc * m ) {
  d_has_simplified = true;
  std::vector< Node > cond;
  cond.insert( cond.end(), d_cond.begin(), d_cond.end() );
  d_cond.clear();
  std::vector< Node > value;
  value.insert( value.end(), d_value.begin(), d_value.end() );
  d_value.clear();
  d_et.reset();
  for (unsigned i=0; i<d_status.size(); i++) {
    if( d_status[i]!=status_redundant ){
      addEntry(m, cond[i], value[i]);
    }
  }
  d_status.clear();
}

void Def::simplify(FullModelChecker * mc, FirstOrderModelFmc * m) {
  Trace("fmc-simplify") << "Simplify definition, #cond = " << d_cond.size() << std::endl;
  basic_simplify( m );
  Trace("fmc-simplify") << "post-basic simplify, #cond = " << d_cond.size() << std::endl;

  //check if the last entry is not all star, if so, we can make the last entry all stars
  if( !d_cond.empty() ){
    bool last_all_stars = true;
    Node cc = d_cond[d_cond.size()-1];
    for( unsigned i=0; i<cc.getNumChildren(); i++ ){
      if (!m->isStar(cc[i]))
      {
        last_all_stars = false;
        break;
      }
    }
    if( !last_all_stars ){
      Trace("fmc-cover-simplify") << "Need to modify last entry to be all stars." << std::endl;
      Trace("fmc-cover-simplify") << "Before: " << std::endl;
      debugPrint("fmc-cover-simplify",Node::null(), mc);
      Trace("fmc-cover-simplify") << std::endl;
      std::vector< Node > cond;
      cond.insert( cond.end(), d_cond.begin(), d_cond.end() );
      d_cond.clear();
      std::vector< Node > value;
      value.insert( value.end(), d_value.begin(), d_value.end() );
      d_value.clear();
      d_et.reset();
      d_has_simplified = false;
      //change the last to all star
      std::vector< Node > nc;
      nc.push_back( cc.getOperator() );
      for( unsigned j=0; j< cc.getNumChildren(); j++){
        nc.push_back(m->getStar(cc[j].getType()));
      }
      cond[cond.size()-1] = NodeManager::currentNM()->mkNode( APPLY_UF, nc );
      //re-add the entries
      for (unsigned i=0; i<cond.size(); i++) {
        addEntry(m, cond[i], value[i]);
      }
      Trace("fmc-cover-simplify") << "Finished re-adding entries." << std::endl;
      basic_simplify( m );
      Trace("fmc-cover-simplify") << "After: " << std::endl;
      debugPrint("fmc-cover-simplify",Node::null(), mc);
      Trace("fmc-cover-simplify") << std::endl;
    }
  }
  Trace("fmc-simplify") << "finish simplify, #cond = " << d_cond.size() << std::endl;
}

void Def::debugPrint(const char * tr, Node op, FullModelChecker * m) {
  if (!op.isNull()) {
    Trace(tr) << "Model for " << op << " : " << std::endl;
  }
  for( unsigned i=0; i<d_cond.size(); i++) {
    //print the condition
    if (!op.isNull()) {
      Trace(tr) << op;
    }
    m->debugPrintCond(tr, d_cond[i], true);
    Trace(tr) << " -> ";
    m->debugPrint(tr, d_value[i]);
    Trace(tr) << std::endl;
  }
}


FullModelChecker::FullModelChecker(context::Context* c, QuantifiersEngine* qe) :
QModelBuilder( c, qe ){
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

bool FullModelChecker::preProcessBuildModel(TheoryModel* m) {
  //standard pre-process
  if( !preProcessBuildModelStd( m ) ){
    return false;
  }
  
  FirstOrderModelFmc * fm = ((FirstOrderModelFmc*)m)->asFirstOrderModelFmc();
  Trace("fmc") << "---Full Model Check preprocess() " << std::endl;
  d_preinitialized_eqc.clear();
  d_preinitialized_types.clear();
  //traverse equality engine
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( fm->d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node r = *eqcs_i;
    TypeNode tr = r.getType();
    d_preinitialized_eqc[tr] = r;
    ++eqcs_i;
  }

  //must ensure model basis terms exists in model for each relevant type
  fm->initialize();
  for( std::map<Node, Def * >::iterator it = fm->d_models.begin(); it != fm->d_models.end(); ++it ) {
    Node op = it->first;
    Trace("fmc") << "preInitialize types for " << op << std::endl;
    TypeNode tno = op.getType();
    for( unsigned i=0; i<tno.getNumChildren(); i++) {
      Trace("fmc") << "preInitializeType " << tno[i] << std::endl;
      preInitializeType( fm, tno[i] );
    }
  }
  //do not have to introduce terms for sorts of domains of quantified formulas if we are allowed to assume empty sorts
  if( !options::fmfEmptySorts() ){
    for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
      Node q = fm->getAssertedQuantifier( i );
      //make sure all types are set
      for( unsigned j=0; j<q[0].getNumChildren(); j++ ){
        preInitializeType( fm, q[0][j].getType() );
      }
    }
  }
  return true;
}

bool FullModelChecker::processBuildModel(TheoryModel* m){
  if (!m->areFunctionValuesEnabled())
  {
    // nothing to do if no functions
    return true;
  }
  FirstOrderModelFmc * fm = ((FirstOrderModelFmc*)m)->asFirstOrderModelFmc();
  Trace("fmc") << "---Full Model Check reset() " << std::endl;
  d_quant_models.clear();
  d_rep_ids.clear();
  d_star_insts.clear();
  //process representatives
  RepSet* rs = fm->getRepSetPtr();
  for (std::map<TypeNode, std::vector<Node> >::iterator it =
           rs->d_type_reps.begin();
       it != rs->d_type_reps.end();
       ++it)
  {
    if( it->first.isSort() ){
      Trace("fmc") << "Cardinality( " << it->first << " )" << " = " << it->second.size() << std::endl;
      for( size_t a=0; a<it->second.size(); a++ ){
        Node r = fm->getRepresentative( it->second[a] );
        if( Trace.isOn("fmc-model-debug") ){
          std::vector< Node > eqc;
          d_qe->getEqualityQuery()->getEquivalenceClass( r, eqc );
          Trace("fmc-model-debug") << "   " << (it->second[a]==r);
          Trace("fmc-model-debug") << " : " << it->second[a] << " : " << r << " : ";
          //Trace("fmc-model-debug") << r2 << " : " << ir << " : ";
          Trace("fmc-model-debug") << " {";
          for( size_t i=0; i<eqc.size(); i++ ){
            Trace("fmc-model-debug") << eqc[i] << ", ";
          }
          Trace("fmc-model-debug") << "}" << std::endl;
        }
        d_rep_ids[it->first][r] = (int)a;
      }
      Trace("fmc-model-debug") << std::endl;
    }
  }

  //now, make models
  for( std::map<Node, Def * >::iterator it = fm->d_models.begin(); it != fm->d_models.end(); ++it ) {
    Node op = it->first;
    //reset the model
    fm->d_models[op]->reset();

    std::vector< Node > add_conds;
    std::vector< Node > add_values;      
    bool needsDefault = true;
    std::map< Node, std::vector< Node > >::iterator itut = fm->d_uf_terms.find( op );
    if( itut!=fm->d_uf_terms.end() ){
      Trace("fmc-model-debug") << itut->second.size() << " model values for " << op << " ... " << std::endl;
      for( size_t i=0; i<itut->second.size(); i++ ){
        Node n = itut->second[i];
        // only consider unique up to congruence (in model equality engine)?
        add_conds.push_back( n );
        add_values.push_back( n );
        Node r = fm->getRepresentative(n);
        Trace("fmc-model-debug") << n << " -> " << r << std::endl;
        //AlwaysAssert( fm->areEqual( itut->second[i], r ) );
      }
    }else{
      Trace("fmc-model-debug") << "No model values for " << op << " ... " << std::endl;
    }
    Trace("fmc-model-debug") << std::endl;
    //possibly get default
    if( needsDefault ){
      Node nmb = fm->getModelBasisOpTerm(op);
      //add default value if necessary
      if( fm->hasTerm( nmb ) ){
        Trace("fmc-model-debug") << "Add default " << nmb << std::endl;
        add_conds.push_back( nmb );
        add_values.push_back( nmb );
      }else{
        Node vmb = getSomeDomainElement(fm, nmb.getType());
        Trace("fmc-model-debug") << "Add default to default representative " << nmb << " ";
        Trace("fmc-model-debug")
            << fm->getRepSet()->getNumRepresentatives(nmb.getType())
            << std::endl;
        add_conds.push_back( nmb );
        add_values.push_back( vmb );
      }
    }

    std::vector< Node > conds;
    std::vector< Node > values;
    std::vector< Node > entry_conds;
    //get the entries for the model
    for( size_t i=0; i<add_conds.size(); i++ ){
      Node c = add_conds[i];
      Node v = add_values[i];
      Trace("fmc-model-debug")
          << "Add cond/value : " << c << " -> " << v << std::endl;
      std::vector< Node > children;
      std::vector< Node > entry_children;
      children.push_back(op);
      entry_children.push_back(op);
      bool hasNonStar = false;
      for( unsigned i=0; i<c.getNumChildren(); i++) {
        Node ri = fm->getRepresentative( c[i] );
        children.push_back(ri);
        bool isStar = false;
        if (fm->isModelBasisTerm(ri))
        {
          ri = fm->getStar(ri.getType());
          isStar = true;
        }
        else
        {
          hasNonStar = true;
        }
        if( !isStar && !ri.isConst() ){
          Trace("fmc-warn") << "Warning : model for " << op << " has non-constant argument in model " << ri << " (from " << c[i] << ")" << std::endl;
          Assert( false );
        }
        entry_children.push_back(ri);
      }
      Node n = NodeManager::currentNM()->mkNode( APPLY_UF, children );
      Node nv = fm->getRepresentative( v );
      Trace("fmc-model-debug")
          << "Representative of " << v << " is " << nv << std::endl;
      if( !nv.isConst() ){
        Trace("fmc-warn") << "Warning : model for " << op << " has non-constant value in model " << nv << std::endl;
        Assert( false );
      }
      Node en = (useSimpleModels() && hasNonStar) ? n : NodeManager::currentNM()->mkNode( APPLY_UF, entry_children );
      if( std::find(conds.begin(), conds.end(), n )==conds.end() ){
        Trace("fmc-model-debug") << "- add " << n << " -> " << nv << " (entry is " << en << ")" << std::endl;
        conds.push_back(n);
        values.push_back(nv);
        entry_conds.push_back(en);
      }
      else {
        Trace("fmc-model-debug") << "Already have entry for : " << n << " -> " << nv << " (entry is " << en << ")" << std::endl;
      }
    }


    //sort based on # default arguments
    std::vector< int > indices;
    ModelBasisArgSort mbas;
    for (int i=0; i<(int)conds.size(); i++) {
      mbas.d_terms.push_back(conds[i]);
      mbas.d_mba_count[conds[i]] = fm->getModelBasisArg(conds[i]);
      indices.push_back(i);
    }
    std::sort( indices.begin(), indices.end(), mbas );

    for (int i=0; i<(int)indices.size(); i++) {
      fm->d_models[op]->addEntry(fm, entry_conds[indices[i]], values[indices[i]]);
    }

    Trace("fmc-model-simplify") << "Before simplification : " << std::endl;
    fm->d_models[op]->debugPrint("fmc-model-simplify", op, this);
    Trace("fmc-model-simplify") << std::endl;

    Trace("fmc-model-simplify") << "Simplifying " << op << "..." << std::endl;
    fm->d_models[op]->simplify( this, fm );

    fm->d_models[op]->debugPrint("fmc-model", op, this);
    Trace("fmc-model") << std::endl;

    //for debugging
    /*
    for( size_t i=0; i<fm->d_uf_terms[op].size(); i++ ){
      std::vector< Node > inst;
      for( unsigned j=0; j<fm->d_uf_terms[op][i].getNumChildren(); j++ ){
        Node r = fm->getRepresentative( fm->d_uf_terms[op][i][j] );
        inst.push_back( r );
      }
      Node ev = fm->d_models[op]->evaluate( fm, inst );
      Trace("fmc-model-debug") << ".....Checking eval( " << fm->d_uf_terms[op][i] << " ) = " << ev << std::endl;
      AlwaysAssert( fm->areEqual( ev, fm->d_uf_terms[op][i] ) );
    }
    */
  }
  Assert( d_addedLemmas==0 );
  
  //make function values
  for( std::map<Node, Def * >::iterator it = fm->d_models.begin(); it != fm->d_models.end(); ++it ){
    Node f_def = getFunctionValue( fm, it->first, "$x" );
    m->assignFunctionDefinition( it->first, f_def );
  }
  return TheoryEngineModelBuilder::processBuildModel( m );
}

void FullModelChecker::preInitializeType( FirstOrderModelFmc * fm, TypeNode tn ){
  if( d_preinitialized_types.find( tn )==d_preinitialized_types.end() ){
    d_preinitialized_types[tn] = true;
    if (!tn.isFunction() || options::ufHo())
    {
      Node mb = fm->getModelBasisTerm(tn);
      // if the model basis term does not exist in the model,
      // either add it directly to the model's equality engine if no other terms
      // of this type exist, or otherwise assert that it is equal to the first
      // equivalence class of its type.
      if (!fm->hasTerm(mb) && !mb.isConst())
      {
        std::map<TypeNode, Node>::iterator itpe = d_preinitialized_eqc.find(tn);
        if (itpe == d_preinitialized_eqc.end())
        {
          Trace("fmc") << "...add model basis term to EE of model " << mb << " "
                       << tn << std::endl;
          fm->d_equalityEngine->addTerm(mb);
        }
        else
        {
          Trace("fmc") << "...add model basis eqc equality to model " << mb
                       << " == " << itpe->second << " " << tn << std::endl;
          bool ret = fm->assertEquality(mb, itpe->second, true);
          AlwaysAssert(ret);
        }
      }
    }
  }
}

void FullModelChecker::debugPrintCond(const char * tr, Node n, bool dispStar) {
  Trace(tr) << "(";
  for( unsigned j=0; j<n.getNumChildren(); j++) {
    if( j>0 ) Trace(tr) << ", ";
    debugPrint(tr, n[j], dispStar);
  }
  Trace(tr) << ")";
}

void FullModelChecker::debugPrint(const char * tr, Node n, bool dispStar) {
  FirstOrderModelFmc * fm = (FirstOrderModelFmc *)d_qe->getModel();
  if( n.isNull() ){
    Trace(tr) << "null";
  }
  else if(fm->isStar(n) && dispStar) {
    Trace(tr) << "*";
  }
  else
  {
    TypeNode tn = n.getType();
    if( tn.isSort() && d_rep_ids.find(tn)!=d_rep_ids.end() ){
      if (d_rep_ids[tn].find(n)!=d_rep_ids[tn].end()) {
        Trace(tr) << d_rep_ids[tn][n];
      }else{
        Trace(tr) << n;
      }
    }else{
      Trace(tr) << n;
    }
  }
}


int FullModelChecker::doExhaustiveInstantiation( FirstOrderModel * fm, Node f, int effort ) {
  Trace("fmc") << "Full model check " << f << ", effort = " << effort << "..." << std::endl;
  Assert( !d_qe->inConflict() );
  if( optUseModel() ){
    FirstOrderModelFmc * fmfmc = fm->asFirstOrderModelFmc();
    if (effort==0) {
      //register the quantifier
      if (d_quant_cond.find(f)==d_quant_cond.end()) {
        std::vector< TypeNode > types;
        for(unsigned i=0; i<f[0].getNumChildren(); i++){
          types.push_back(f[0][i].getType());
        }
        TypeNode typ = NodeManager::currentNM()->mkFunctionType( types, NodeManager::currentNM()->booleanType() );
        Node op = NodeManager::currentNM()->mkSkolem( "qfmc", typ, "op created for full-model checking" );
        d_quant_cond[f] = op;
      }

      if( options::mbqiMode()==MBQI_NONE ){
        //just exhaustive instantiate
        Node c = mkCondDefault( fmfmc, f );
        d_quant_models[f].addEntry( fmfmc, c, d_false );
        return exhaustiveInstantiate( fmfmc, f, c, -1);
      }else{
        //model check the quantifier
        doCheck(fmfmc, f, d_quant_models[f], f[1]);
        Trace("fmc") << "Definition for quantifier " << f << " is : " << std::endl;
        Assert( !d_quant_models[f].d_cond.empty() );
        d_quant_models[f].debugPrint("fmc", Node::null(), this);
        Trace("fmc") << std::endl;

        //consider all entries going to non-true
        for (unsigned i=0; i<d_quant_models[f].d_cond.size(); i++) {
          if( d_quant_models[f].d_value[i]!=d_true ) {
            Trace("fmc-inst") << "Instantiate based on " << d_quant_models[f].d_cond[i] << "..." << std::endl;
            bool hasStar = false;
            std::vector< Node > inst;
            for (unsigned j=0; j<d_quant_models[f].d_cond[i].getNumChildren(); j++) {
              if (fmfmc->isStar(d_quant_models[f].d_cond[i][j])) {
                hasStar = true;
                inst.push_back(fmfmc->getModelBasisTerm(d_quant_models[f].d_cond[i][j].getType()));
              }else{
                inst.push_back(d_quant_models[f].d_cond[i][j]);
              }
            }
            bool addInst = true;
            if( hasStar ){
              //try obvious (specified by inst)
              Node ev = d_quant_models[f].evaluate(fmfmc, inst);
              if (ev==d_true) {
                addInst = false;
                Trace("fmc-debug") << "...do not instantiate, evaluation was " << ev << std::endl;
              }
            }else{
              //for debugging
              if (Trace.isOn("fmc-test-inst")) {
                Node ev = d_quant_models[f].evaluate(fmfmc, inst);
                if( ev==d_true ){
                  Message() << "WARNING: instantiation was true! " << f << " "
                            << d_quant_models[f].d_cond[i] << std::endl;
                  AlwaysAssert(false);
                }else{
                  Trace("fmc-test-inst") << "...instantiation evaluated to false." << std::endl;
                }
              }
            }
            if( addInst ){
              if( options::fmfBound() ){
                std::vector< Node > cond;
                cond.push_back(d_quant_cond[f]);
                cond.insert( cond.end(), inst.begin(), inst.end() );
                //need to do exhaustive instantiate algorithm to set things properly (should only add one instance)
                Node c = mkCond( cond );
                unsigned prevInst = d_addedLemmas;
                exhaustiveInstantiate( fmfmc, f, c, -1 );
                if( d_addedLemmas==prevInst ){
                  d_star_insts[f].push_back(i);
                }
              }else{
                //just add the instance
                d_triedLemmas++;
                if (d_qe->getInstantiate()->addInstantiation(f, inst, true))
                {
                  Trace("fmc-debug-inst") << "** Added instantiation." << std::endl;
                  d_addedLemmas++;
                  if( d_qe->inConflict() || options::fmfOneInstPerRound() ){
                    break;
                  }
                }else{
                  Trace("fmc-debug-inst") << "** Instantiation was duplicate." << std::endl;
                  //this can happen if evaluation is unknown, or if we are generalizing a star that already has a value
                  //if( !hasStar && d_quant_models[f].d_value[i]==d_false ){
                  //  Trace("fmc-warn") << "**** FMC warning: inconsistent duplicate instantiation." << std::endl;
                  //}
                  //this assertion can happen if two instantiations from this round are identical
                  // (0,1)->false (1,0)->false   for   forall xy. f( x, y ) = f( y, x )
                  //Assert( hasStar || d_quant_models[f].d_value[i]!=d_false );
                  //might try it next effort level
                  d_star_insts[f].push_back(i);
                }
              }
            }else{
              Trace("fmc-debug-inst") << "** Instantiation was already true." << std::endl;
              //might try it next effort level
              d_star_insts[f].push_back(i);
            }
          }
        }
      }
    }else{
      if (!d_star_insts[f].empty()) {
        Trace("fmc-exh") << "Exhaustive instantiate " << f << std::endl;
        Trace("fmc-exh") << "Definition was : " << std::endl;
        d_quant_models[f].debugPrint("fmc-exh", Node::null(), this);
        Trace("fmc-exh") << std::endl;
        Def temp;
        //simplify the exceptions?
        for( int i=(d_star_insts[f].size()-1); i>=0; i--) {
          //get witness for d_star_insts[f][i]
          int j = d_star_insts[f][i];
          if( temp.addEntry(fmfmc, d_quant_models[f].d_cond[j], d_quant_models[f].d_value[j] ) ){
            if( !exhaustiveInstantiate(fmfmc, f, d_quant_models[f].d_cond[j], j ) ){
              //something went wrong, resort to exhaustive instantiation
              return 0;
            }
          }
        }
      }
    }
    return 1;
  }else{
    return 0;
  }
}

/** Representative bound fmc entry
 *
 * This bound information corresponds to one
 * entry in a term definition (see terminology in
 * Chapter 5 of Finite Model Finding for
 * Satisfiability Modulo Theories thesis).
 * For example, a term definition for the body
 * of a quantified formula:
 *   forall xyz. P( x, y, z )
 * may be:
 *   ( 0, 0, 0 ) -> false
 *   ( *, 1, 2 ) -> false
 *   ( *, *, * ) -> true
 * Indicating that the quantified formula evaluates
 * to false in the current model for x=0, y=0, z=0,
 * or y=1, z=2 for any x, and evaluates to true
 * otherwise.
 * This class is used if we wish
 * to iterate over all values corresponding to one
 * of these entries. For example, for the second entry:
 *   (*, 1, 2 )
 * we iterate over all values of x, but only {1}
 * for y and {2} for z.
 */
class RepBoundFmcEntry : public QRepBoundExt
{
 public:
  RepBoundFmcEntry(QuantifiersEngine* qe, Node e, FirstOrderModelFmc* f)
      : QRepBoundExt(qe), d_entry(e), d_fm(f)
  {
  }
  ~RepBoundFmcEntry() {}
  /** set bound */
  virtual RsiEnumType setBound(Node owner,
                               unsigned i,
                               std::vector<Node>& elements) override
  {
    if (!d_fm->isStar(d_entry[i]))
    {
      // only need to consider the single point
      elements.push_back(d_entry[i]);
      return ENUM_DEFAULT;
    }
    return QRepBoundExt::setBound(owner, i, elements);
  }

 private:
  /** the entry for this bound */
  Node d_entry;
  /** the model builder associated with this bound */
  FirstOrderModelFmc* d_fm;
};

bool FullModelChecker::exhaustiveInstantiate(FirstOrderModelFmc * fm, Node f, Node c, int c_index) {
  Trace("fmc-exh") << "----Exhaustive instantiate based on index " << c_index << " : " << c << " ";
  debugPrintCond("fmc-exh", c, true);
  Trace("fmc-exh")<< std::endl;
  RepBoundFmcEntry rbfe(d_qe, c, fm);
  RepSetIterator riter(d_qe->getModel()->getRepSet(), &rbfe);
  Trace("fmc-exh-debug") << "Set quantifier..." << std::endl;
  //initialize
  if (riter.setQuantifier(f))
  {
    Trace("fmc-exh-debug") << "Set element domains..." << std::endl;
    int addedLemmas = 0;
    //now do full iteration
    while( !riter.isFinished() ){
      d_triedLemmas++;
      Trace("fmc-exh-debug") << "Inst : ";
      std::vector< Node > ev_inst;
      std::vector< Node > inst;
      for (unsigned i = 0; i < riter.getNumTerms(); i++)
      {
        Node rr = riter.getCurrentTerm( i );
        Node r = rr;
        //if( r.getType().isSort() ){
        r = fm->getRepresentative( r );
        //}else{
        //  r = fm->getCurrentModelValue( r );
        //}
        debugPrint("fmc-exh-debug", r);
        Trace("fmc-exh-debug") << " (term : " << rr << ")";
        ev_inst.push_back( r );
        inst.push_back( rr );
      }
      int ev_index = d_quant_models[f].getGeneralizationIndex(fm, ev_inst);
      Trace("fmc-exh-debug") << ", index = " << ev_index << " / " << d_quant_models[f].d_value.size();
      Node ev = ev_index==-1 ? Node::null() : d_quant_models[f].d_value[ev_index];
      if (ev!=d_true) {
        Trace("fmc-exh-debug") << ", add!";
        //add as instantiation
        if (d_qe->getInstantiate()->addInstantiation(f, inst, true))
        {
          Trace("fmc-exh-debug")  << " ...success.";
          addedLemmas++;
          if( d_qe->inConflict() || options::fmfOneInstPerRound() ){
            break;
          }
        }else{
          Trace("fmc-exh-debug") << ", failed.";
        }
      }else{
        Trace("fmc-exh-debug") << ", already true";
      }
      Trace("fmc-exh-debug") << std::endl;
      int index = riter.increment();
      Trace("fmc-exh-debug") << "Incremented index " << index << std::endl;
      if( !riter.isFinished() ){
        if (index >= 0 && riter.d_index[index] > 0 && addedLemmas > 0
            && riter.d_enum_type[index] == ENUM_CUSTOM)
        {
          Trace("fmc-exh-debug")
              << "Since this is a custom enumeration, skip to the next..."
              << std::endl;
          riter.incrementAtIndex(index - 1);
        }
      }
    }
    d_addedLemmas += addedLemmas;
    Trace("fmc-exh") << "----Finished Exhaustive instantiate, lemmas = " << addedLemmas << ", incomplete=" << riter.isIncomplete() << std::endl;
    return addedLemmas>0 || !riter.isIncomplete();
  }else{
    Trace("fmc-exh") << "----Finished Exhaustive instantiate, failed." << std::endl;
    return !riter.isIncomplete();
  }
}

void FullModelChecker::doCheck(FirstOrderModelFmc * fm, Node f, Def & d, Node n ) {
  Trace("fmc-debug") << "Check " << n << " " << n.getKind() << std::endl;
  //first check if it is a bounding literal
  if( n.hasAttribute(BoundIntLitAttribute()) ){
    Trace("fmc-debug") << "It is a bounding literal, polarity = " << n.getAttribute(BoundIntLitAttribute()) << std::endl;
    d.addEntry(fm, mkCondDefault(fm, f), n.getAttribute(BoundIntLitAttribute())==1 ? d_false : d_true );
  }else if( n.getKind() == kind::BOUND_VARIABLE ){
    Trace("fmc-debug") << "Add default entry..." << std::endl;
    d.addEntry(fm, mkCondDefault(fm, f), n);
  }
  else if( n.getKind() == kind::NOT ){
    //just do directly
    doCheck( fm, f, d, n[0] );
    doNegate( d );
  }
  else if( n.getKind() == kind::FORALL ){
    d.addEntry(fm, mkCondDefault(fm, f), Node::null());
  }
  else if( n.getType().isArray() ){
    //Trace("fmc-warn") << "WARNING : ARRAYS : Can't process base array " << r << std::endl;
    //Trace("fmc-warn") << "          Default value was : " << odefaultValue << std::endl;
    //Trace("fmc-debug") << "Can't process base array " << r << std::endl;
    //can't process this array
    d.reset();
    d.addEntry(fm, mkCondDefault(fm, f), Node::null());
  }
  else if( n.getNumChildren()==0 ){
    Node r = n;
    if( !n.isConst() ){
      if( !fm->hasTerm(n) ){
        r = getSomeDomainElement(fm, n.getType() );
      }
      r = fm->getRepresentative( r );
    }
    Trace("fmc-debug") << "Add constant entry..." << std::endl;
    d.addEntry(fm, mkCondDefault(fm, f), r);
  }
  else{
    std::vector< int > var_ch;
    std::vector< Def > children;
    for( int i=0; i<(int)n.getNumChildren(); i++) {
      Def dc;
      doCheck(fm, f, dc, n[i]);
      children.push_back(dc);
      if( n[i].getKind() == kind::BOUND_VARIABLE ){
        var_ch.push_back(i);
      }
    }

    if( n.getKind()==APPLY_UF ){
      Trace("fmc-debug") << "Do uninterpreted compose " << n << std::endl;
      //uninterpreted compose
      doUninterpretedCompose( fm, f, d, n.getOperator(), children );
      /*
    } else if( n.getKind()==SELECT ){
      Trace("fmc-debug") << "Do select compose " << n << std::endl;
      std::vector< Def > children2;
      children2.push_back( children[1] );
      std::vector< Node > cond;
      mkCondDefaultVec(fm, f, cond);
      std::vector< Node > val;
      doUninterpretedCompose(fm, f, d, children[0], children2, 0, cond, val );
      */
    } else {
      if( !var_ch.empty() ){
        if( n.getKind()==EQUAL && !n[0].getType().isBoolean() ){
          if( var_ch.size()==2 ){
            Trace("fmc-debug") << "Do variable equality " << n << std::endl;
            doVariableEquality( fm, f, d, n );
          }else{
            Trace("fmc-debug") << "Do variable relation " << n << std::endl;
            doVariableRelation( fm, f, d, var_ch[0]==0 ? children[1] : children[0], var_ch[0]==0 ? n[0] : n[1] );
          }
        }else{
          Trace("fmc-warn") << "Don't know how to check " << n << std::endl;
          d.addEntry(fm, mkCondDefault(fm, f), Node::null());
        }
      }else{
        Trace("fmc-debug") << "Do interpreted compose " << n << std::endl;
        std::vector< Node > cond;
        mkCondDefaultVec(fm, f, cond);
        std::vector< Node > val;
        //interpreted compose
        doInterpretedCompose( fm, f, d, n, children, 0, cond, val );
      }
    }
    Trace("fmc-debug") << "Simplify the definition..." << std::endl;
    d.debugPrint("fmc-debug", Node::null(), this);
    d.simplify(this, fm);
    Trace("fmc-debug") << "Done simplifying" << std::endl;
  }
  Trace("fmc-debug") << "Definition for " << n << " is : " << std::endl;
  d.debugPrint("fmc-debug", Node::null(), this);
  Trace("fmc-debug") << std::endl;
}

void FullModelChecker::doNegate( Def & dc ) {
  for (unsigned i=0; i<dc.d_cond.size(); i++) {
    if (!dc.d_value[i].isNull()) {
      dc.d_value[i] = dc.d_value[i]==d_true ? d_false : ( dc.d_value[i]==d_false ? d_true : dc.d_value[i] );
    }
  }
}

void FullModelChecker::doVariableEquality( FirstOrderModelFmc * fm, Node f, Def & d, Node eq ) {
  std::vector<Node> cond;
  mkCondDefaultVec(fm, f, cond);
  if (eq[0]==eq[1]){
    d.addEntry(fm, mkCond(cond), d_true);
  }else{
    TypeNode tn = eq[0].getType();
    if( tn.isSort() ){
      int j = fm->getVariableId(f, eq[0]);
      int k = fm->getVariableId(f, eq[1]);
      const RepSet* rs = fm->getRepSet();
      if (!rs->hasType(tn))
      {
        getSomeDomainElement( fm, tn );  //to verify the type is initialized
      }
      unsigned nreps = rs->getNumRepresentatives(tn);
      for (unsigned i = 0; i < nreps; i++)
      {
        Node r = fm->getRepresentative(rs->getRepresentative(tn, i));
        cond[j+1] = r;
        cond[k+1] = r;
        d.addEntry( fm, mkCond(cond), d_true);
      }
      d.addEntry( fm, mkCondDefault(fm, f), d_false);
    }else{
      d.addEntry( fm, mkCondDefault(fm, f), Node::null());
    }
  }
}

void FullModelChecker::doVariableRelation( FirstOrderModelFmc * fm, Node f, Def & d, Def & dc, Node v) {
  int j = fm->getVariableId(f, v);
  for (unsigned i=0; i<dc.d_cond.size(); i++) {
    Node val = dc.d_value[i];
    if( val.isNull() ){
      d.addEntry( fm, dc.d_cond[i], val);
    }else{
      if( dc.d_cond[i][j]!=val ){
        if (fm->isStar(dc.d_cond[i][j])) {
          std::vector<Node> cond;
          mkCondVec(dc.d_cond[i],cond);
          cond[j+1] = val;
          d.addEntry(fm, mkCond(cond), d_true);
          cond[j+1] = fm->getStar(val.getType());
          d.addEntry(fm, mkCond(cond), d_false);
        }else{
          d.addEntry( fm, dc.d_cond[i], d_false);
        }
      }else{
        d.addEntry( fm, dc.d_cond[i], d_true);
      }
    }
  }
}

void FullModelChecker::doUninterpretedCompose( FirstOrderModelFmc * fm, Node f, Def & d, Node op, std::vector< Def > & dc ) {
  Trace("fmc-uf-debug") << "Definition : " << std::endl;
  fm->d_models[op]->debugPrint("fmc-uf-debug", op, this);
  Trace("fmc-uf-debug") << std::endl;

  std::vector< Node > cond;
  mkCondDefaultVec(fm, f, cond);
  std::vector< Node > val;
  doUninterpretedCompose( fm, f, d, *fm->d_models[op], dc, 0, cond, val);
}

void FullModelChecker::doUninterpretedCompose( FirstOrderModelFmc * fm, Node f, Def & d,
                                               Def & df, std::vector< Def > & dc, int index,
                                               std::vector< Node > & cond, std::vector<Node> & val ) {
  Trace("fmc-uf-process") << "process at " << index << std::endl;
  for( unsigned i=1; i<cond.size(); i++) {
    debugPrint("fmc-uf-process", cond[i], true);
    Trace("fmc-uf-process") << " ";
  }
  Trace("fmc-uf-process") << std::endl;
  if (index==(int)dc.size()) {
    //we have an entry, now do actual compose
    std::map< int, Node > entries;
    doUninterpretedCompose2( fm, f, entries, 0, cond, val, df.d_et);
    if( entries.empty() ){
      d.addEntry(fm, mkCond(cond), Node::null());
    }else{
      //add them to the definition
      for( unsigned e=0; e<df.d_cond.size(); e++ ){
        if ( entries.find(e)!=entries.end() ){
          Trace("fmf-uf-process-debug") << "Add entry..." << std::endl;
          d.addEntry(fm, entries[e], df.d_value[e] );
          Trace("fmf-uf-process-debug") << "Done add entry." << std::endl;
        }
      }
    }
  }else{
    for (unsigned i=0; i<dc[index].d_cond.size(); i++) {
      if (isCompat(fm, cond, dc[index].d_cond[i])!=0) {
        std::vector< Node > new_cond;
        new_cond.insert(new_cond.end(), cond.begin(), cond.end());
        if( doMeet(fm, new_cond, dc[index].d_cond[i]) ){
          Trace("fmc-uf-process") << "index " << i << " succeeded meet." << std::endl;
          val.push_back(dc[index].d_value[i]);
          doUninterpretedCompose(fm, f, d, df, dc, index+1, new_cond, val);
          val.pop_back();
        }else{
          Trace("fmc-uf-process") << "index " << i << " failed meet." << std::endl;
        }
      }
    }
  }
}

void FullModelChecker::doUninterpretedCompose2( FirstOrderModelFmc * fm, Node f,
                                                std::map< int, Node > & entries, int index,
                                                std::vector< Node > & cond, std::vector< Node > & val,
                                                EntryTrie & curr ) {
  Trace("fmc-uf-process") << "compose " << index << " / " << val.size() << std::endl;
  for( unsigned i=1; i<cond.size(); i++) {
    debugPrint("fmc-uf-process", cond[i], true);
    Trace("fmc-uf-process") << " ";
  }
  Trace("fmc-uf-process") << std::endl;
  if (index==(int)val.size()) {
    Node c = mkCond(cond);
    Trace("fmc-uf-entry") << "Entry : " << c << " -> index[" << curr.d_data << "]" << std::endl;
    entries[curr.d_data] = c;
  }else{
    Node v = val[index];
    Trace("fmc-uf-process") << "Process " << v << std::endl;
    bool bind_var = false;
    if( !v.isNull() && v.getKind()==kind::BOUND_VARIABLE ){
      int j = fm->getVariableId(f, v);
      Trace("fmc-uf-process") << v << " is variable #" << j << std::endl;
      if (!fm->isStar(cond[j + 1]))
      {
        v = cond[j+1];
      }else{
        bind_var = true;
      }
    }
    if (bind_var) {
      Trace("fmc-uf-process") << "bind variable..." << std::endl;
      int j = fm->getVariableId(f, v);
      Assert(fm->isStar(cond[j + 1]));
      for (std::map<Node, EntryTrie>::iterator it = curr.d_child.begin();
           it != curr.d_child.end();
           ++it)
      {
        cond[j + 1] = it->first;
        doUninterpretedCompose2(
            fm, f, entries, index + 1, cond, val, it->second);
      }
      cond[j + 1] = fm->getStar(v.getType());
    }else{
      if( !v.isNull() ){
        if (curr.d_child.find(v) != curr.d_child.end())
        {
          Trace("fmc-uf-process") << "follow value..." << std::endl;
          doUninterpretedCompose2(
              fm, f, entries, index + 1, cond, val, curr.d_child[v]);
        }
        Node st = fm->getStar(v.getType());
        if (curr.d_child.find(st) != curr.d_child.end())
        {
          Trace("fmc-uf-process") << "follow star..." << std::endl;
          doUninterpretedCompose2(
              fm, f, entries, index + 1, cond, val, curr.d_child[st]);
        }
      }
    }
  }
}

void FullModelChecker::doInterpretedCompose( FirstOrderModelFmc * fm, Node f, Def & d, Node n,
                                             std::vector< Def > & dc, int index,
                                             std::vector< Node > & cond, std::vector<Node> & val ) {
  Trace("fmc-if-process") << "int compose " << index << " / " << dc.size() << std::endl;
  for( unsigned i=1; i<cond.size(); i++) {
    debugPrint("fmc-if-process", cond[i], true);
    Trace("fmc-if-process") << " ";
  }
  Trace("fmc-if-process") << std::endl;
  if ( index==(int)dc.size() ){
    Node c = mkCond(cond);
    Node v = evaluateInterpreted(n, val);
    d.addEntry(fm, c, v);
  }
  else {
    TypeNode vtn = n.getType();
    for (unsigned i=0; i<dc[index].d_cond.size(); i++) {
      if (isCompat(fm, cond, dc[index].d_cond[i])!=0) {
        std::vector< Node > new_cond;
        new_cond.insert(new_cond.end(), cond.begin(), cond.end());
        if( doMeet(fm, new_cond, dc[index].d_cond[i]) ){
          bool process = true;
          if (vtn.isBoolean()) {
            //short circuit
            if( (n.getKind()==OR && dc[index].d_value[i]==d_true) ||
                (n.getKind()==AND && dc[index].d_value[i]==d_false) ){
              Node c = mkCond(new_cond);
              d.addEntry(fm, c, dc[index].d_value[i]);
              process = false;
            }
          }
          if (process) {
            val.push_back(dc[index].d_value[i]);
            doInterpretedCompose(fm, f, d, n, dc, index+1, new_cond, val);
            val.pop_back();
          }
        }
      }
    }
  }
}

int FullModelChecker::isCompat( FirstOrderModelFmc * fm, std::vector< Node > & cond, Node c ) {
  Trace("fmc-debug3") << "isCompat " << c << std::endl;
  Assert(cond.size()==c.getNumChildren()+1);
  for (unsigned i=1; i<cond.size(); i++) {
    if (cond[i] != c[i - 1] && !fm->isStar(cond[i]) && !fm->isStar(c[i - 1]))
    {
      return 0;
    }
  }
  return 1;
}

bool FullModelChecker::doMeet( FirstOrderModelFmc * fm, std::vector< Node > & cond, Node c ) {
  Trace("fmc-debug3") << "doMeet " << c << std::endl;
  Assert(cond.size()==c.getNumChildren()+1);
  for (unsigned i=1; i<cond.size(); i++) {
    if( cond[i]!=c[i-1] ) {
      if (fm->isStar(cond[i]))
      {
        cond[i] = c[i - 1];
      }
      else if (!fm->isStar(c[i - 1]))
      {
        return false;
      }
    }
  }
  return true;
}

Node FullModelChecker::mkCond( std::vector< Node > & cond ) {
  return NodeManager::currentNM()->mkNode(APPLY_UF, cond);
}

Node FullModelChecker::mkCondDefault( FirstOrderModelFmc * fm, Node f) {
  std::vector< Node > cond;
  mkCondDefaultVec(fm, f, cond);
  return mkCond(cond);
}

void FullModelChecker::mkCondDefaultVec( FirstOrderModelFmc * fm, Node f, std::vector< Node > & cond ) {
  Trace("fmc-debug") << "Make default vec" << std::endl;
  //get function symbol for f
  cond.push_back(d_quant_cond[f]);
  for (unsigned i=0; i<f[0].getNumChildren(); i++) {
    Node ts = fm->getStar(f[0][i].getType());
    Assert( ts.getType()==f[0][i].getType() );
    cond.push_back(ts);
  }
}

void FullModelChecker::mkCondVec( Node n, std::vector< Node > & cond ) {
  cond.push_back(n.getOperator());
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    cond.push_back( n[i] );
  }
}

Node FullModelChecker::evaluateInterpreted( Node n, std::vector< Node > & vals ) {
  if( n.getKind()==EQUAL && !n[0].getType().isBoolean() ){
    if (!vals[0].isNull() && !vals[1].isNull()) {
      return vals[0]==vals[1] ? d_true : d_false;
    }else{
      return Node::null();
    }
  }else if( n.getKind()==ITE ){
    if( vals[0]==d_true ){
      return vals[1];
    }else if( vals[0]==d_false ){
      return vals[2];
    }else{
      return vals[1]==vals[2] ? vals[1] : Node::null();
    }
  }else if( n.getKind()==AND || n.getKind()==OR ){
    bool isNull = false;
    for (unsigned i=0; i<vals.size(); i++) {
      if((vals[i]==d_true && n.getKind()==OR) || (vals[i]==d_false && n.getKind()==AND)) {
        return vals[i];
      }else if( vals[i].isNull() ){
        isNull = true;
      }
    }
    return isNull ? Node::null() : vals[0];
  }else{
    std::vector<Node> children;
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
      children.push_back( n.getOperator() );
    }
    for (unsigned i=0; i<vals.size(); i++) {
      if( vals[i].isNull() ){
        return Node::null();
      }else{
        children.push_back( vals[i] );
      }
    }
    Node nc = NodeManager::currentNM()->mkNode(n.getKind(), children);
    Trace("fmc-eval") << "Evaluate " << nc << " to ";
    nc = Rewriter::rewrite(nc);
    Trace("fmc-eval") << nc << std::endl;
    return nc;
  }
}

Node FullModelChecker::getSomeDomainElement( FirstOrderModelFmc * fm, TypeNode tn ) {
  bool addRepId = !fm->getRepSet()->hasType(tn);
  Node de = fm->getSomeDomainElement(tn);
  if( addRepId ){
    d_rep_ids[tn][de] = 0;
  }
  return de;
}

Node FullModelChecker::getFunctionValue(FirstOrderModelFmc * fm, Node op, const char* argPrefix ) {
  return fm->getFunctionValue(op, argPrefix);
}


bool FullModelChecker::useSimpleModels() {
  return options::fmfFmcSimple();
}
