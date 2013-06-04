
/*********************                                                        */
/*! \file full_model_check.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of full model check class
 **/

#include "theory/quantifiers/full_model_check.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/options.h"

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
  bool operator() (int i,int j) {
    return (d_terms[i].getAttribute(ModelBasisArgAttribute()) <
            d_terms[j].getAttribute(ModelBasisArgAttribute()) );
  }
};


bool EntryTrie::hasGeneralization( FirstOrderModelFmc * m, Node c, int index ) {
  if (index==(int)c.getNumChildren()) {
    return d_data!=-1;
  }else{
    Node st = m->getStar(c[index].getType());
    if(d_child.find(st)!=d_child.end()) {
      if( d_child[st].hasGeneralization(m, c, index+1) ){
        return true;
      }
    }
    if( d_child.find( c[index] )!=d_child.end() ){
      if( d_child[ c[index] ].hasGeneralization(m, c, index+1) ){
        return true;
      }
    }
    return false;
  }
}

int EntryTrie::getGeneralizationIndex( FirstOrderModelFmc * m, std::vector<Node> & inst, int index ) {
  if (index==(int)inst.size()) {
    return d_data;
  }else{
    int minIndex = -1;
    Node st = m->getStar(inst[index].getType());
    if(d_child.find(st)!=d_child.end()) {
      minIndex = d_child[st].getGeneralizationIndex(m, inst, index+1);
    }
    Node cc = inst[index];
    if( d_child.find( cc )!=d_child.end() ){
      int gindex = d_child[ cc ].getGeneralizationIndex(m, inst, index+1);
      if (minIndex==-1 || (gindex!=-1 && gindex<minIndex) ){
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
  if (!d_et.hasGeneralization(m, c)) {
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
  }else{
    return false;
  }
}

Node Def::evaluate( FirstOrderModelFmc * m, std::vector<Node>& inst ) {
  int gindex = d_et.getGeneralizationIndex(m, inst);
  if (gindex!=-1) {
    return d_value[gindex];
  }else{
    return Node::null();
  }
}

int Def::getGeneralizationIndex( FirstOrderModelFmc * m, std::vector<Node>& inst ) {
  return d_et.getGeneralizationIndex(m, inst);
}

void Def::simplify(FirstOrderModelFmc * m) {
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

void FullModelChecker::processBuildModel(TheoryModel* m, bool fullModel){
  d_addedLemmas = 0;
  FirstOrderModelFmc * fm = ((FirstOrderModelFmc*)m)->asFirstOrderModelFmc();
  if( fullModel ){
    //make function values
    for( std::map< Node, std::vector< Node > >::iterator it = m->d_uf_terms.begin(); it != m->d_uf_terms.end(); ++it ){
      m->d_uf_models[ it->first ] = getFunctionValue( fm, it->first, "$x" );
    }
    TheoryEngineModelBuilder::processBuildModel( m, fullModel );
    //mark that the model has been set
    fm->markModelSet();
    //debug the model
    debugModel( fm );
  }else{
    Trace("fmc") << "---Full Model Check reset() " << std::endl;
    fm->initialize( d_considerAxioms );
    d_quant_models.clear();
    d_rep_ids.clear();
    d_star_insts.clear();
    //process representatives
    for( std::map< TypeNode, std::vector< Node > >::iterator it = fm->d_rep_set.d_type_reps.begin();
         it != fm->d_rep_set.d_type_reps.end(); ++it ){
      if( it->first.isSort() ){
        Trace("fmc") << "Cardinality( " << it->first << " )" << " = " << it->second.size() << std::endl;
        Node mbt = d_qe->getTermDatabase()->getModelBasisTerm(it->first);
        Node rmbt = fm->getUsedRepresentative( mbt);
        int mbt_index = -1;
        Trace("fmc") << "  Model basis term : " << mbt << std::endl;
        for( size_t a=0; a<it->second.size(); a++ ){
          Node r = fm->getUsedRepresentative( it->second[a] );
          std::vector< Node > eqc;
          ((EqualityQueryQuantifiersEngine*)d_qe->getEqualityQuery())->getEquivalenceClass( r, eqc );
          Trace("fmc-model-debug") << "   " << (it->second[a]==r) << (r==mbt);
          Trace("fmc-model-debug") << " : " << it->second[a] << " : " << r << " : ";
          //Trace("fmc-model-debug") << r2 << " : " << ir << " : ";
          Trace("fmc-model-debug") << " {";
          //find best selection for representative
          for( size_t i=0; i<eqc.size(); i++ ){
            Trace("fmc-model-debug") << eqc[i] << ", ";
          }
          Trace("fmc-model-debug") << "}" << std::endl;

          //if this is the model basis eqc, replace with actual model basis term
          if (r==rmbt || (mbt_index==-1 && a==(it->second.size()-1))) {
            fm->d_model_basis_rep[it->first] = r;
            r = mbt;
            mbt_index = a;
          }
          d_rep_ids[it->first][r] = (int)a;
        }
        Trace("fmc-model-debug") << std::endl;

        if (mbt_index==-1) {
          std::cout << "   WARNING: model basis term is not a representative!" << std::endl;
          exit(0);
        }else{
          Trace("fmc") << "Star index for " << it->first << " is " << mbt_index << std::endl;
        }
      }
    }
    //also process non-rep set sorts
    for( std::map<Node, Def * >::iterator it = fm->d_models.begin(); it != fm->d_models.end(); ++it ) {
      Node op = it->first;
      TypeNode tno = op.getType();
      for( unsigned i=0; i<tno.getNumChildren(); i++) {
        TypeNode tn = tno[i];
        if( fm->d_model_basis_rep.find( tn )==fm->d_model_basis_rep.end() ){
          Node mbn = d_qe->getTermDatabase()->getModelBasisTerm(tn);
          fm->d_model_basis_rep[tn] = fm->getUsedRepresentative( mbn );
        }
      }
    }
    //now, make models
    for( std::map<Node, Def * >::iterator it = fm->d_models.begin(); it != fm->d_models.end(); ++it ) {
      Node op = it->first;
      //reset the model
      fm->d_models[op]->reset();

      std::vector< Node > conds;
      std::vector< Node > values;
      std::vector< Node > entry_conds;
      Trace("fmc-model-debug") << fm->d_uf_terms[op].size() << " model values for " << op << " ... " << std::endl;
      for( size_t i=0; i<fm->d_uf_terms[op].size(); i++ ){
        Node r = fm->getUsedRepresentative(fm->d_uf_terms[op][i]);
        Trace("fmc-model-debug") << fm->d_uf_terms[op][i] << " -> " << r << std::endl;
      }
      Trace("fmc-model-debug") << std::endl;
      //initialize the model
      for( size_t i=0; i<fm->d_uf_terms[op].size(); i++ ){
        Node n = fm->d_uf_terms[op][i];
        if( !n.getAttribute(NoMatchAttribute()) ){
          addEntry(fm, op, n, n, conds, values, entry_conds);
        }
      }
      Node nmb = d_qe->getTermDatabase()->getModelBasisOpTerm(op);
      //add default value
      if( fm->hasTerm( nmb ) ){
        Trace("fmc-model-debug") << "Add default " << nmb << std::endl;
        addEntry(fm, op, nmb, nmb, conds, values, entry_conds);
      }else{
        Node vmb = getSomeDomainElement(fm, nmb.getType());
        Trace("fmc-model-debug") << "Add default to default representative " << nmb << " ";
        Trace("fmc-model-debug") << fm->d_rep_set.d_type_reps[nmb.getType()].size() << std::endl;
        addEntry(fm, op, nmb, vmb, conds, values, entry_conds);
      }

      //sort based on # default arguments
      std::vector< int > indices;
      ModelBasisArgSort mbas;
      for (int i=0; i<(int)conds.size(); i++) {
        d_qe->getTermDatabase()->computeModelBasisArgAttribute( conds[i] );
        mbas.d_terms.push_back(conds[i]);
        indices.push_back(i);
      }
      std::sort( indices.begin(), indices.end(), mbas );


      for (int i=0; i<(int)indices.size(); i++) {
        fm->d_models[op]->addEntry(fm, entry_conds[indices[i]], values[indices[i]]);
      }
      fm->d_models[op]->debugPrint("fmc-model", op, this);
      Trace("fmc-model") << std::endl;

      fm->d_models[op]->simplify( fm );
      Trace("fmc-model-simplify") << "After simplification : " << std::endl;
      fm->d_models[op]->debugPrint("fmc-model-simplify", op, this);
      Trace("fmc-model-simplify") << std::endl;
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
  }else{
    TypeNode tn = n.getType();
    if( d_rep_ids.find(tn)!=d_rep_ids.end() ){
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


bool FullModelChecker::doExhaustiveInstantiation( FirstOrderModel * fm, Node f, int effort, int & lemmas ) {
  Trace("fmc") << "Full model check " << f << ", effort = " << effort << "..." << std::endl;
  if (!options::fmfModelBasedInst()) {
    return false;
  }else{
    FirstOrderModelFmc * fmfmc = fm->asFirstOrderModelFmc();
    if (effort==0) {
      //register the quantifier
      if (d_quant_cond.find(f)==d_quant_cond.end()) {
        std::vector< TypeNode > types;
        for(unsigned i=0; i<f[0].getNumChildren(); i++){
          types.push_back(f[0][i].getType());
          d_quant_var_id[f][f[0][i]] = i;
        }
        TypeNode typ = NodeManager::currentNM()->mkFunctionType( types, NodeManager::currentNM()->booleanType() );
        Node op = NodeManager::currentNM()->mkSkolem( "fmc_$$", typ, "op created for full-model checking" );
        d_quant_cond[f] = op;
      }

      //model check the quantifier
      doCheck(fmfmc, f, d_quant_models[f], f[1]);
      Trace("fmc") << "Definition for quantifier " << f << " is : " << std::endl;
      d_quant_models[f].debugPrint("fmc", Node::null(), this);
      Trace("fmc") << std::endl;
      //consider all entries going to false
      for (unsigned i=0; i<d_quant_models[f].d_cond.size(); i++) {
        if( d_quant_models[f].d_value[i]!=d_true) {
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
            }
          }else{
            //for debugging
            if (Trace.isOn("fmc-test-inst")) {
              Node ev = d_quant_models[f].evaluate(fmfmc, inst);
              if( ev==d_true ){
                std::cout << "WARNING: instantiation was true! " << f << " " << d_quant_models[f].d_cond[i] << std::endl;
                exit(0);
              }else{
                Trace("fmc-test-inst") << "...instantiation evaluated to false." << std::endl;
              }
            }
          }
          if( addInst ){
            InstMatch m;
            for( unsigned j=0; j<inst.size(); j++) {
              m.set( d_qe, f, j, inst[j] );
            }
            if( d_qe->addInstantiation( f, m ) ){
              lemmas++;
            }else{
              //this can happen if evaluation is unknown
              //might try it next effort level
              d_star_insts[f].push_back(i);
            }
          }else{
            //might try it next effort level
            d_star_insts[f].push_back(i);
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
            int lem = exhaustiveInstantiate(fmfmc, f, d_quant_models[f].d_cond[j], j );
            if( lem==-1 ){
              //something went wrong, resort to exhaustive instantiation
              return false;
            }else{
              lemmas += lem;
            }
          }
        }
      }
    }
    return true;
  }
}

int FullModelChecker::exhaustiveInstantiate(FirstOrderModelFmc * fm, Node f, Node c, int c_index) {
  int addedLemmas = 0;
  RepSetIterator riter( d_qe, &(fm->d_rep_set) );
  Trace("fmc-exh") << "Exhaustive instantiate based on index " << c_index << " : " << c << " ";
  debugPrintCond("fmc-exh", c, true);
  Trace("fmc-exh")<< std::endl;
  if( riter.setQuantifier( f ) ){
    std::vector< RepDomain > dom;
    for (unsigned i=0; i<c.getNumChildren(); i++) {
      if (riter.d_enum_type[i]==RepSetIterator::ENUM_DOMAIN_ELEMENTS) {
        TypeNode tn = c[i].getType();
        if( d_rep_ids.find(tn)!=d_rep_ids.end() ){
          if( fm->isStar(c[i]) ){
            //add the full range
          }else{
            if (d_rep_ids[tn].find(c[i])!=d_rep_ids[tn].end()) {
              riter.d_domain[i].clear();
              riter.d_domain[i].push_back(d_rep_ids[tn][c[i]]);
            }else{
              return -1;
            }
          }
        }else{
          return -1;
        }
      }
    }
    //now do full iteration
    while( !riter.isFinished() ){
      Trace("fmc-exh-debug") << "Inst : ";
      std::vector< Node > inst;
      for( int i=0; i<riter.getNumTerms(); i++ ){
        //m.set( d_quantEngine, f, riter.d_index_order[i], riter.getTerm( i ) );
        Node r = fm->getUsedRepresentative( riter.getTerm( i ) );
        debugPrint("fmc-exh-debug", r);
        Trace("fmc-exh-debug") << " ";
        inst.push_back(r);
      }

      int ev_index = d_quant_models[f].getGeneralizationIndex(fm, inst);
      Trace("fmc-exh-debug") << ", index = " << ev_index;
      Node ev = ev_index==-1 ? Node::null() : d_quant_models[f].d_value[ev_index];
      if (ev!=d_true) {
        InstMatch m;
        for( int i=0; i<riter.getNumTerms(); i++ ){
          m.set( d_qe, f, i, riter.getTerm( i ) );
        }
        Trace("fmc-exh-debug") << ", add!";
        //add as instantiation
        if( d_qe->addInstantiation( f, m ) ){
          addedLemmas++;
        }
      }
      Trace("fmc-exh-debug") << std::endl;
      riter.increment();
    }
  }
  return addedLemmas;
}

void FullModelChecker::doCheck(FirstOrderModelFmc * fm, Node f, Def & d, Node n ) {
  Trace("fmc-debug") << "Check " << n << " " << n.getKind() << std::endl;
  if( n.getKind() == kind::BOUND_VARIABLE ){
    d.addEntry(fm, mkCondDefault(fm, f), n);
    Trace("fmc-debug") << "Done with " << n << " " << n.getKind() << std::endl;
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
    //make the definition
    Node r = fm->getRepresentative(n);
    Trace("fmc-debug") << "Representative for array is " << r << std::endl;
    while( r.getKind() == kind::STORE ){
      Node i = fm->getUsedRepresentative( r[1] );
      Node e = fm->getUsedRepresentative( r[2] );
      d.addEntry(fm, mkArrayCond(i), e );
      r = r[0];
    }
    Node defC = mkArrayCond(fm->getStar(n.getType().getArrayIndexType()));
    bool success = false;
    if( r.getKind() == kind::STORE_ALL ){
      ArrayStoreAll storeAll = r.getConst<ArrayStoreAll>();
      Node defaultValue = Node::fromExpr(storeAll.getExpr());
      defaultValue = fm->getUsedRepresentative( defaultValue, true );
      if( !defaultValue.isNull() ){
        d.addEntry(fm, defC, defaultValue);
        success = true;
      }
    }
    if( !success ){
      Trace("fmc-debug") << "Can't process base array " << r << std::endl;
      //can't process this array
      d.reset();
      d.addEntry(fm, defC, Node::null());
    }
  }
  else if( n.getNumChildren()==0 ){
    Node r = n;
    if( !fm->hasTerm(n) ){
      r = getSomeDomainElement(fm, n.getType() );
    }
    r = fm->getUsedRepresentative( r);
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
    } else if( n.getKind()==SELECT ){
      Trace("fmc-debug") << "Do select compose " << n << std::endl;
      std::vector< Def > children2;
      children2.push_back( children[1] );
      std::vector< Node > cond;
      mkCondDefaultVec(fm, f, cond);
      std::vector< Node > val;
      doUninterpretedCompose(fm, f, d, children[0], children2, 0, cond, val );
    } else {
      if( !var_ch.empty() ){
        if( n.getKind()==EQUAL ){
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
    d.simplify(fm);
  }
  Trace("fmc-debug") << "Definition for " << n << " is : " << std::endl;
  d.debugPrint("fmc-debug", Node::null(), this);
  Trace("fmc-debug") << std::endl;
}

void FullModelChecker::doNegate( Def & dc ) {
  for (unsigned i=0; i<dc.d_cond.size(); i++) {
    if (!dc.d_value[i].isNull()) {
      dc.d_value[i] = dc.d_value[i]==d_true ? d_false : d_true;
    }
  }
}

void FullModelChecker::doVariableEquality( FirstOrderModelFmc * fm, Node f, Def & d, Node eq ) {
  std::vector<Node> cond;
  mkCondDefaultVec(fm, f, cond);
  if (eq[0]==eq[1]){
    d.addEntry(fm, mkCond(cond), d_true);
  }else{
    int j = getVariableId(f, eq[0]);
    int k = getVariableId(f, eq[1]);
    TypeNode tn = eq[0].getType();
    if( !fm->d_rep_set.hasType( tn ) ){
      getSomeDomainElement( fm, tn );  //to verify the type is initialized
    }
    for (unsigned i=0; i<fm->d_rep_set.d_type_reps[tn].size(); i++) {
      Node r = fm->getUsedRepresentative( fm->d_rep_set.d_type_reps[tn][i] );
      cond[j+1] = r;
      cond[k+1] = r;
      d.addEntry( fm, mkCond(cond), d_true);
    }
    d.addEntry( fm, mkCondDefault(fm, f), d_false);
  }
}

void FullModelChecker::doVariableRelation( FirstOrderModelFmc * fm, Node f, Def & d, Def & dc, Node v) {
  int j = getVariableId(f, v);
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
          d.addEntry(fm, entries[e], df.d_value[e] );
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
  Trace("fmc-uf-process") << "compose " << index << std::endl;
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
    bool bind_var = false;
    if( !v.isNull() && v.getKind()==kind::BOUND_VARIABLE ){
      int j = getVariableId(f, v);
      Trace("fmc-uf-process") << v << " is variable #" << j << std::endl;
      if (!fm->isStar(cond[j+1])) {
        v = cond[j+1];
      }else{
        bind_var = true;
      }
    }
    if (bind_var) {
      Trace("fmc-uf-process") << "bind variable..." << std::endl;
      int j = getVariableId(f, v);
      for (std::map<Node, EntryTrie>::iterator it = curr.d_child.begin(); it != curr.d_child.end(); ++it) {
        cond[j+1] = it->first;
        doUninterpretedCompose2(fm, f, entries, index+1, cond, val, it->second);
      }
      cond[j+1] = fm->getStar(v.getType());
    }else{
      if( !v.isNull() ){
        if (curr.d_child.find(v)!=curr.d_child.end()) {
          Trace("fmc-uf-process") << "follow value..." << std::endl;
          doUninterpretedCompose2(fm, f, entries, index+1, cond, val, curr.d_child[v]);
        }
        Node st = fm->getStar(v.getType());
        if (curr.d_child.find(st)!=curr.d_child.end()) {
          Trace("fmc-uf-process") << "follow star..." << std::endl;
          doUninterpretedCompose2(fm, f, entries, index+1, cond, val, curr.d_child[st]);
        }
      }
    }
  }
}

void FullModelChecker::doInterpretedCompose( FirstOrderModelFmc * fm, Node f, Def & d, Node n,
                                             std::vector< Def > & dc, int index,
                                             std::vector< Node > & cond, std::vector<Node> & val ) {
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
  Assert(cond.size()==c.getNumChildren()+1);
  for (unsigned i=1; i<cond.size(); i++) {
    if( cond[i]!=c[i-1] && !fm->isStar(cond[i]) && !fm->isStar(c[i-1]) ) {
      return 0;
    }
  }
  return 1;
}

bool FullModelChecker::doMeet( FirstOrderModelFmc * fm, std::vector< Node > & cond, Node c ) {
  Assert(cond.size()==c.getNumChildren()+1);
  for (unsigned i=1; i<cond.size(); i++) {
    if( cond[i]!=c[i-1] ) {
      if( fm->isStar(cond[i]) ){
        cond[i] = c[i-1];
      }else if( !fm->isStar(c[i-1]) ){
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
  //get function symbol for f
  cond.push_back(d_quant_cond[f]);
  for (unsigned i=0; i<f[0].getNumChildren(); i++) {
    Node ts = fm->getStar( f[0][i].getType() );
    cond.push_back(ts);
  }
}

void FullModelChecker::mkCondVec( Node n, std::vector< Node > & cond ) {
  cond.push_back(n.getOperator());
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    cond.push_back( n[i] );
  }
}

Node FullModelChecker::mkArrayCond( Node a ) {
  if( d_array_term_cond.find(a)==d_array_term_cond.end() ){
    if( d_array_cond.find(a.getType())==d_array_cond.end() ){
      TypeNode typ = NodeManager::currentNM()->mkFunctionType( a.getType(), NodeManager::currentNM()->booleanType() );
      Node op = NodeManager::currentNM()->mkSkolem( "fmc_$$", typ, "op created for full-model checking" );
      d_array_cond[a.getType()] = op;
    }
    std::vector< Node > cond;
    cond.push_back(d_array_cond[a.getType()]);
    cond.push_back(a);
    d_array_term_cond[a] = NodeManager::currentNM()->mkNode(APPLY_UF, cond );
  }
  return d_array_term_cond[a];
}

Node FullModelChecker::evaluateInterpreted( Node n, std::vector< Node > & vals ) {
  if( n.getKind()==EQUAL ){
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
  bool addRepId = !fm->d_rep_set.hasType( tn );
  Node de = fm->getSomeDomainElement(tn);
  if( addRepId ){
    d_rep_ids[tn][de] = 0;
  }
  return de;
}

Node FullModelChecker::getFunctionValue(FirstOrderModelFmc * fm, Node op, const char* argPrefix ) {
  return fm->getFunctionValue(op, argPrefix);
}



void FullModelChecker::addEntry( FirstOrderModelFmc * fm, Node op, Node c, Node v,
                                   std::vector< Node > & conds,
                                   std::vector< Node > & values,
                                   std::vector< Node > & entry_conds ) {
  std::vector< Node > children;
  std::vector< Node > entry_children;
  children.push_back(op);
  entry_children.push_back(op);
  bool hasNonStar = false;
  for( unsigned i=0; i<c.getNumChildren(); i++) {
    Node ri = fm->getUsedRepresentative( c[i]);
    children.push_back(ri);
    if (fm->isModelBasisTerm(ri)) {
      ri = fm->getStar( ri.getType() );
    }else{
      hasNonStar = true;
    }
    entry_children.push_back(ri);
  }
  Node n = NodeManager::currentNM()->mkNode( APPLY_UF, children );
  Node nv = fm->getUsedRepresentative( v);
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

bool FullModelChecker::useSimpleModels() {
  return options::fmfFullModelCheckSimple();
}
