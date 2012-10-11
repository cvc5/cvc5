/*********************                                                        */
/*! \file model.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters, barrett
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of model class
 **/

#include "theory/model.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/type_enumerator.h"
#include "smt/options.h"
#include "theory/uf/theory_uf_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

TheoryModel::TheoryModel( context::Context* c, std::string name, bool enableFuncModels ) :
  d_substitutions(c), d_equalityEngine(c, name), d_enableFuncModels(enableFuncModels)
{
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
  // The kinds we are treating as function application in congruence
  d_equalityEngine.addFunctionKind(kind::APPLY_UF);
  d_equalityEngine.addFunctionKind(kind::SELECT);
  //  d_equalityEngine.addFunctionKind(kind::STORE);
  d_equalityEngine.addFunctionKind(kind::APPLY_CONSTRUCTOR);
  d_equalityEngine.addFunctionKind(kind::APPLY_SELECTOR);
  d_equalityEngine.addFunctionKind(kind::APPLY_TESTER);
}

void TheoryModel::reset(){
  d_reps.clear();
  d_rep_set.clear();
  d_uf_terms.clear();
  d_uf_models.clear();
}

Node TheoryModel::getValue( TNode n ) const{
  //apply substitutions
  Node nn = d_substitutions.apply( n );
  //get value in model
  return getModelValue( nn );
}

Expr TheoryModel::getValue( Expr expr ) const{
  Node n = Node::fromExpr( expr );
  Node ret = getValue( n );
  return ret.toExpr();
}

/** get cardinality for sort */
Cardinality TheoryModel::getCardinality( Type t ) const{
  TypeNode tn = TypeNode::fromType( t );
  //for now, we only handle cardinalities for uninterpreted sorts
  if( tn.isSort() ){
    if( d_rep_set.hasType( tn ) ){
      return Cardinality( d_rep_set.getNumRepresentatives( tn ) );
    }else{
      return Cardinality( CardinalityUnknown() );
    }
  }else{
    return Cardinality( CardinalityUnknown() );
  }
}

Node TheoryModel::getModelValue( TNode n ) const{
  if( n.isConst() ) {
    return n;
  }

  TypeNode t = n.getType();
  if (t.isFunction() || t.isPredicate()) {
    if (d_enableFuncModels) {
      std::map< Node, Node >::const_iterator it = d_uf_models.find(n);
      if (it != d_uf_models.end()) {
        // Existing function
        return it->second;
      }
      // Unknown function symbol: return LAMBDA x. c, where c is the first constant in the enumeration of the range type
      vector<TypeNode> argTypes = t.getArgTypes();
      vector<Node> args;
      NodeManager* nm = NodeManager::currentNM();
      for (unsigned i = 0; i < argTypes.size(); ++i) {
        args.push_back(nm->mkBoundVar(argTypes[i]));
      }
      Node boundVarList = nm->mkNode(kind::BOUND_VAR_LIST, args);
      TypeEnumerator te(t.getRangeType());
      return nm->mkNode(kind::LAMBDA, boundVarList, *te);
    }
    // TODO: if func models not enabled, throw an error?
    Unreachable();
  }

  if (n.getNumChildren() > 0) {
    std::vector<Node> children;
    if (n.getKind() == APPLY_UF) {
      Node op = n.getOperator();
      std::map< Node, Node >::const_iterator it = d_uf_models.find(op);
      if (it == d_uf_models.end()) {
        // Unknown term - return first enumerated value for this type
        TypeEnumerator te(n.getType());
        return *te;
      }else{
        // Plug in uninterpreted function model
        children.push_back(it->second);
      }
    }
    else if (n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      children.push_back(n.getOperator());
    }
    //evaluate the children
    for (unsigned i = 0; i < n.getNumChildren(); ++i) {
      Node val = getValue(n[i]);
      children.push_back(val);
    }
    Node val = Rewriter::rewrite(NodeManager::currentNM()->mkNode(n.getKind(), children));
    Assert(val.isConst());
    return val;
  }

  if (!d_equalityEngine.hasTerm(n)) {
    // Unknown term - return first enumerated value for this type
    TypeEnumerator te(n.getType());
    return *te;
  }
  Node val = d_equalityEngine.getRepresentative(n);
  Assert(d_reps.find(val) != d_reps.end());
  std::map< Node, Node >::const_iterator it = d_reps.find( val );
  if( it!=d_reps.end() ){
    return it->second;
  }else{
    return Node::null();
  }
}

Node TheoryModel::getDomainValue( TypeNode tn, std::vector< Node >& exclude ){
  if( d_rep_set.d_type_reps.find( tn )!=d_rep_set.d_type_reps.end() ){
    //try to find a pre-existing arbitrary element
    for( size_t i=0; i<d_rep_set.d_type_reps[tn].size(); i++ ){
      if( std::find( exclude.begin(), exclude.end(), d_rep_set.d_type_reps[tn][i] )==exclude.end() ){
        return d_rep_set.d_type_reps[tn][i];
      }
    }
  }
  return Node::null();
}

//FIXME: need to ensure that theory enumerators exist for each sort
Node TheoryModel::getNewDomainValue( TypeNode tn ){
  if( tn.isSort() ){
    return Node::null();
  }else{
    TypeEnumerator te(tn);
    while( !te.isFinished() ){
      Node r = *te;
      if(Debug.isOn("getNewDomainValue")) {
        Debug("getNewDomainValue") << "getNewDomainValue( " << tn << ")" << endl;
        Debug("getNewDomainValue") << "+ TypeEnumerator gave: " << r << endl;
        Debug("getNewDomainValue") << "+ d_type_reps are:";
        for(vector<Node>::const_iterator i = d_rep_set.d_type_reps[tn].begin();
            i != d_rep_set.d_type_reps[tn].end();
            ++i) {
          Debug("getNewDomainValue") << " " << *i;
        }
        Debug("getNewDomainValue") << endl;
      }
      if( std::find(d_rep_set.d_type_reps[tn].begin(), d_rep_set.d_type_reps[tn].end(), r) ==d_rep_set.d_type_reps[tn].end() ) {
        Debug("getNewDomainValue") << "+ it's new, so returning " << r << endl;
        return r;
      }
      ++te;
    }
    return Node::null();
  }
}

/** add substitution */
void TheoryModel::addSubstitution( TNode x, TNode t, bool invalidateCache ){
  if( !d_substitutions.hasSubstitution( x ) ){
    d_substitutions.addSubstitution( x, t, invalidateCache );
  } else {
#ifdef CVC4_ASSERTIONS
    Node oldX = d_substitutions.getSubstitution(x);
    // check that either the old substitution is the same, or it now maps to the new substitution
    if(oldX != t && d_substitutions.apply(oldX) != d_substitutions.apply(t)) {
      stringstream ss;
      ss << "Two incompatible substitutions added to TheoryModel:\n"
         << "the term:    " << x << "\n"
         << "old mapping: " << d_substitutions.apply(oldX) << "\n"
         << "new mapping: " << d_substitutions.apply(t);
      InternalError(ss.str());
    }
#endif /* CVC4_ASSERTIONS */
  }
}

/** add term */
void TheoryModel::addTerm( Node n ){
  if( !d_equalityEngine.hasTerm( n ) ){
    d_equalityEngine.addTerm( n );
  }
  //must collect UF terms
  if (n.getKind()==APPLY_UF) {
    Node op = n.getOperator();
    if( std::find( d_uf_terms[ op ].begin(), d_uf_terms[ op ].end(), n )==d_uf_terms[ op ].end() ){
      d_uf_terms[ op ].push_back( n );
      Trace("model-add-term-uf") << "Add term " << n << std::endl;
    }
  }
}

/** assert equality */
void TheoryModel::assertEquality( Node a, Node b, bool polarity ){
  d_equalityEngine.assertEquality( a.eqNode(b), polarity, Node::null() );
}

/** assert predicate */
void TheoryModel::assertPredicate( Node a, bool polarity ){
  if( a.getKind()==EQUAL ){
    d_equalityEngine.assertEquality( a, polarity, Node::null() );
  }else{
    d_equalityEngine.assertPredicate( a, polarity, Node::null() );
  }
}

/** assert equality engine */
void TheoryModel::assertEqualityEngine( const eq::EqualityEngine* ee ){
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    bool predicate = false;
    bool predTrue = false;
    bool predFalse = false;
    if (eqc.getType().isBoolean()) {
      predicate = true;
      predTrue = ee->areEqual(eqc, d_true);
      predFalse = ee->areEqual(eqc, d_false);
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
    while(!eqc_i.isFinished()) {
      if (predicate) {
        if (predTrue) {
          assertPredicate(*eqc_i, true);
        }
        else if (predFalse) {
          assertPredicate(*eqc_i, false);
        }
        else {
          d_equalityEngine.mergePredicates(*eqc_i, eqc, Node::null());
        }
      } else {
        assertEquality(*eqc_i, eqc, true);
      }
      ++eqc_i;
    }
    ++eqcs_i;
  }
}

void TheoryModel::assertRepresentative( Node n ){
  Trace("model-builder-reps") << "Assert rep : " << n << std::endl;
  d_reps[ n ] = n;
}

bool TheoryModel::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

Node TheoryModel::getRepresentative( Node a ){
  if( d_equalityEngine.hasTerm( a ) ){
    Node r = d_equalityEngine.getRepresentative( a );
    if( d_reps.find( r )!=d_reps.end() ){
      return d_reps[ r ];
    }else{
      return r;
    }
  }else{
    return a;
  }
}

bool TheoryModel::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryModel::areDisequal( Node a, Node b ){
  if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
    return d_equalityEngine.areDisequal( a, b, false );
  }else{
    return false;
  }
}

//for debugging
void TheoryModel::printRepresentativeDebug( const char* c, Node r ){
  if( r.isNull() ){
    Debug( c ) << "null";
  }else if( r.getType().isBoolean() ){
    if( areEqual( r, d_true ) ){
      Debug( c ) << "true";
    }else{
      Debug( c ) << "false";
    }
  }else{
    Debug( c ) << getRepresentative( r );
  }
}

void TheoryModel::printRepresentative( std::ostream& out, Node r ){
  Assert( !r.isNull() );
  if( r.isNull() ){
    out << "null";
  }else if( r.getType().isBoolean() ){
    if( areEqual( r, d_true ) ){
      out  << "true";
    }else{
      out  << "false";
    }
  }else{
    out << getRepresentative( r );
  }
}

TheoryEngineModelBuilder::TheoryEngineModelBuilder( TheoryEngine* te ) : d_te( te ){

}

void TheoryEngineModelBuilder::buildModel(Model* m, bool fullModel)
{
  TheoryModel* tm = (TheoryModel*)m;

  // Reset model
  tm->reset();

  // Collect model info from the theories
  Trace("model-builder") << "TheoryEngineModelBuilder: Collect model info..." << std::endl;
  d_te->collectModelInfo(tm, fullModel);

  Trace("model-builder") << "Collect representatives..." << std::endl;
  // Process all terms in the equality engine, store representatives for each EC
  std::map< Node, Node > assertedReps, constantReps;
  TypeSet typeConstSet, typeRepSet, typeNoRepSet;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &tm->d_equalityEngine );
  for ( ; !eqcs_i.isFinished(); ++eqcs_i) {

    // eqc is the equivalence class representative
    Node eqc = (*eqcs_i);
    Trace("model-builder") << "Processing EC: " << eqc << endl;
    Assert(tm->d_equalityEngine.getRepresentative(eqc) == eqc);
    TypeNode eqct = eqc.getType();
    Assert(assertedReps.find(eqc) == assertedReps.end());
    Assert(constantReps.find(eqc) == constantReps.end());

    // Loop through terms in this EC
    Node rep, const_rep;
    eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, &tm->d_equalityEngine);
    for ( ; !eqc_i.isFinished(); ++eqc_i) {
      Node n = *eqc_i;
      Trace("model-builder") << "  Processing Term: " << n << endl;
      // Record as rep if this node was specified as a representative
      if (tm->d_reps.find(n) != tm->d_reps.end()){
        Assert(rep.isNull());
        rep = tm->d_reps[n];
        Assert(!rep.isNull() );
        Trace("model-builder") << "  Rep( " << eqc << " ) = " << rep << std::endl;
      }
      // Record as const_rep if this node is constant
      if (n.isConst()) {
        Assert(const_rep.isNull());
        const_rep = n;
        Trace("model-builder") << "  ConstRep( " << eqc << " ) = " << const_rep << std::endl;
      }
      //model-specific processing of the term
      tm->addTerm(n);
    }

    // Assign representative for this EC
    if (!const_rep.isNull()) {
      // Theories should not specify a rep if there is already a constant in the EC
      Assert(rep.isNull() || rep == const_rep);
      constantReps[eqc] = const_rep;
      typeConstSet.add(eqct, const_rep);
    }
    else if (!rep.isNull()) {
      assertedReps[eqc] = rep;
      typeRepSet.add(eqct, eqc);
    }
    else {
      typeNoRepSet.add(eqct, eqc);
    }
  }

  // Need to ensure that each EC has a constant representative.

  // Phase 1: For types that do not have asserted reps, assign the unassigned EC's using either evaluation or type enumeration
  Trace("model-builder") << "Starting phase 1..." << std::endl;
  TypeSet::iterator it;
  for (it = typeNoRepSet.begin(); it != typeNoRepSet.end(); ++it) {
    TypeNode t = TypeSet::getType(it);
    Trace("model-builder") << "  Working on type: " << t << endl;
    set<Node>& noRepSet = TypeSet::getSet(it);
    Assert(!noRepSet.empty());

    set<Node>::iterator i, i2;
    bool changed;

    // Find value for this EC using evaluation if possible
    do {
      changed = false;
      d_normalizedCache.clear();
      for (i = noRepSet.begin(); i != noRepSet.end(); ) {
        i2 = i;
        ++i;
        eq::EqClassIterator eqc_i = eq::EqClassIterator(*i2, &tm->d_equalityEngine);
        for ( ; !eqc_i.isFinished(); ++eqc_i) {
          Node n = *eqc_i;
          Node normalized = normalize(tm, n, constantReps, true);
          if (normalized.isConst()) {
            typeConstSet.add(t, normalized);
            constantReps[*i2] = normalized;
            Trace("model-builder") << "  Eval: Setting constant rep of " << (*i2) << " to " << normalized << endl;
            changed = true;
            noRepSet.erase(i2);
            break;
          }
        }
      }
    } while (changed);

    // Skip next step if nothing to do or if fullModel is false (meaning we shouldn't choose any representatives that aren't forced)
    if (noRepSet.empty() || !fullModel) {
      continue;
    }

    // This assertion may be too strong, but hopefully not: we expect that for every type, either all of its EC's have asserted reps (or constants)
    // or none of its EC's have asserted reps.
    Assert(typeRepSet.getSet(t) == NULL);

    Node n;
    for (i = noRepSet.begin(); i != noRepSet.end(); ++i) {
      n = typeConstSet.nextTypeEnum(t);
      Assert(!n.isNull(), "out of values for finite type enumeration while building model");
      constantReps[*i] = n;
      Trace("model-builder") << "  New Const: Setting constant rep of " << (*i) << " to " << n << endl;
    }
  }

  // Phase 2: Substitute into asserted reps using constReps.
  // Iterate until a fixed point is reached.
  Trace("model-builder") << "Starting phase 2..." << std::endl;
  bool changed;
  do {
    changed = false;
    d_normalizedCache.clear();
    for (it = typeRepSet.begin(); it != typeRepSet.end(); ++it) {
      set<Node>& repSet = TypeSet::getSet(it);
      set<Node>::iterator i;
      for (i = repSet.begin(); i != repSet.end(); ) {
        Assert(assertedReps.find(*i) != assertedReps.end());
        Node rep = assertedReps[*i];
        Node normalized = normalize(tm, rep, constantReps, false);
        Trace("model-builder") << "  Normalizing rep (" << rep << "), normalized to (" << normalized << ")" << endl;
        if (normalized.isConst()) {
          changed = true;
          constantReps[*i] = normalized;
          assertedReps.erase(*i);
          set<Node>::iterator i2 = i;
          ++i;
          repSet.erase(i2);
        }
        else {
          if (normalized != rep) {
            assertedReps[*i] = normalized;
            changed = true;
          }
          ++i;
        }
      }
    }
  } while (changed);

#ifdef CVC4_ASSERTIONS
  if (fullModel) {
    // Assert that all representatives have been converted to constants
    for (it = typeRepSet.begin(); it != typeRepSet.end(); ++it) {
      set<Node>& repSet = TypeSet::getSet(it);
      Assert(repSet.empty());
    }
  }
#endif /* CVC4_ASSERTIONS */

  Trace("model-builder") << "Copy representatives to model..." << std::endl;
  tm->d_reps.clear();
  std::map< Node, Node >::iterator itMap;
  for (itMap = constantReps.begin(); itMap != constantReps.end(); ++itMap) {
    tm->d_reps[itMap->first] = itMap->second;
    tm->d_rep_set.add(itMap->second);
  }

  if (!fullModel) {
    // Make sure every EC has a rep
    for (itMap = assertedReps.begin(); itMap != assertedReps.end(); ++itMap ) {
      tm->d_reps[itMap->first] = itMap->second;
      tm->d_rep_set.add(itMap->second);
    }
    for (it = typeNoRepSet.begin(); it != typeNoRepSet.end(); ++it) {
      set<Node>& noRepSet = TypeSet::getSet(it);
      set<Node>::iterator i;
      for (i = noRepSet.begin(); i != noRepSet.end(); ++i) {
        tm->d_reps[*i] = *i;
        tm->d_rep_set.add(*i);
      }
    }
  }

  //modelBuilder-specific initialization
  processBuildModel( tm, fullModel );

  if (fullModel) {
    // Check that every term evaluates to its representative in the model
    for (eqcs_i = eq::EqClassesIterator(&tm->d_equalityEngine); !eqcs_i.isFinished(); ++eqcs_i) {
      // eqc is the equivalence class representative
      Node eqc = (*eqcs_i);
      Assert(constantReps.find(eqc) != constantReps.end());
      Node rep = constantReps[eqc];
      eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, &tm->d_equalityEngine);
      for ( ; !eqc_i.isFinished(); ++eqc_i) {
        Node n = *eqc_i;
        Assert(tm->getValue(*eqc_i) == rep);
      }
    }
  }
}


Node TheoryEngineModelBuilder::normalize(TheoryModel* m, TNode r, std::map< Node, Node >& constantReps, bool evalOnly)
{
  std::map<Node, Node>::iterator itMap = constantReps.find(r);
  if (itMap != constantReps.end()) {
    return (*itMap).second;
  }
  NodeMap::iterator it = d_normalizedCache.find(r);
  if (it != d_normalizedCache.end()) {
    return (*it).second;
  }
  Node retNode = r;
  if (r.getNumChildren() > 0) {
    std::vector<Node> children;
    if (r.getMetaKind() == kind::metakind::PARAMETERIZED) {
      children.push_back(r.getOperator());
    }
    bool childrenConst = true;
    for (size_t i=0; i < r.getNumChildren(); ++i) {
      Node ri = r[i];
      if (!ri.isConst()) {
        if (m->d_equalityEngine.hasTerm(ri)) {
          ri = m->d_equalityEngine.getRepresentative(ri);
          itMap = constantReps.find(ri);
          if (itMap != constantReps.end()) {
            ri = (*itMap).second;
          }
          else if (evalOnly) {
            ri = normalize(m, r[i], constantReps, evalOnly);
          }
        }
        else {
          ri = normalize(m, ri, constantReps, evalOnly);
        }
        if (!ri.isConst()) {
          childrenConst = false;
        }
      }
      children.push_back(ri);
    }
    retNode = NodeManager::currentNM()->mkNode( r.getKind(), children );
    if (childrenConst) {
      retNode = Rewriter::rewrite(retNode);
      Assert(retNode.getKind() == kind::APPLY_UF || retNode.isConst());
    }
  }
  d_normalizedCache[r] = retNode;
  return retNode;
}


void TheoryEngineModelBuilder::processBuildModel(TheoryModel* m, bool fullModel)
{
  if (fullModel) {
    Trace("model-builder") << "Assigning function values..." << endl;
    //construct function values
    for( std::map< Node, std::vector< Node > >::iterator it = m->d_uf_terms.begin(); it != m->d_uf_terms.end(); ++it ){
      Node n = it->first;
      if( m->d_uf_models.find( n )==m->d_uf_models.end() ){
        TypeNode type = n.getType();
        uf::UfModelTree ufmt( n );
        Node default_v, un, simp, v;
        for( size_t i=0; i<it->second.size(); i++ ){
          un = it->second[i];
          vector<TNode> children;
          children.push_back(n);
          for (size_t j = 0; j < un.getNumChildren(); ++j) {
            children.push_back(m->getRepresentative(un[j]));
          }
          simp = NodeManager::currentNM()->mkNode(un.getKind(), children);
          v = m->getRepresentative(un);
          Trace("model-builder") << "  Setting (" << simp << ") to (" << v << ")" << endl;
          ufmt.setValue(m, simp, v);
          default_v = v;
        }
        if( default_v.isNull() ){
          //choose default value from model if none exists
          TypeEnumerator te(type.getRangeType());
          default_v = (*te);
        }
        ufmt.setDefaultValue( m, default_v );
        ufmt.simplify();
        Node val = ufmt.getFunctionValue( "$x" );
        Trace("model-builder") << "  Assigning (" << n << ") to (" << val << ")" << endl;
        m->d_uf_models[n] = val;
        //ufmt.debugPrint( std::cout, m );
      }
    }
  }
}
