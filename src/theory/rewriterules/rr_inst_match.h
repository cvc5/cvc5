/*********************                                                        */
/*! \file rr_inst_match.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Francois Bobot
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__RR_INST_MATCH_H
#define __CVC4__THEORY__REWRITERULES__RR_INST_MATCH_H

#include "theory/theory.h"
#include "util/hash.h"
#include "util/ntuple.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "context/cdlist.h"

#include "theory/quantifiers/term_database.h"
#include "expr/node_manager.h"
#include "expr/node_builder.h"

#include "theory/quantifiers/options.h"
#include "theory/rewriterules/options.h"

//#define USE_EFFICIENT_E_MATCHING

namespace CVC4 {
namespace theory {

class EqualityQuery;

namespace rrinst{

/** basic class defining an instantiation */
class InstMatch {
  /* map from variable to ground terms */
  std::map< Node, Node > d_map;
public:
  InstMatch();
  InstMatch( InstMatch* m );

  /** set the match of v to m */
  bool setMatch( EqualityQuery* q, TNode v, TNode m );
  /* This version tell if the variable has been set */
  bool setMatch( EqualityQuery* q, TNode v, TNode m, bool & set);
  /** fill all unfilled values with m */
  bool add( InstMatch& m );
  /** if compatible, fill all unfilled values with m and return true
      return false otherwise */
  bool merge( EqualityQuery* q, InstMatch& m );
  /** debug print method */
  void debugPrint( const char* c );
  /** is complete? */
  bool isComplete( Node f ) { return d_map.size()==f[0].getNumChildren(); }
  /** make complete */
  void makeComplete( Node f, QuantifiersEngine* qe );
  /** make internal representative */
  //void makeInternalRepresentative( QuantifiersEngine* qe );
  /** make representative */
  void makeRepresentative( QuantifiersEngine* qe );
  /** get value */
  Node getValue( Node var ) const;
  /** clear */
  void clear(){ d_map.clear(); }
  /** is_empty */
  bool empty(){ return d_map.empty(); }
  /** to stream */
  inline void toStream(std::ostream& out) const {
    out << "INST_MATCH( ";
    for( std::map< Node, Node >::const_iterator it = d_map.begin(); it != d_map.end(); ++it ){
      if( it != d_map.begin() ){ out << ", "; }
      out << it->first << " -> " << it->second;
    }
    out << " )";
  }


  //for rewrite rules

  /** apply rewrite */
  void applyRewrite();
  /** erase */
  template<class Iterator>
  void erase(Iterator begin, Iterator end){
    for(Iterator i = begin; i != end; ++i){
      d_map.erase(*i);
    };
  }
  void erase(Node node){ d_map.erase(node); }
  /** get */
  Node get( TNode var ) { return d_map[var]; }
  Node get( QuantifiersEngine* qe, Node f, int i );
  /** set */
  void set(TNode var, TNode n);
  void set( QuantifiersEngine* qe, Node f, int i, TNode n );
  /** size */
  size_t size(){ return d_map.size(); }
  /* iterator */
  std::map< Node, Node >::iterator begin(){ return d_map.begin(); };
  std::map< Node, Node >::iterator end(){ return d_map.end(); };
  std::map< Node, Node >::iterator find(Node var){ return d_map.find(var); };
  /* Node used for matching the trigger only for mono-trigger (just for
     efficiency because I need only that) */
  Node d_matched;
};/* class InstMatch */



class CandidateGenerator
{
public:
  CandidateGenerator(){}
  virtual ~CandidateGenerator(){};

  /** Get candidates functions.  These set up a context to get all match candidates.
      cg->reset( eqc );
      do{
        Node cand = cg->getNextCandidate();
        //.......
      }while( !cand.isNull() );

      eqc is the equivalence class you are searching in
  */
  virtual void reset( TNode eqc ) = 0;
  virtual TNode getNextCandidate() = 0;
  /** call this at the beginning of each instantiation round */
  virtual void resetInstantiationRound() = 0;
public:
  /** legal candidate */
  static inline bool isLegalCandidate( TNode n ){
    return !n.getAttribute(NoMatchAttribute()) &&
      ( !options::cbqi() || !quantifiers::TermDb::hasInstConstAttr(n)) &&
      ( !options::efficientEMatching() || n.hasAttribute(AvailableInTermDb()) );
}

};


inline std::ostream& operator<<(std::ostream& out, const InstMatch& m) {
  m.toStream(out);
  return out;
}

template<bool modEq = false> class InstMatchTrie2;
template<bool modEq = false> class InstMatchTrie2Pairs;

template<bool modEq = false>
class InstMatchTrie2Gen
{
  friend class InstMatchTrie2<modEq>;
  friend class InstMatchTrie2Pairs<modEq>;

private:

  class Tree {
  public:
    typedef std::hash_map< Node, Tree *, NodeHashFunction > MLevel;
    MLevel e;
    const size_t level; //context level of creation
    Tree() CVC4_UNDEFINED;
    const Tree & operator =(const Tree & t){
      Assert(t.e.empty()); Assert(e.empty());
      Assert(t.level == level);
      return t;
    }
    Tree(size_t l): level(l) {};
    ~Tree(){
      for(typename MLevel::iterator i = e.begin(); i!=e.end(); ++i)
        delete(i->second);
    };
  };


  typedef std::pair<Tree *, TNode> Mod;

  class CleanUp{
  public:
    inline void operator()(Mod * m){
      typename Tree::MLevel::iterator i = m->first->e.find(m->second);
      Assert (i != m->first->e.end()); //should not have been already removed
      m->first->e.erase(i);
    };
  };

  EqualityQuery* d_eQ;
  CandidateGenerator * d_cG;

  context::Context* d_context;
  context::CDList<Mod, CleanUp, std::allocator<Mod> > d_mods;


  typedef std::map<Node, Node>::const_iterator mapIter;

  /** add the substitution given by the iterator*/
  void addSubTree( Tree * root, mapIter current, mapIter end, size_t currLevel);
  /** test if it exists match, modulo uf-equations if modEq is true if
   *  return false the deepest point of divergence is put in [e] and
   *  [diverge].
   */
  bool existsInstMatch( Tree * root,
                        mapIter & current, mapIter & end,
                        Tree * & e, mapIter & diverge) const;

  /** add match m in the trie root
      return true if it was never seen */
  bool addInstMatch( InstMatch& m, Tree * root);

public:
  InstMatchTrie2Gen(context::Context* c,  QuantifiersEngine* q);
  InstMatchTrie2Gen(const InstMatchTrie2Gen &) CVC4_UNDEFINED;
  const InstMatchTrie2Gen & operator =(const InstMatchTrie2Gen & e) CVC4_UNDEFINED;
};

template<bool modEq>
class InstMatchTrie2
{
  typename InstMatchTrie2Gen<modEq>::Tree d_data;
  InstMatchTrie2Gen<modEq> d_backtrack;
public:
  InstMatchTrie2(context::Context* c,  QuantifiersEngine* q): d_data(0),
                                                              d_backtrack(c,q) {};
  InstMatchTrie2(const InstMatchTrie2 &) CVC4_UNDEFINED;
  const InstMatchTrie2 & operator =(const InstMatchTrie2 & e) CVC4_UNDEFINED;
  /** add match m in the trie,
      return true if it was never seen */
  inline bool addInstMatch( InstMatch& m){
    return d_backtrack.addInstMatch(m,&d_data);
  };

};/* class InstMatchTrie2 */

class Matcher
{
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset the term to match, return false if there is no such term */
  virtual bool reset( TNode n, InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** get the next match. If it return false once you shouldn't call
      getNextMatch again before doing a reset */
  virtual bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** If reset, or getNextMatch return false they remove from the
      InstMatch the binding that they have previously created */

  /** virtual Matcher in order to have defined behavior */
  virtual ~Matcher(){};
};


class ApplyMatcher: public Matcher{
private:
  /** What to check first: constant and variable */
  std::vector< triple< TNode,size_t,EqualityQuery* > > d_constants;
  std::vector< triple< TNode,size_t,EqualityQuery* > > d_variables;
  /** children generators, only the sub-pattern which are
      neither a variable neither a constant appears */
  std::vector< triple< Matcher*, size_t, EqualityQuery* > > d_childrens;
  /** the variable that have been set by this matcher (during its own reset) */
  std::vector< TNode > d_binded; /* TNode because the variable are already in d_pattern */
  /** the representative of the argument of the term given by the last reset */
  std::vector< Node > d_reps;
public:
  /** The pattern we are producing matches for */
  Node d_pattern;
public:
  /** constructors */
  ApplyMatcher( Node pat, QuantifiersEngine* qe);
  /** destructor */
  ~ApplyMatcher(){/*TODO delete dandling pointers? */}
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset the term to match */
  bool reset( TNode n, InstMatch& m, QuantifiersEngine* qe );
  /** get the next match. */
  bool getNextMatch(InstMatch& m, QuantifiersEngine* qe);
private:
  bool getNextMatch(InstMatch& m, QuantifiersEngine* qe, bool reset);
};


/* Match literal so you don't choose the equivalence class( */
class PatMatcher
{
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset the matcher, return false if there is no such term */
  virtual bool reset( InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** get the next match. If it return false once you shouldn't call
      getNextMatch again before doing a reset */
  virtual bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ) = 0;
  /** If reset, or getNextMatch return false they remove from the
      InstMatch the binding that they have previously created */
};

Matcher* mkMatcher( Node pat, QuantifiersEngine* qe );
PatMatcher* mkPattern( Node pat, QuantifiersEngine* qe );

/* Match literal so you don't choose the equivalence class( */
class PatsMatcher
{
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** reset the matcher, return false if there is no such term */
  virtual bool getNextMatch( QuantifiersEngine* qe ) = 0;
  virtual const InstMatch& getInstMatch() = 0;
  /** Add directly the instantiation to quantifiers engine */
  virtual int addInstantiations( InstMatch& baseMatch, Node quant, QuantifiersEngine* qe) = 0;
};

PatsMatcher* mkPatterns( std::vector< Node > pat, QuantifiersEngine* qe );
PatsMatcher* mkPatternsEfficient( std::vector< Node > pat, QuantifiersEngine* qe );

/** return true if whatever Node is substituted for the variables the
    given Node can't match the pattern */
bool nonunifiable( TNode t, TNode pat, const std::vector<Node> & vars);

class InstMatchGenerator;

}/* CVC4::theory rrinst */

}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__REWRITERULES__RR_INST_MATCH_H */
