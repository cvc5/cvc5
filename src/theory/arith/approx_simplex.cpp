/*********************                                                        */
/*! \file approx_simplex.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "theory/arith/approx_simplex.h"

#include <math.h>
#include <cfloat>
#include <cmath>
#include <unordered_set>

#include "base/output.h"
#include "cvc4autoconfig.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/constraint.h"
#include "theory/arith/cut_log.h"
#include "theory/arith/matrix.h"
#include "theory/arith/normal_form.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

struct AuxInfo {
  TreeLog* tl;
  int pivotLimit;
  int branchLimit;
  int branchDepth;
  MipResult term; /* terminatation */
};

enum SlackReplace { SlackUndef=0, SlackLB, SlackUB, SlackVLB, SlackVUB };

std::ostream& operator<<(std::ostream& out, MipResult res){
  switch(res){
  case MipUnknown:
    out << "MipUnknown"; break;
  case MipBingo:
    out << "MipBingo"; break;
  case MipClosed:
    out << "MipClosed"; break;
  case BranchesExhausted:
    out << "BranchesExhausted"; break;
  case PivotsExhauasted:
    out << "PivotsExhauasted"; break;
  case ExecExhausted:
    out << "ExecExhausted"; break;
  default:
    out << "Unexpected Mip Value!"; break;
  }
  return out;
}
struct VirtualBound {
  // Either x <= d * y or x >= d * y
  ArithVar x; // variable being bounded
  Kind k; // either LEQ or GEQ
  Rational d; // the multiple on y
  ArithVar y; // the variable that is the upper bound
  ConstraintP c; // the original constraint relating x and y

  VirtualBound()
    : x(ARITHVAR_SENTINEL)
    , k(kind::UNDEFINED_KIND)
    , d()
    , y(ARITHVAR_SENTINEL)
    , c(NullConstraint)
  {}
  VirtualBound(ArithVar toBound, Kind rel, const Rational& coeff, ArithVar bounding, ConstraintP orig)
    : x(toBound)
    , k(rel)
    , d(coeff)
    , y(bounding)
    , c(orig)
  {
    Assert(k == kind::LEQ || k == kind::GEQ);
  }
};

struct CutScratchPad {
  bool d_failure; // if the construction was unsuccessful

  /* GOMORY CUTS Datastructures */
  ArithVar d_basic; // a variable that is basic in the approximate solver
  DenseVector d_tabRow;           // a row in the tableau not including d_basic, equal to 0
  DenseMap<ConstraintP> d_toBound; // each variable in toBound maps each variable in tabRow to either an upper/lower bound

  /* MIR CUTS Datastructures */
  DenseMap<SlackReplace> d_slacks;// The x'[i] selected for x[i]
  DenseMap<VirtualBound> d_vub;   // Virtual upper bounds.
  DenseMap<VirtualBound> d_vlb;   // Virtual lower bounds.
  DenseMap<Rational> d_compRanges;

  // a sum of rows in the tableau, with possible replacements for fixed
  // sum aggLhs[i] x[i] = aggRhs;
  DenseVector d_agg;
  // Takes agg and replaces x[i] with a slack variable x'[i]
  // Takes agg and replaces x[i] with a slack variable x'[i]
  // sum modLhs[i] x'[i] = modRhs;
  DenseVector d_mod;

  // Takes mod, and performs c-Mir on it
  // sum alpha[i] x'[i] <= beta
  DenseVector d_alpha;

  /* The constructed cut */
  // sum cut[i] x[i] <= cutRhs
  DenseVector d_cut;
  Kind d_cutKind;

  /* The constraints used throughout construction. */
  std::set<ConstraintP> d_explanation; // use pointer equality
  CutScratchPad(){
    clear();
  }
  void clear(){
    d_failure = false;
    d_basic = ARITHVAR_SENTINEL;
    d_tabRow.purge();
    d_toBound.purge();

    d_slacks.purge();
    d_vub.purge();
    d_vlb.purge();
    d_compRanges.purge();

    d_agg.purge();
    d_mod.purge();
    d_alpha.purge();

    d_cut.purge();
    d_cutKind = kind::UNDEFINED_KIND;
    d_explanation.clear();
  }
};

ApproximateStatistics::ApproximateStatistics()
  :  d_branchMaxDepth("z::approx::branchMaxDepth",0)
  ,  d_branchesMaxOnAVar("z::approx::branchesMaxOnAVar",0)
  ,  d_gaussianElimConstructTime("z::approx::gaussianElimConstruct::time")
  ,  d_gaussianElimConstruct("z::approx::gaussianElimConstruct::calls",0)
  ,  d_averageGuesses("z::approx::averageGuesses")
{
  smtStatisticsRegistry()->registerStat(&d_branchMaxDepth);
  smtStatisticsRegistry()->registerStat(&d_branchesMaxOnAVar);

  smtStatisticsRegistry()->registerStat(&d_gaussianElimConstructTime);
  smtStatisticsRegistry()->registerStat(&d_gaussianElimConstruct);

  smtStatisticsRegistry()->registerStat(&d_averageGuesses);
}

ApproximateStatistics::~ApproximateStatistics(){
  smtStatisticsRegistry()->unregisterStat(&d_branchMaxDepth);
  smtStatisticsRegistry()->unregisterStat(&d_branchesMaxOnAVar);

  smtStatisticsRegistry()->unregisterStat(&d_gaussianElimConstructTime);
  smtStatisticsRegistry()->unregisterStat(&d_gaussianElimConstruct);

  smtStatisticsRegistry()->unregisterStat(&d_averageGuesses);
}

Integer ApproximateSimplex::s_defaultMaxDenom(1<<26);

ApproximateSimplex::ApproximateSimplex(const ArithVariables& v, TreeLog& l,
                                       ApproximateStatistics& s)
  : d_vars(v)
  , d_log(l)
  , d_stats(s)
  , d_pivotLimit(std::numeric_limits<int>::max())
  , d_branchLimit(std::numeric_limits<int>::max())
  , d_maxDepth(std::numeric_limits<int>::max())
{}

void ApproximateSimplex::setPivotLimit(int pl){
  Assert(pl >= 0);
  d_pivotLimit = pl;
}

void ApproximateSimplex::setBranchingDepth(int bd){
  Assert(bd >= 0);
  d_maxDepth = bd;
}

void ApproximateSimplex::setBranchOnVariableLimit(int bl){
  Assert(bl >= 0);
  d_branchLimit = bl;
}

const double ApproximateSimplex::SMALL_FIXED_DELTA = .000000001;
const double ApproximateSimplex::TOLERENCE = 1 + .000000001;

bool ApproximateSimplex::roughlyEqual(double a, double b){
  if (a == 0){
    return -SMALL_FIXED_DELTA <= b && b <= SMALL_FIXED_DELTA;
  }else if (b == 0){
    return -SMALL_FIXED_DELTA <= a && a <= SMALL_FIXED_DELTA;
  }else{
    return std::abs(b/a) <= TOLERENCE && std::abs(a/b) <= TOLERENCE;
  }
}

Rational ApproximateSimplex::cfeToRational(const vector<Integer>& exp){
  if(exp.empty()){
    return Rational(0);
  }else{
    Rational result = exp.back();
    vector<Integer>::const_reverse_iterator exp_iter = exp.rbegin();
    vector<Integer>::const_reverse_iterator exp_end = exp.rend();
    ++exp_iter;
    while(exp_iter != exp_end){
      result = result.inverse();
      const Integer& i = *exp_iter;
      result += i;
      ++exp_iter;
    }
    return result;
  }
}
std::vector<Integer> ApproximateSimplex::rationalToCfe(const Rational& q, int depth){
  vector<Integer> mods;
  if(!q.isZero()){
    Rational carry = q;
    for(int i = 0; i <= depth; ++i){
      Assert(!carry.isZero());
      mods.push_back(Integer());
      Integer& back = mods.back();
      back = carry.floor();
      Debug("rationalToCfe") << "  cfe["<<i<<"]: " << back << endl;
      carry -= back;
      if(carry.isZero()){
        break;
      }else if(ApproximateSimplex::roughlyEqual(carry.getDouble(), 0.0)){
        break;
      }else{
        carry = carry.inverse();
      }
    }
  }
  return mods;
}


Rational ApproximateSimplex::estimateWithCFE(const Rational& r, const Integer& K){
  Debug("estimateWithCFE") << "estimateWithCFE(" << r << ", " << K << ")" <<endl;
  // references
  // page 4: http://carlossicoli.free.fr/C/Cassels_J.W.S.-An_introduction_to_diophantine_approximation-University_Press(1965).pdf
  // http://en.wikipedia.org/wiki/Continued_fraction
  Assert(K >= Integer(1));
  if( r.getDenominator() <= K ){
    return r;
  }

  // current numerator and denominator that has not been resolved in the cfe
  Integer num = r.getNumerator(), den = r.getDenominator();
  Integer quot,rem;

  unsigned t = 0;
  // For a sequence of candidate solutions q_t/p_t
  // we keep only 3 time steps: 0[prev], 1[current], 2[next]
  // timesteps with a fake timestep 0 (p is 0 and q is 1)
  // at timestep 1
  Integer p[3]; // h
  Integer q[3]; // k
  // load the first 3 time steps manually
  p[0] =    0; q[0] = 1; // timestep -2
  p[1] =    1; q[1] = 0; // timestep -1

  Integer::floorQR(quot, rem, num, den);
  num = den; den = rem;

  q[2] = q[0] + quot*q[1];
  p[2] = p[0] + quot*p[1];
  Debug("estimateWithCFE") <<  "  cfe["<<t<<"]: " << p[2] <<"/"<< q[2] << endl;
  while( q[2] <= K ){
    p[0] = p[1]; p[1] = p[2];
    q[0] = q[1]; q[1] = q[2];


    Integer::floorQR(quot, rem, num, den);
    num = den; den = rem;

    p[2] = p[0]+quot*p[1];
    q[2] = q[0]+quot*q[1];
    ++t;
    Debug("estimateWithCFE") << "  cfe["<<t<<"]: " << p[2] <<"/"<< q[2] << endl;
  }

  Integer k = (K-q[0]).floorDivideQuotient(q[1]);
  Rational cand_prev(p[0]+k*p[1], q[0]+k*q[1]);
  Rational cand_curr(p[1], q[1]);
  Rational dist_prev = (cand_prev - r).abs();
  Rational dist_curr = (cand_curr - r).abs();
  if(dist_prev <= dist_curr){
    Debug("estimateWithCFE") << cand_prev << " is closer than " << cand_curr << endl;
    return cand_prev;
  }else{
    Debug("estimateWithCFE") << cand_curr << " is closer than " << cand_prev << endl;
    return cand_curr;
  }
}

Maybe<Rational> ApproximateSimplex::estimateWithCFE(double d, const Integer& D)
{
  if (Maybe<Rational> from_double = Rational::fromDouble(d))
  {
    return estimateWithCFE(from_double.value(), D);
  }
  return Maybe<Rational>();
}

Maybe<Rational> ApproximateSimplex::estimateWithCFE(double d)
{
  return estimateWithCFE(d, s_defaultMaxDenom);
}

class ApproxNoOp : public ApproximateSimplex {
public:
  ApproxNoOp(const ArithVariables& v, TreeLog& l, ApproximateStatistics& s)
  : ApproximateSimplex(v,l,s)
  {}
  ~ApproxNoOp(){}

  LinResult solveRelaxation() override { return LinUnknown; }
  Solution extractRelaxation() const override { return Solution(); }

  ArithRatPairVec heuristicOptCoeffs() const override
  {
    return ArithRatPairVec();
  }

  MipResult solveMIP(bool al) override { return MipUnknown; }
  Solution extractMIP() const override { return Solution(); }

  void setOptCoeffs(const ArithRatPairVec& ref) override {}

  void tryCut(int nid, CutInfo& cut) override {}

  std::vector<const CutInfo*> getValidCuts(const NodeLog& node) override
  {
    return std::vector<const CutInfo*>();
  }

  ArithVar getBranchVar(const NodeLog& nl) const override
  {
    return ARITHVAR_SENTINEL;
  }

  double sumInfeasibilities(bool mip) const override { return 0.0; }
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

/* Begin the declaration of GLPK specific code. */
#ifdef CVC4_USE_GLPK
extern "C" {
#include <glpk.h>
}/* extern "C" */

namespace CVC4 {
namespace theory {
namespace arith {

Kind glpk_type_to_kind(int glpk_cut_type){
  switch(glpk_cut_type){
  case GLP_LO: return kind::GEQ;
  case GLP_UP: return kind::LEQ;
  case GLP_FX: return kind::EQUAL;
  case GLP_DB:
  case GLP_FR:
  default:     return kind::UNDEFINED_KIND;
  }
}

class GmiInfo;
class MirInfo;
class BranchCutInfo;

class ApproxGLPK : public ApproximateSimplex {
private:
  glp_prob* d_inputProb; /* a copy of the input prob */
  glp_prob* d_realProb;  /* a copy of the real relaxation output */
  glp_prob* d_mipProb;   /* a copy of the integer prob */

  DenseMap<int> d_colIndices;
  DenseMap<int> d_rowIndices;

  NodeLog::RowIdMap d_rootRowIds;
  //DenseMap<ArithVar> d_rowToArithVar;
  DenseMap<ArithVar> d_colToArithVar;

  int d_instanceID;

  bool d_solvedRelaxation;
  bool d_solvedMIP;

  static int s_verbosity;

  CutScratchPad d_pad;

  std::vector<Integer> d_denomGuesses;

public:
  ApproxGLPK(const ArithVariables& v, TreeLog& l, ApproximateStatistics& s);
  ~ApproxGLPK();

  LinResult solveRelaxation();
  Solution extractRelaxation() const override { return extractSolution(false); }

  ArithRatPairVec heuristicOptCoeffs() const override;

  MipResult solveMIP(bool al) override;
  Solution extractMIP() const override { return extractSolution(true); }
  void setOptCoeffs(const ArithRatPairVec& ref) override;
  std::vector<const CutInfo*> getValidCuts(const NodeLog& nodes) override;
  ArithVar getBranchVar(const NodeLog& con) const;

  static void printGLPKStatus(int status, std::ostream& out);


private:
 Solution extractSolution(bool mip) const;
 int guessDir(ArithVar v) const;

 // get this stuff out of here
 void tryCut(int nid, CutInfo& cut) override;

 ArithVar _getArithVar(int nid, int M, int ind) const;
 ArithVar getArithVarFromRow(int nid, int ind) const
 {
   if (ind >= 0)
   {
     const NodeLog& nl = d_log.getNode(nid);
     return nl.lookupRowId(ind);
   }
   return ARITHVAR_SENTINEL;
  }

  // virtual void mapRowId(int nid, int ind, ArithVar v){
  //   NodeLog& nl = d_log.getNode(nid);
  //   nl.mapRowId(ind, v);
  // }
  // virtual void applyRowsDeleted(int nid, const RowsDeleted& rd){
  //   NodeLog& nl = d_log.getNode(nid);
  //   nl.applyRowsDeleted(rd);
  // }

  ArithVar getArithVarFromStructural(int ind) const{
    if(ind >= 0){
      unsigned u = (unsigned) ind;
      if(d_colToArithVar.isKey(u)){
        return d_colToArithVar[u];
      }
    }
    return ARITHVAR_SENTINEL;
  }

  /**
   * Attempts to make the row vector vec on the pad.
   * If this is not in the row span of the original tableau this
   * raises the failure flag.
   */
  bool attemptConstructTableRow(int node, int M, const PrimitiveVec& vec);
  bool guessCoefficientsConstructTableRow(int node, int M, const PrimitiveVec& vec);
  bool guessCoefficientsConstructTableRow(int node, int M, const PrimitiveVec& vec, const Integer& D);
  bool gaussianElimConstructTableRow(int node, int M, const PrimitiveVec& vec);

  /* This is a guess of a vector in the row span of the tableau.
   * Attempt to cancel out all of the variables.
   * returns true if this is constructable.
   */
  bool guessIsConstructable(const DenseMap<Rational>& guess) const;

  /**
   * Loads a vector of statuses into a dense map over bounds.
   * returns true on failure.
   */
  bool loadToBound(int node, int M, int len, int* inds, int* statuses,
                   DenseMap<ConstraintP>& toBound) const;

  /** checks the cut on the pad for whether it is sufficiently similar to cut. */
  bool checkCutOnPad(int nid, const CutInfo& cut) const;


  /** turns the pad into a node and creates an explanation. */
  //std::pair<Node, Node> makeCutNodes(int nid, const CutInfo& cut) const;

  // true means failure!
  // BRANCH CUTS
  bool attemptBranchCut(int nid, const BranchCutInfo& br);

  // GOMORY CUTS
  bool attemptGmi(int nid, const GmiInfo& gmi);
  /** tries to turn the information on the pad into a cut. */
  bool constructGmiCut();

  // MIR CUTS
  bool attemptMir(int nid, const MirInfo& mir);
  bool applyCMIRRule(int nid, const MirInfo& mir);
  bool makeRangeForComplemented(int nid, const MirInfo& mir);
  bool loadSlacksIntoPad(int nid, const MirInfo& mir);
  bool loadVirtualBoundsIntoPad(int nid, const MirInfo& mir);
  bool loadRowSumIntoAgg(int nid, int M, const PrimitiveVec& mir);
  bool buildModifiedRow(int nid, const MirInfo& mir);
  bool constructMixedKnapsack();
  bool replaceSlacksOnCuts();
  bool loadVB(int nid, int M, int j, int ri, bool wantUb, VirtualBound& tmp);


  double sumInfeasibilities(bool mip) const{
    return sumInfeasibilities(mip? d_mipProb : d_realProb);
  }
  double sumInfeasibilities(glp_prob* prob, bool mip) const;
};

int ApproxGLPK::s_verbosity = 0;

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
#endif /*#ifdef CVC4_USE_GLPK */
/* End the declaration of GLPK specific code. */

/* Begin GPLK/NOGLPK Glue code. */
namespace CVC4 {
namespace theory {
namespace arith {
ApproximateSimplex* ApproximateSimplex::mkApproximateSimplexSolver(const ArithVariables& vars, TreeLog& l, ApproximateStatistics& s){
#ifdef CVC4_USE_GLPK
  return new ApproxGLPK(vars, l, s);
#else
  return new ApproxNoOp(vars, l, s);
#endif
}
bool ApproximateSimplex::enabled() {
#ifdef CVC4_USE_GLPK
  return true;
#else
  return false;
#endif
}
}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
/* End GPLK/NOGLPK Glue code. */


/* Begin GPLK implementation. */
#ifdef CVC4_USE_GLPK
namespace CVC4 {
namespace theory {
namespace arith {

static CutInfoKlass fromGlpkClass(int klass){
  switch(klass){
  case GLP_RF_GMI: return GmiCutKlass;
  case GLP_RF_MIR: return MirCutKlass;
  case GLP_RF_COV:
  case GLP_RF_CLQ:
  default:         return UnknownKlass;
  }
}

ApproxGLPK::ApproxGLPK(const ArithVariables& v, TreeLog& l, ApproximateStatistics& s)
  : ApproximateSimplex(v, l, s)
  , d_inputProb(NULL)
  , d_realProb(NULL)
  , d_mipProb(NULL)
  , d_solvedRelaxation(false)
  , d_solvedMIP(false)
{
  static int instance = 0;
  ++instance;
  d_instanceID = instance;

  d_denomGuesses.push_back(Integer(1<<22));
  d_denomGuesses.push_back(ApproximateSimplex::s_defaultMaxDenom);
  d_denomGuesses.push_back(Integer(1ul<<29));
  d_denomGuesses.push_back(Integer(1ul<<31));

  d_inputProb = glp_create_prob();
  d_realProb = glp_create_prob();
  d_mipProb = glp_create_prob();
  glp_set_obj_dir(d_inputProb, GLP_MAX);
  glp_set_prob_name(d_inputProb, "ApproximateSimplex::approximateFindModel");

  int numRows = 0;
  int numCols = 0;

  // Assign each variable to a row and column variable as it appears in the input
  for(ArithVariables::var_iterator vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end; ++vi){
    ArithVar v = *vi;

    if(d_vars.isAuxiliary(v)){
      ++numRows;
      d_rowIndices.set(v, numRows);
      //mapRowId(d_log.getRootId(), numRows, v);
      d_rootRowIds.insert(make_pair(numRows, v));
      //d_rowToArithVar.set(numRows, v);
      Debug("approx") << "Row vars: " << v << "<->" << numRows << endl;
    }else{
      ++numCols;
      d_colIndices.set(v, numCols);
      d_colToArithVar.set(numCols, v);
      Debug("approx") << "Col vars: " << v << "<->" << numCols << endl;
    }
  }
  Assert(numRows > 0);
  Assert(numCols > 0);

  glp_add_rows(d_inputProb, numRows);
  glp_add_cols(d_inputProb, numCols);

  // Assign the upper/lower bounds and types to each variable
  for(ArithVariables::var_iterator vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end; ++vi){
    ArithVar v = *vi;

    if(s_verbosity >= 2){
      //Message() << v  << " ";
      //d_vars.printModel(v, Message());
    }

    int type;
    double lb = 0.0;
    double ub = 0.0;
    if(d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)){
      if(d_vars.boundsAreEqual(v)){
        type = GLP_FX;
      }else{
        type = GLP_DB;
      }
      lb = d_vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
      ub = d_vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
    }else if(d_vars.hasUpperBound(v) && !d_vars.hasLowerBound(v)){
      type = GLP_UP;
      ub = d_vars.getUpperBound(v).approx(SMALL_FIXED_DELTA);
    }else if(!d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)){
      type = GLP_LO;
      lb = d_vars.getLowerBound(v).approx(SMALL_FIXED_DELTA);
    }else{
      type = GLP_FR;
    }

    if(d_vars.isAuxiliary(v)){
      int rowIndex = d_rowIndices[v];
      glp_set_row_bnds(d_inputProb, rowIndex, type, lb, ub);
    }else{
      int colIndex = d_colIndices[v];
      // is input is correct here
      int kind = d_vars.isInteger(v) ? GLP_IV : GLP_CV;
      glp_set_col_kind(d_inputProb, colIndex, kind);
      glp_set_col_bnds(d_inputProb, colIndex, type, lb, ub);
    }
  }

  // Count the number of entries
  int numEntries = 0;
  for(DenseMap<int>::const_iterator i = d_rowIndices.begin(), i_end = d_rowIndices.end(); i != i_end; ++i){
    ArithVar v = *i;
    Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
    for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){
      ++numEntries;
    }
  }

  int* ia = new int[numEntries+1];
  int* ja = new int[numEntries+1];
  double* ar = new double[numEntries+1];

  int entryCounter = 0;
  for(DenseMap<int>::const_iterator i = d_rowIndices.begin(), i_end = d_rowIndices.end(); i != i_end; ++i){
    ArithVar v = *i;
    int rowIndex = d_rowIndices[v];

    Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));

    for(Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i){

      const Monomial& mono = *i;
      const Constant& constant = mono.getConstant();
      const VarList& variable = mono.getVarList();

      Node n = variable.getNode();

      Assert(d_vars.hasArithVar(n));
      ArithVar av = d_vars.asArithVar(n);
      int colIndex = d_colIndices[av];
      double coeff = constant.getValue().getDouble();

      ++entryCounter;
      ia[entryCounter] = rowIndex;
      ja[entryCounter] = colIndex;
      ar[entryCounter] = coeff;
    }
  }
  glp_load_matrix(d_inputProb, numEntries, ia, ja, ar);

  delete[] ia;
  delete[] ja;
  delete[] ar;
}
int ApproxGLPK::guessDir(ArithVar v) const{
  if(d_vars.hasUpperBound(v) && !d_vars.hasLowerBound(v)){
    return -1;
  }else if(!d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)){
    return 1;
  }else if(!d_vars.hasUpperBound(v) && !d_vars.hasLowerBound(v)){
    return 0;
  }else{
    int ubSgn = d_vars.getUpperBound(v).sgn();
    int lbSgn = d_vars.getLowerBound(v).sgn();

    if(ubSgn != 0 && lbSgn == 0){
      return -1;
    }else if(ubSgn == 0 && lbSgn != 0){
      return 1;
    }

    return 1;
  }
}

ArithRatPairVec ApproxGLPK::heuristicOptCoeffs() const{
  ArithRatPairVec ret;

  // Strategies are guess:
  // 1 simple shared "ceiling" variable: danoint, pk1
  //  x1 >= c, x1 >= tmp1, x1 >= tmp2, ...
  // 1 large row: fixnet, vpm2, pp08a
  //  (+ .......... ) <= c
  // Not yet supported:
  // 1 complex shared "ceiling" variable: opt1217
  //  x1 >= c, x1 >= (+ ..... ), x1 >= (+ ..... )
  //  and all of the ... are the same sign


  // Candidates:
  // 1) Upper and lower bounds are not equal.
  // 2) The variable is not integer
  // 3a) For columns look for a ceiling variable
  // 3B) For rows look for a large row with

  DenseMap<BoundCounts> d_colCandidates;
  DenseMap<uint32_t> d_rowCandidates;

  double sumRowLength = 0.0;
  uint32_t maxRowLength = 0;
  for(ArithVariables::var_iterator vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end; ++vi){
    ArithVar v = *vi;

    if(s_verbosity >= 2){
      Message() << v  << " ";
      d_vars.printModel(v, Message());
    }

    int type;
    if(d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)){
      if(d_vars.boundsAreEqual(v)){
        type = GLP_FX;
      }else{
        type = GLP_DB;
      }
    }else if(d_vars.hasUpperBound(v) && !d_vars.hasLowerBound(v)){
      type = GLP_UP;
    }else if(!d_vars.hasUpperBound(v) && d_vars.hasLowerBound(v)){
      type = GLP_LO;
    }else{
      type = GLP_FR;
    }

    if(type != GLP_FX && type != GLP_FR){

      if(d_vars.isAuxiliary(v)){
        Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
        uint32_t len = p.size();
        d_rowCandidates.set(v, len);
        sumRowLength += len;
        maxRowLength = std::max(maxRowLength, len);
      }else if(!d_vars.isInteger(v)){
        d_colCandidates.set(v, BoundCounts());
      }
    }
  }

  uint32_t maxCount = 0;
  for(DenseMap<int>::const_iterator i = d_rowIndices.begin(), i_end = d_rowIndices.end(); i != i_end; ++i){
    ArithVar v = *i;

    bool lbCap = d_vars.hasLowerBound(v) && !d_vars.hasUpperBound(v);
    bool ubCap = !d_vars.hasLowerBound(v) && d_vars.hasUpperBound(v);

    if(lbCap || ubCap){
      ConstraintP b = lbCap ? d_vars.getLowerBoundConstraint(v)
        : d_vars.getUpperBoundConstraint(v);

      if(!(b->getValue()).noninfinitesimalIsZero()){ continue; }

      Polynomial poly = Polynomial::parsePolynomial(d_vars.asNode(v));
      if(poly.size() != 2) { continue; }

      Polynomial::iterator j = poly.begin();
      Monomial first = *j;
      ++j;
      Monomial second = *j;

      bool firstIsPos = first.constantIsPositive();
      bool secondIsPos = second.constantIsPositive();

      if(firstIsPos == secondIsPos){ continue; }

      Monomial pos = firstIsPos == lbCap ? first : second;
      Monomial neg = firstIsPos != lbCap ? first : second;
      // pos >= neg
      VarList p = pos.getVarList();
      VarList n = neg.getVarList();
      if(d_vars.hasArithVar(p.getNode())){
        ArithVar ap = d_vars.asArithVar(p.getNode());
        if( d_colCandidates.isKey(ap)){
          BoundCounts bc = d_colCandidates.get(ap);
          bc = BoundCounts(bc.lowerBoundCount(), bc.upperBoundCount()+1);
          maxCount = std::max(maxCount, bc.upperBoundCount());
          d_colCandidates.set(ap, bc);
        }
      }
      if(d_vars.hasArithVar(n.getNode())){
        ArithVar an = d_vars.asArithVar(n.getNode());
        if( d_colCandidates.isKey(an)){
          BoundCounts bc = d_colCandidates.get(an);
          bc = BoundCounts(bc.lowerBoundCount()+1, bc.upperBoundCount());
          maxCount = std::max(maxCount, bc.lowerBoundCount());
          d_colCandidates.set(an, bc);
        }
      }
    }
  }

  // Attempt row
  double avgRowLength = d_rowCandidates.size() >= 1 ?
    ( sumRowLength / d_rowCandidates.size() ) : 0.0;

  // There is a large row among the candidates
  bool guessARowCandidate = maxRowLength >= (10.0 * avgRowLength);

  double rowLengthReq = (maxRowLength * .9);

  if(guessARowCandidate){
    for(DenseMap<uint32_t>::const_iterator i = d_rowCandidates.begin(), iend =d_rowCandidates.end(); i != iend; ++i ){
      ArithVar r = *i;
      uint32_t len = d_rowCandidates[r];

      int dir = guessDir(r);
      if(len >= rowLengthReq){
        if(s_verbosity >= 1){
          Message() << "high row " << r << " " << len << " " << avgRowLength << " " << dir<< endl;
          d_vars.printModel(r, Message());
        }
        ret.push_back(ArithRatPair(r, Rational(dir)));
      }
    }
  }

  // Attempt columns
  bool guessAColCandidate = maxCount >= 4;
  if(guessAColCandidate){
    for(DenseMap<BoundCounts>::const_iterator i = d_colCandidates.begin(), iend = d_colCandidates.end(); i != iend; ++i ){
      ArithVar c = *i;
      BoundCounts bc = d_colCandidates[c];

      int dir = guessDir(c);
      double ubScore = double(bc.upperBoundCount()) / maxCount;
      double lbScore = double(bc.lowerBoundCount()) / maxCount;
      if(ubScore  >= .9 || lbScore >= .9){
        if(s_verbosity >= 1){
          Message() << "high col " << c << " " << bc << " " << ubScore << " " << lbScore << " " << dir << endl;
          d_vars.printModel(c, Message());
        }
        ret.push_back(ArithRatPair(c, Rational(c)));
      }
    }
  }


  return ret;
}

void ApproxGLPK::setOptCoeffs(const ArithRatPairVec& ref){
  DenseMap<double> nbCoeffs;

  for(ArithRatPairVec::const_iterator i = ref.begin(), iend = ref.end(); i != iend; ++i){
    ArithVar v = (*i).first;
    const Rational& q = (*i).second;

    if(d_vars.isAuxiliary(v)){
      // replace the variable by its definition and multiply by q
      Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(v));
      Polynomial pq = p * q;

      for(Polynomial::iterator j = pq.begin(), jend = pq.end(); j != jend; ++j){
        const Monomial& mono = *j;
        const Constant& constant = mono.getConstant();
        const VarList& variable = mono.getVarList();

        Node n = variable.getNode();

        Assert(d_vars.hasArithVar(n));
        ArithVar av = d_vars.asArithVar(n);
        int colIndex = d_colIndices[av];
        double coeff = constant.getValue().getDouble();
        if(!nbCoeffs.isKey(colIndex)){
          nbCoeffs.set(colIndex, 0.0);
        }
        nbCoeffs.set(colIndex, nbCoeffs[colIndex]+coeff);
      }
    }else{
      int colIndex = d_colIndices[v];
      double coeff = q.getDouble();
      if(!nbCoeffs.isKey(colIndex)){
        nbCoeffs.set(colIndex, 0.0);
      }
      nbCoeffs.set(colIndex, nbCoeffs[colIndex]+coeff);
    }
  }
  for(DenseMap<double>::const_iterator ci =nbCoeffs.begin(), ciend = nbCoeffs.end(); ci != ciend; ++ci){
    Index colIndex = *ci;
    double coeff = nbCoeffs[colIndex];
    glp_set_obj_coef(d_inputProb, colIndex, coeff);
  }
}


/*
 * rough strategy:
 *  real relaxation
 *   try approximate real optimization of error function
 *   pivot in its basis
 *   update to its assignment
 *   check with FCSimplex
 *  check integer solution
 *   try approximate mixed integer problem
 *   stop at the first feasible point
 *   pivot in its basis
 *   update to its assignment
 *   check with FCSimplex
 */

void ApproxGLPK::printGLPKStatus(int status, std::ostream& out){
  switch(status){
  case GLP_OPT:
    out << "GLP_OPT" << endl;
    break;
  case GLP_FEAS:
    out << "GLP_FEAS" << endl;
    break;
  case GLP_INFEAS:
    out << "GLP_INFEAS" << endl;
    break;
  case GLP_NOFEAS:
    out << "GLP_NOFEAS" << endl;
    break;
  case GLP_UNBND:
    out << "GLP_UNBND" << endl;
    break;
  case GLP_UNDEF:
    out << "GLP_UNDEF" << endl;
    break;
  default:
    out << "Status unknown" << endl;
    break;
  }
}

ApproxGLPK::~ApproxGLPK(){
  glp_delete_prob(d_inputProb);
  glp_delete_prob(d_realProb);
  glp_delete_prob(d_mipProb);

}

ApproximateSimplex::Solution ApproxGLPK::extractSolution(bool mip) const
{
  Assert(d_solvedRelaxation);
  Assert(!mip || d_solvedMIP);

  ApproximateSimplex::Solution sol;
  DenseSet& newBasis = sol.newBasis;
  DenseMap<DeltaRational>& newValues = sol.newValues;

  glp_prob* prob = mip ? d_mipProb : d_realProb;

  for(ArithVariables::var_iterator i = d_vars.var_begin(), i_end = d_vars.var_end(); i != i_end; ++i){
    ArithVar vi = *i;
    bool isAux = d_vars.isAuxiliary(vi);
    int glpk_index = isAux ? d_rowIndices[vi] : d_colIndices[vi];

    int status = isAux ? glp_get_row_stat(prob, glpk_index)
      : glp_get_col_stat(prob, glpk_index);
    if(s_verbosity >= 2){
      Message() << "assignment " << vi << endl;
    }

    bool useDefaultAssignment = false;

    switch(status){
    case GLP_BS:
      //Message() << "basic" << endl;
      newBasis.add(vi);
      useDefaultAssignment = true;
      break;
    case GLP_NL:
    case GLP_NS:
      if(!mip){
        if(s_verbosity >= 2){ Message() << "non-basic lb" << endl; }
        newValues.set(vi, d_vars.getLowerBound(vi));
      }else{// intentionally fall through otherwise
        useDefaultAssignment = true;
      }
      break;
    case GLP_NU:
      if(!mip){
        if(s_verbosity >= 2){ Message() << "non-basic ub" << endl; }
        newValues.set(vi, d_vars.getUpperBound(vi));
      }else {// intentionally fall through otherwise
        useDefaultAssignment = true;
      }
      break;
    default:
      {
        useDefaultAssignment = true;
      }
      break;
    }

    if(useDefaultAssignment){
      if(s_verbosity >= 2){ Message() << "non-basic other" << endl; }

      double newAssign;
      if(mip){
        newAssign = (isAux ? glp_mip_row_val(prob, glpk_index)
                     :  glp_mip_col_val(prob, glpk_index));
      }else{
        newAssign = (isAux ? glp_get_row_prim(prob, glpk_index)
                     :  glp_get_col_prim(prob, glpk_index));
      }
      const DeltaRational& oldAssign = d_vars.getAssignment(vi);


      if(d_vars.hasLowerBound(vi) &&
         roughlyEqual(newAssign, d_vars.getLowerBound(vi).approx(SMALL_FIXED_DELTA))){
        //Message() << "  to lb" << endl;

        newValues.set(vi, d_vars.getLowerBound(vi));
      }else if(d_vars.hasUpperBound(vi) &&
               roughlyEqual(newAssign, d_vars.getUpperBound(vi).approx(SMALL_FIXED_DELTA))){
        newValues.set(vi, d_vars.getUpperBound(vi));
        // Message() << "  to ub" << endl;
      }else{

        double rounded = round(newAssign);
        if(roughlyEqual(newAssign, rounded)){
          // Message() << "roughly equal " << rounded << " " << newAssign << " " << oldAssign << endl;
          newAssign = rounded;
        }else{
          // Message() << "not roughly equal " << rounded << " " << newAssign << " " << oldAssign << endl;
        }

        DeltaRational proposal;
        if (Maybe<Rational> maybe_new = estimateWithCFE(newAssign))
        {
          proposal = maybe_new.value();
        }
        else
        {
          // failed to estimate the old value. defaulting to the current.
          proposal = d_vars.getAssignment(vi);
        }

        if(roughlyEqual(newAssign, oldAssign.approx(SMALL_FIXED_DELTA))){
          // Message() << "  to prev value" << newAssign << " " << oldAssign << endl;
          proposal = d_vars.getAssignment(vi);
        }


        if(d_vars.strictlyLessThanLowerBound(vi, proposal)){
          //Message() << "  round to lb " << d_vars.getLowerBound(vi) << endl;
          proposal = d_vars.getLowerBound(vi);
        }else if(d_vars.strictlyGreaterThanUpperBound(vi, proposal)){
          //Message() << "  round to ub " << d_vars.getUpperBound(vi) << endl;
          proposal = d_vars.getUpperBound(vi);
        }else{
          //Message() << "  use proposal" << proposal << " " << oldAssign  << endl;
        }
        newValues.set(vi, proposal);
      }
    }
  }
  return sol;
}

double ApproxGLPK::sumInfeasibilities(glp_prob* prob, bool mip) const{
  /* compute the sum of dual infeasibilities */
  double infeas = 0.0;

  for(ArithVariables::var_iterator i = d_vars.var_begin(), i_end = d_vars.var_end(); i != i_end; ++i){
    ArithVar vi = *i;
    bool isAux = d_vars.isAuxiliary(vi);
    int glpk_index = isAux ? d_rowIndices[vi] : d_colIndices[vi];

    double newAssign;
    if(mip){
      newAssign = (isAux ? glp_mip_row_val(prob, glpk_index)
                   :  glp_mip_col_val(prob, glpk_index));
    }else{
      newAssign = (isAux ? glp_get_row_prim(prob, glpk_index)
                   :  glp_get_col_prim(prob, glpk_index));
    }


    double ub = isAux ?
      glp_get_row_ub(prob, glpk_index) : glp_get_col_ub(prob, glpk_index);

    double lb = isAux ?
      glp_get_row_lb(prob, glpk_index) : glp_get_col_lb(prob, glpk_index);

    if(ub != +DBL_MAX){
      if(newAssign > ub){
        double ubinf = newAssign - ub;
        infeas += ubinf;
        Debug("approx::soi") << "ub inf" << vi << " " << ubinf << " " << infeas << endl;
      }
    }
    if(lb != -DBL_MAX){
      if(newAssign < lb){
        double lbinf = lb - newAssign;
        infeas  += lbinf;

        Debug("approx::soi") << "lb inf" << vi << " " << lbinf << " " << infeas << endl;
      }
    }
  }
  return infeas;
}

LinResult ApproxGLPK::solveRelaxation(){
  Assert(!d_solvedRelaxation);

  glp_smcp parm;
  glp_init_smcp(&parm);
  parm.presolve = GLP_OFF;
  parm.meth = GLP_PRIMAL;
  parm.pricing = GLP_PT_PSE;
  parm.it_lim = d_pivotLimit;
  parm.msg_lev = GLP_MSG_OFF;
  if(s_verbosity >= 1){
    parm.msg_lev = GLP_MSG_ALL;
  }

  glp_erase_prob(d_realProb);
  glp_copy_prob(d_realProb, d_inputProb, GLP_OFF);

  int res = glp_simplex(d_realProb, &parm);
  switch(res){
  case 0:
    {
      int status = glp_get_status(d_realProb);
      int iterationcount = glp_get_it_cnt(d_realProb);
      switch(status){
      case GLP_OPT:
      case GLP_FEAS:
      case GLP_UNBND:
        d_solvedRelaxation = true;
        return LinFeasible;
      case GLP_INFEAS:
      case GLP_NOFEAS:
        d_solvedRelaxation = true;
        return LinInfeasible;
      default:
        {
          if(iterationcount >= d_pivotLimit){
            return LinExhausted;
          }
          return LinUnknown;
        }
      }
    }
  default:
    return LinUnknown;
  }
}


struct MirInfo : public CutInfo {

  /** a sum of input rows. */
  PrimitiveVec row_sum;

  /* the delta used */
  double delta;

  /* all of these are length vars == N+M*/
  int nvars;
  char* cset;
  char* subst;
  int*  vlbRows;
  int*  vubRows;
  MirInfo(int execOrd, int ord)
    : CutInfo(MirCutKlass, execOrd, ord)
    , nvars(0)
    , cset(NULL)
    , subst(NULL)
    , vlbRows(NULL)
    , vubRows(NULL)
  {}

  ~MirInfo(){
    clearSets();
  }
  void clearSets(){
    if(cset != NULL){
      delete[] cset;
      delete[] subst;
      delete[] vlbRows;
      delete[] vubRows;
      cset = NULL;
      nvars = 0;
    }
  }
  void initSet(){
    Assert(d_N >= 0);
    Assert(d_mAtCreation >= 0);
    clearSets();

    int vars = 1 + d_N + d_mAtCreation;

    cset = new char[1+vars];
    subst = new char[1+vars];
    vlbRows = new int[1+vars];
    vubRows = new int[1+vars];
  }
};

struct GmiInfo : public CutInfo {
  int basic;
  PrimitiveVec tab_row;
  int* tab_statuses;
  /* has the length tab_row.length */

  GmiInfo(int execOrd, int ord)
    : CutInfo(GmiCutKlass, execOrd, ord)
    , basic(-1)
    , tab_row()
    , tab_statuses(NULL)
  {
    Assert(!initialized_tab());
  }

  ~GmiInfo(){
    if(initialized_tab()){
      clear_tab();
    }
  }

  bool initialized_tab() const {
    return tab_statuses != NULL;
  }

  void init_tab(int N){
    if(initialized_tab()){
      clear_tab();
    }
    tab_row.setup(N);
    tab_statuses = new int[1+N];
  }

  void clear_tab() {
    delete[] tab_statuses;
    tab_statuses = NULL;
    tab_row.clear();
    basic = -1;
  }
};



static void loadCut(glp_tree *tree, CutInfo* cut){
  int ord, cut_len, cut_klass;
  int N, M;
  int* cut_inds;
  double* cut_coeffs;
  int glpk_cut_type;
  double cut_rhs;
  glp_prob* lp;

  lp = glp_ios_get_prob(tree);
  ord = cut->poolOrdinal();

  N = glp_get_num_cols(lp);
  M = glp_get_num_rows(lp);

  cut->setDimensions(N, M);



  // Get the cut
  cut_len = glp_ios_get_cut(tree, ord, NULL, NULL, &cut_klass, NULL, NULL);
  Assert(fromGlpkClass(cut_klass) == cut->getKlass());

  PrimitiveVec& cut_vec = cut->getCutVector();
  cut_vec.setup(cut_len);
  cut_inds = cut_vec.inds;
  cut_coeffs = cut_vec.coeffs;

  cut_vec.len = glp_ios_get_cut(tree, ord, cut_inds, cut_coeffs, &cut_klass, &glpk_cut_type, &cut_rhs);
  Assert(fromGlpkClass(cut_klass) == cut->getKlass());
  Assert(cut_vec.len == cut_len);

  cut->setRhs(cut_rhs);

  cut->setKind( glpk_type_to_kind(glpk_cut_type) );
}


static MirInfo* mirCut(glp_tree *tree, int exec_ord, int cut_ord){
  Debug("approx::mirCut") << "mirCut()" << exec_ord << endl;

  MirInfo* mir;
  mir = new MirInfo(exec_ord, cut_ord);
  loadCut(tree, mir);
  mir->initSet();


  int nrows = glp_ios_cut_get_aux_nrows(tree, cut_ord);

  PrimitiveVec& row_sum = mir->row_sum;
  row_sum.setup(nrows);
  glp_ios_cut_get_aux_rows(tree, cut_ord, row_sum.inds, row_sum.coeffs);

  glp_ios_cut_get_mir_cset(tree, cut_ord, mir->cset);
  mir->delta = glp_ios_cut_get_mir_delta(tree, cut_ord);
  glp_ios_cut_get_mir_subst(tree, cut_ord, mir->subst);
  glp_ios_cut_get_mir_virtual_rows(tree, cut_ord, mir->vlbRows, mir->vubRows);

  if(Debug.isOn("approx::mirCut")){
    Debug("approx::mirCut") << "mir_id: " << exec_ord << endl;
    row_sum.print(Debug("approx::mirCut"));
  }

  return mir;
}

static GmiInfo* gmiCut(glp_tree *tree, int exec_ord, int cut_ord){
  Debug("approx::gmiCut") << "gmiCut()" << exec_ord << endl;

  int gmi_var;
  int write_pos;
  int read_pos;
  int stat;
  int ind;
  int i;

  GmiInfo* gmi;
  glp_prob* lp;

  gmi = new GmiInfo(exec_ord, cut_ord);
  loadCut(tree, gmi);

  lp = glp_ios_get_prob(tree);

  int N = gmi->getN();
  int M = gmi->getMAtCreation();

  // Get the tableau row
  int nrows CVC4_UNUSED = glp_ios_cut_get_aux_nrows(tree, gmi->poolOrdinal());
  Assert(nrows == 1);
  int rows[1+1];
  glp_ios_cut_get_aux_rows(tree, gmi->poolOrdinal(), rows, NULL);
  gmi_var = rows[1];

  gmi->init_tab(N);
  gmi->basic = M+gmi_var;

  Debug("approx::gmiCut")
    << gmi <<" " << gmi->basic << " "
    << cut_ord<<" "  << M <<" " << gmi_var << endl;

  PrimitiveVec& tab_row = gmi->tab_row;
  Debug("approx::gmiCut") << "Is N sufficient here?" << endl;
  tab_row.len = glp_eval_tab_row(lp, gmi->basic, tab_row.inds, tab_row.coeffs);

  Debug("approx::gmiCut") << "gmi_var " << gmi_var << endl;

  Debug("approx::gmiCut") << "tab_pos " << tab_row.len << endl;
  write_pos = 1;
  for(read_pos = 1; read_pos <= tab_row.len; ++read_pos){
    if (fabs(tab_row.coeffs[read_pos]) < 1e-10){
    }else{
      tab_row.coeffs[write_pos] = tab_row.coeffs[read_pos];
      tab_row.inds[write_pos] = tab_row.inds[read_pos];
      ++write_pos;
    }
  }
  tab_row.len = write_pos-1;
  Debug("approx::gmiCut") << "write_pos " << write_pos << endl;
  Assert(tab_row.len > 0);

  for(i = 1; i <= tab_row.len; ++i){
    ind = tab_row.inds[i];
    Debug("approx::gmiCut") << "ind " << i << " " << ind << endl;
    stat = (ind <= M) ?
      glp_get_row_stat(lp, ind) : glp_get_col_stat(lp, ind - M);

    Debug("approx::gmiCut") << "ind " << i << " " << ind << " stat " << stat << endl;
    switch (stat){
    case GLP_NL:
    case GLP_NU:
    case GLP_NS:
      gmi->tab_statuses[i] = stat;
      break;
    case GLP_NF:
    default:
      Unreachable();
    }
  }

  if(Debug.isOn("approx::gmiCut")){
    gmi->print(Debug("approx::gmiCut"));
  }
  return gmi;
}

static BranchCutInfo* branchCut(glp_tree *tree, int exec_ord, int br_var, double br_val, bool down_bad){
  //(tree, br_var, br_val, dn < 0);
  double rhs;
  Kind k;
  if(down_bad){
    // down branch is infeasible
    // x <= floor(v) is infeasible
    // - so x >= ceiling(v) is implied
    k = kind::GEQ;
    rhs = std::ceil(br_val);
  }else{
    // up branch is infeasible
    // x >= ceiling(v) is infeasible
    // - so x <= floor(v) is implied
    k = kind::LEQ;
    rhs = std::floor(br_val);
  }
  BranchCutInfo* br_cut = new BranchCutInfo(exec_ord, br_var, k, rhs);
  return br_cut;
}

static void glpkCallback(glp_tree *tree, void *info){
  AuxInfo* aux = (AuxInfo*)(info);
  TreeLog& tl = *(aux->tl);

  int exec = tl.getExecutionOrd();
  int glpk_node_p = -1;
  int node_ord = -1;

  if(tl.isActivelyLogging()){
    switch(glp_ios_reason(tree)){
    case GLP_LI_DELROW:
      {
        glpk_node_p = glp_ios_curr_node(tree);
        node_ord = glp_ios_node_ord(tree, glpk_node_p);

        int nrows = glp_ios_rows_deleted(tree, NULL);
        int* num = new int[1+nrows];
        glp_ios_rows_deleted(tree, num);

        NodeLog& node = tl.getNode(node_ord);

        RowsDeleted* rd = new RowsDeleted(exec, nrows, num);

        node.addCut(rd);
        delete[] num;
      }
      break;
    case GLP_ICUTADDED:
      {
        int cut_ord = glp_ios_pool_size(tree);
        glpk_node_p = glp_ios_curr_node(tree);
        node_ord = glp_ios_node_ord(tree, glpk_node_p);
        Assert(cut_ord > 0);
        Debug("approx") << "curr node " << glpk_node_p
                        << " cut ordinal " << cut_ord
                        << " node depth " << glp_ios_node_level(tree, glpk_node_p)
                        << endl;
        int klass;
        glp_ios_get_cut(tree, cut_ord, NULL, NULL, &klass, NULL, NULL);

        NodeLog& node = tl.getNode(node_ord);
        switch(klass){
        case GLP_RF_GMI:
          {
            GmiInfo* gmi = gmiCut(tree, exec, cut_ord);
            node.addCut(gmi);
          }
          break;
        case GLP_RF_MIR:
          {
            MirInfo* mir = mirCut(tree, exec, cut_ord);
            node.addCut(mir);
          }
          break;
        case GLP_RF_COV:
          Debug("approx") << "GLP_RF_COV" << endl;
          break;
        case GLP_RF_CLQ:
          Debug("approx") << "GLP_RF_CLQ" << endl;
          break;
        default:
          break;
        }
      }
      break;
    case GLP_ICUTSELECT:
      {
        glpk_node_p = glp_ios_curr_node(tree);
        node_ord = glp_ios_node_ord(tree, glpk_node_p);
        int cuts = glp_ios_pool_size(tree);
        int* ords = new int[1+cuts];
        int* rows = new int[1+cuts];
        int N = glp_ios_selected_cuts(tree, ords, rows);

        NodeLog& nl = tl.getNode(node_ord);
        Debug("approx") << glpk_node_p << " " << node_ord << " " << cuts << " " << N << std::endl;
        for(int i = 1; i <= N; ++i){
          Debug("approx") << "adding to " << node_ord <<" @ i= " << i
                          << " ords[i] = " << ords[i]
                          << " rows[i] = " << rows[i] << endl;
          nl.addSelected(ords[i], rows[i]);
        }
        delete[] ords;
        delete[] rows;
        nl.applySelected();
      }
    break;
  case GLP_LI_BRANCH:
    {
      // a branch was just made
      int br_var;
      int p, dn, up;
      int p_ord, dn_ord, up_ord;
      double br_val;
      br_var = glp_ios_branch_log(tree, &br_val, &p, &dn, &up);
      p_ord = glp_ios_node_ord(tree, p);

      dn_ord = (dn >= 0) ? glp_ios_node_ord(tree, dn) : -1;
      up_ord = (up >= 0) ? glp_ios_node_ord(tree, up) : -1;

      Debug("approx::") << "branch: "<< br_var << " "  << br_val << " tree " << p << " " << dn << " " << up << endl;
      Debug("approx::") << "\t " << p_ord << " " << dn_ord << " " << up_ord << endl;
      if(dn < 0 && up < 0){
        Debug("approx::") << "branch close " << exec << endl;
        NodeLog& node = tl.getNode(p_ord);
        BranchCutInfo* cut_br = branchCut(tree, exec, br_var, br_val, dn < 0);
        node.addCut(cut_br);
        tl.close(p_ord);
      }else if(dn < 0 || up < 0){
        Debug("approx::") << "branch cut" << exec << endl;
        NodeLog& node = tl.getNode(p_ord);
        BranchCutInfo* cut_br = branchCut(tree, exec, br_var, br_val, dn < 0);
        node.addCut(cut_br);
      }else{
        Debug("approx::") << "normal branch" << endl;
        tl.branch(p_ord, br_var, br_val, dn_ord, up_ord);
      }
    }
    break;
    case GLP_LI_CLOSE:
      {
        glpk_node_p = glp_ios_curr_node(tree);
        node_ord = glp_ios_node_ord(tree, glpk_node_p);
        Debug("approx::") << "close " << glpk_node_p << endl;
        tl.close(node_ord);
      }
      break;
    default:
      break;
    }
  }

  switch(glp_ios_reason(tree)){
  case GLP_IBINGO:
    Debug("approx::") << "bingo" << endl;
    aux->term = MipBingo;
    glp_ios_terminate(tree);
    break;
  case GLP_ICUTADDED:
    {
      tl.addCut();
    }
    break;
  case GLP_LI_BRANCH:
    {
      int p, dn, up;
      int br_var = glp_ios_branch_log(tree, NULL, &p, &dn, &up);

      if(br_var >= 0){
        unsigned v = br_var;
        tl.logBranch(v);
        int depth = glp_ios_node_level(tree, p);
        unsigned ubl =  (aux->branchLimit) >= 0 ? ((unsigned)(aux->branchLimit)) : 0u;
        if(tl.numBranches(v) >= ubl || depth >= (aux->branchDepth)){
          aux->term = BranchesExhausted;
          glp_ios_terminate(tree);
        }
      }
    }
    break;
  case GLP_LI_CLOSE:
    break;
  default:
    {
      glp_prob* prob = glp_ios_get_prob(tree);
      int iterationcount = glp_get_it_cnt(prob);
      if(exec > (aux->pivotLimit)){
        aux->term = ExecExhausted;
        glp_ios_terminate(tree);
      }else if(iterationcount > (aux->pivotLimit)){
        aux->term = PivotsExhauasted;
        glp_ios_terminate(tree);
      }
    }
    break;
  }
}

std::vector<const CutInfo*> ApproxGLPK::getValidCuts(const NodeLog& con)
{
  std::vector<const CutInfo*> proven;
  int nid = con.getNodeId();
  for(NodeLog::const_iterator j = con.begin(), jend=con.end(); j!=jend; ++j){
    CutInfo* cut = *j;

    if(cut->getKlass() != RowsDeletedKlass){
      if(!cut->reconstructed()){
        Assert(!cut->reconstructed());
        tryCut(nid, *cut);
      }
    }

    if(cut->proven()){
      proven.push_back(cut);
    }
  }
  return proven;
}

ArithVar ApproxGLPK::getBranchVar(const NodeLog& con) const{
  int br_var = con.branchVariable();
  return getArithVarFromStructural(br_var);
}


MipResult ApproxGLPK::solveMIP(bool activelyLog){
  Assert(d_solvedRelaxation);
  // Explicitly disable presolving
  // We need the basis thus the presolver must be off!
  // This is default, but this is just being cautious.
  AuxInfo aux;
  aux.pivotLimit = d_pivotLimit;
  aux.branchLimit = d_branchLimit;
  aux.branchDepth = d_maxDepth;
  aux.tl = &d_log;
  aux.term = MipUnknown;

  d_log.reset(d_rootRowIds);
  if(activelyLog){
    d_log.makeActive();
  }else{
    d_log.makeInactive();
  }

  glp_iocp parm;
  glp_init_iocp(&parm);
  parm.presolve = GLP_OFF;
  parm.pp_tech = GLP_PP_NONE;
  parm.fp_heur = GLP_ON;
  parm.gmi_cuts = GLP_ON;
  parm.mir_cuts = GLP_ON;
  parm.cov_cuts = GLP_ON;
  parm.cb_func = glpkCallback;
  parm.cb_info = &aux;
  parm.msg_lev = GLP_MSG_OFF;
  if(s_verbosity >= 1){
    parm.msg_lev = GLP_MSG_ALL;
  }

  glp_erase_prob(d_mipProb);
  glp_copy_prob(d_mipProb, d_realProb, GLP_OFF);

  int res = glp_intopt(d_mipProb, &parm);

  Debug("approx::solveMIP") << "res "<<res<<" aux.term "<< aux.term << endl;

  switch(res){
  case 0:
  case GLP_ESTOP:
    {
      int status = glp_mip_status(d_mipProb);
      Debug("approx::") << "status " << status << endl;
      switch(status){
      case GLP_OPT:
      case GLP_FEAS:
        d_solvedMIP = true;
        Debug("approx::") << "bingo here!" << endl;
        return MipBingo;
      case GLP_NOFEAS:
        d_solvedMIP = true;
        return MipClosed;
      default:
        if(aux.term == MipBingo){
          d_solvedMIP = true;
          Debug("approx::") << "bingo here?" << endl;
        }
        return aux.term;
      }
    }
  default:
    return MipUnknown;
  }
}

// Node explainSet(const set<ConstraintP>& inp){
//   Assert(!inp.empty());
//   NodeBuilder<> nb(kind::AND);
//   set<ConstraintP>::const_iterator iter, end;
//   for(iter = inp.begin(), end = inp.end(); iter != end; ++iter){
//     const ConstraintP c = *iter;
//     Assert(c != NullConstraint);
//     c->explainForConflict(nb);
//   }
//   Node ret = safeConstructNary(nb);
//   Node rew = Rewriter::rewrite(ret);
//   if(rew.getNumChildren() < ret.getNumChildren()){
//     //Debug("approx::") << "explainSet " << ret << " " << rew << endl;
//   }
//   return rew;
// }

DeltaRational sumConstraints(const DenseMap<Rational>& xs, const DenseMap<ConstraintP>& cs, bool* anyinf){
  if(anyinf != NULL){
    *anyinf = false;
  }

  DeltaRational beta(0);
  DenseMap<Rational>::const_iterator iter, end;
  iter = xs.begin();
  end = xs.end();

  Debug("approx::sumConstraints") << "sumConstraints";
  for(; iter != end; ++iter){
    ArithVar x = *iter;
    const Rational& psi = xs[x];
    ConstraintP c = cs[x];
    Assert(c != NullConstraint);

    const DeltaRational& bound = c->getValue();
    beta += bound * psi;
    Debug("approx::sumConstraints") << " +("<<bound << "*" << psi <<")";
    if(anyinf != NULL ){
      *anyinf = *anyinf || !bound.infinitesimalIsZero();
    }
  }
  Debug("approx::sumConstraints") << "= " << beta << endl;

  return beta;
}

// remove fixed variables from the vector
void removeFixed(const ArithVariables& vars, DenseVector& dv, set<ConstraintP>& exp){
  DenseMap<Rational>& vec = dv.lhs;
  Rational& removed = dv.rhs;
  vector<ArithVar> equal;
  DenseMap<Rational>::const_iterator vec_iter, vec_end;
  vec_iter = vec.begin(), vec_end = vec.end();
  for(; vec_iter != vec_end; ++vec_iter){
    ArithVar x = *vec_iter;
    if(vars.boundsAreEqual(x)){
      equal.push_back(x);
    }
  }
  vector<ArithVar>::const_iterator equal_iter, equal_end;
  equal_iter = equal.begin(), equal_end = equal.end();
  for(; equal_iter != equal_end; ++equal_iter){
    ArithVar x = *equal_iter;
    Assert(vars.boundsAreEqual(x));
    const DeltaRational& lb = vars.getLowerBound(x);
    Assert(lb.infinitesimalIsZero());
    removed -= (vec[x]) * lb.getNoninfinitesimalPart();

    vec.remove(x);

    std::pair<ConstraintP, ConstraintP> p = vars.explainEqualBounds(x);
    exp.insert(p.first);
    Debug("removeFixed") << "remove fixed " << p.first << endl;
    if(p.second != NullConstraint){
      exp.insert(p.second);
      Debug("removeFixed") << "remove fixed " << p.second << endl;
    }
  }
}
void removeZeroes(DenseMap<Rational>& v){
  // Remove Slack variables
  vector<ArithVar> zeroes;
  DenseMap<Rational>::const_iterator i, iend;
  for(i = v.begin(), iend = v.end(); i != iend; ++i){
    ArithVar x = *i;
    if(v[x].isZero()){
      zeroes.push_back(x);
    }
  }

  vector<ArithVar>::const_iterator j, jend;
  for(j = zeroes.begin(), jend = zeroes.end(); j != jend; ++j){
    ArithVar x = *j;
    v.remove(x);
  }
}
void removeZeroes(DenseVector& v){
  removeZeroes(v.lhs);
}

void removeAuxillaryVariables(const ArithVariables& vars, DenseMap<Rational>& vec){
  // Remove auxillary variables
  vector<ArithVar> aux;
  DenseMap<Rational>::const_iterator vec_iter, vec_end;
  vec_iter = vec.begin(), vec_end = vec.end();
  for(; vec_iter != vec_end; ++vec_iter){
    ArithVar x = *vec_iter;
    if(vars.isAuxiliary(x)){
      aux.push_back(x);
    }
  }

  vector<ArithVar>::const_iterator aux_iter, aux_end;
  aux_iter = aux.begin(), aux_end = aux.end();
  for(; aux_iter != aux_end; ++aux_iter){
    ArithVar s = *aux_iter;
    Rational& s_coeff = vec.get(s);
    Assert(vars.isAuxiliary(s));
    Assert(vars.hasNode(s));
    Node sAsNode = vars.asNode(s);
    Polynomial p = Polynomial::parsePolynomial(sAsNode);
    for(Polynomial::iterator j = p.begin(), p_end=p.end(); j != p_end; ++j){
      Monomial m = *j;
      const Rational& ns_coeff = m.getConstant().getValue();
      Node vl = m.getVarList().getNode();
      ArithVar ns = vars.asArithVar(vl);
      Rational prod = s_coeff * ns_coeff;
      if(vec.isKey(ns)){
        vec.get(ns) += prod;
      }else{
        vec.set(ns, prod);
      }
    }
    s_coeff = Rational(0); // subtract s_coeff * s from vec
  }
  removeZeroes(vec);
}

ArithVar ApproxGLPK::_getArithVar(int nid, int M, int ind) const{
  if(ind <= 0){
    return ARITHVAR_SENTINEL;
  }else if(ind <= M){
    return getArithVarFromRow(nid, ind);
  }else{
    return getArithVarFromStructural(ind - M);
  }
}


bool ApproxGLPK::guessIsConstructable(const DenseMap<Rational>& guess) const {
  // basic variable
  // sum g[i] * x_i
  DenseMap<Rational> g = guess;
  removeAuxillaryVariables(d_vars, g);

  if(Debug.isOn("guessIsConstructable")){
    if(!g.empty()){
      Debug("approx::guessIsConstructable") << "guessIsConstructable failed " << g.size() << endl;
      DenseVector::print(Debug("approx::guessIsConstructable"), g);
      Debug("approx::guessIsConstructable") << endl;
    }
  }
  return g.empty();
}

bool ApproxGLPK::loadToBound(int nid, int M, int len, int* inds, int* statuses, DenseMap<ConstraintP>& toBound) const{
  for(int i = 1; i <= len; ++i){
    int status = statuses[i];
    int ind = inds[i];
    ArithVar v = _getArithVar(nid, M, ind);
    ConstraintP c = NullConstraint;
    if(v == ARITHVAR_SENTINEL){ return true; }

    switch(status){
    case GLP_NL:
      c = d_vars.getLowerBoundConstraint(v);
      break;
    case GLP_NU:
    case GLP_NS: // upper bound sufficies for fixed variables
      c = d_vars.getUpperBoundConstraint(v);
      break;
    case GLP_NF:
    default:
      return true;
    }
    if(c == NullConstraint){
      Debug("approx::") << "couldn't find " << v << " @ " << nid << endl;
      return true;
    }
    Assert(c != NullConstraint);
    toBound.set(v, c);
  }
  return false;
}

bool ApproxGLPK::checkCutOnPad(int nid, const CutInfo& cut) const{

  Debug("approx::checkCutOnPad") << "checkCutOnPad(" << nid <<", " << cut.getId() <<")"<<endl;

  const DenseMap<Rational>& constructedLhs = d_pad.d_cut.lhs;
  const Rational& constructedRhs = d_pad.d_cut.rhs;
  std::unordered_set<ArithVar> visited;

  if(constructedLhs.empty()){
    Debug("approx::checkCutOnPad") << "its empty?" <<endl;
    return true;
  }
  if(cut.getKind() != d_pad.d_cutKind) {
    Debug("approx::checkCutOnPad") << "rel doesn't match" << endl;
    return true;
  }

  const PrimitiveVec& cv = cut.getCutVector();
  for(int i = 1; i <= cv.len; ++i){
    int ind = cv.inds[i]; // this is always a structural variable
    double coeff = cv.coeffs[i];



    if(!d_colToArithVar.isKey(ind)){ return true; }
    ArithVar x = d_colToArithVar[ind];
    //if(x == ARITHVAR_SENTINEL){ return true; }
    visited.insert(x);


    if(!constructedLhs.isKey(x)){
      if(Debug.isOn("approx::checkCutOnPad")){
        Debug("approx::checkCutOnPad") << " didn't find key for " << x << std::endl;
        cut.print(Debug("approx::checkCutOnPad"));
        Debug("approx::checkCutOnPad") << endl;
        d_pad.d_cut.print(Debug("approx::checkCutOnPad"));
        Debug("approx::checkCutOnPad") << endl;
      }
      return true;
    }

    const Rational& onConstructed = constructedLhs[x];

    Debug("approx::checkCutOnPad") << ind << " " << coeff  << " " << endl;
    Debug("approx::checkCutOnPad") << " " << x << " " << onConstructed << endl;

    if(!roughlyEqual(coeff, onConstructed.getDouble())){
      Debug("approx::checkCutOnPad") << "coeff failure" << endl;
      return true;
    }
  }
  if(visited.size() != constructedLhs.size()){
    Debug("approx::checkCutOnPad") << "size mismatch" << endl;
    return true;
  }


  if(!roughlyEqual(cut.getRhs(), constructedRhs.getDouble())){
    Debug("approx::checkCutOnPad")
      << "norm rhs is off " << cut.getRhs() << " " << constructedRhs << endl;
    return true;
  }
  return false;
}



bool ApproxGLPK::attemptBranchCut(int nid, const BranchCutInfo& br_cut){
  d_pad.clear();

  const PrimitiveVec& cut_vec = br_cut.getCutVector();
  int structural = cut_vec.inds[1];
  Assert(roughlyEqual(cut_vec.coeffs[1], +1.0));

  ArithVar x = getArithVarFromStructural(structural);
  d_pad.d_failure = (x == ARITHVAR_SENTINEL);
  if(d_pad.d_failure){ return true; }

  Kind brKind = br_cut.getKind();

  d_pad.d_failure = (brKind != kind::LEQ && brKind != kind::GEQ);
  if(d_pad.d_failure){ return true; }

  d_pad.d_cutKind = brKind;
  d_pad.d_cut.lhs.set(x, Rational(1));

  Rational& rhs = d_pad.d_cut.rhs;
  Maybe<Rational> br_cut_rhs = Rational::fromDouble(br_cut.getRhs());
  if (!br_cut_rhs)
  {
    return true;
  }

  rhs = estimateWithCFE(br_cut_rhs.value(), Integer(1));
  d_pad.d_failure = !rhs.isIntegral();
  if(d_pad.d_failure) { return true; }

  d_pad.d_failure = checkCutOnPad(nid, br_cut);
  if(d_pad.d_failure){ return true; }

  return false;
}

bool ApproxGLPK::attemptGmi(int nid, const GmiInfo& gmi){
  d_pad.clear();

  d_pad.d_cutKind = kind::GEQ;

  int M = gmi.getMAtCreation();
  ArithVar b = _getArithVar(nid, M, gmi.basic);
  d_pad.d_failure = (b == ARITHVAR_SENTINEL);
  if(d_pad.d_failure){ return true; }

  d_pad.d_failure = !d_vars.isIntegerInput(b);
  if(d_pad.d_failure){ return true; }

  d_pad.d_basic = b;


  const PrimitiveVec& tab = gmi.tab_row;
  d_pad.d_failure = attemptConstructTableRow(nid, M, tab);
  if(d_pad.d_failure){ return true; }

  int* statuses = gmi.tab_statuses;
  DenseMap<ConstraintP>& toBound = d_pad.d_toBound;
  d_pad.d_failure = loadToBound(nid, M, tab.len, tab.inds, statuses, toBound);
  if(d_pad.d_failure){ return true; }

  d_pad.d_failure = constructGmiCut();
  if(d_pad.d_failure){ return true; }

  d_pad.d_failure = checkCutOnPad(nid, gmi);
  if(d_pad.d_failure){ return true; }

  return false;
}

bool ApproxGLPK::applyCMIRRule(int nid, const MirInfo& mir){

  const DenseMap<Rational>& compRanges = d_pad.d_compRanges;

  DenseMap<Rational>& alpha = d_pad.d_alpha.lhs;
  Rational& b = d_pad.d_alpha.rhs;

  Maybe<Rational> delta = estimateWithCFE(mir.delta);
  if (!delta)
  {
    return true;
  }

  d_pad.d_failure = (delta.value().sgn() <= 0);
  if(d_pad.d_failure){ return true; }

  Debug("approx::mir") << "applyCMIRRule() " << delta << " " << mir.delta << endl;

  DenseMap<Rational>::const_iterator iter, iend;
  iter = alpha.begin(), iend = alpha.end();
  for(; iter != iend; ++iter){
    ArithVar v = *iter;
    const Rational& curr = alpha[v];
    Rational next = curr / delta.value();
    if(compRanges.isKey(v)){
      b -= curr * compRanges[v];
      alpha.set(v, - next);
    }else{
      alpha.set(v, next);
    }
  }
  b = b / delta.value();

  Rational roundB = (b + Rational(1,2)).floor();
  d_pad.d_failure = (b - roundB).abs() < Rational(1,90);
  // intensionally more generous than glpk here
  if(d_pad.d_failure){ return true; }

  Rational one(1);
  Rational fb = b.floor_frac();
  Rational one_sub_fb = one - fb;
  Rational gamma = (one / one_sub_fb);

  DenseMap<Rational>& cut = d_pad.d_cut.lhs;
  Rational& beta = d_pad.d_cut.rhs;

  iter = alpha.begin(), iend = alpha.end();
  for(; iter != iend; ++iter){
    ArithVar v = *iter;
    const Rational& a_j = alpha[v];
    if(d_vars.isIntegerInput(v)){
      Rational floor_aj = a_j.floor();
      Rational frac_aj = a_j.floor_frac();
      if(frac_aj <= fb){
        cut.set(v, floor_aj);
      }else{
        Rational tmp =  ((frac_aj - fb) / one_sub_fb);
        cut.set(v, floor_aj + tmp);
      }
    }else{
      cut.set(v, a_j * gamma);
    }
  }
  beta = b.floor();

  iter = cut.begin(), iend = cut.end();
  for(; iter != iend; ++iter){
    ArithVar v = *iter;
    if(compRanges.isKey(v)){
      Rational neg = - cut[v];
      beta += neg * compRanges[v];
      cut.set(v, neg);
    }
  }

  return false;
}

bool ApproxGLPK::attemptMir(int nid, const MirInfo& mir){
  d_pad.clear();

  d_pad.d_cutKind = kind::LEQ;

  // virtual bounds must be done before slacks
  d_pad.d_failure = loadVirtualBoundsIntoPad(nid, mir);
  if(d_pad.d_failure){ return true; }

  d_pad.d_failure = loadSlacksIntoPad(nid, mir);
  if(d_pad.d_failure){ return true; }


  d_pad.d_failure = loadRowSumIntoAgg(nid, mir.getMAtCreation(), mir.row_sum);
  if(d_pad.d_failure){ return true; }

  removeFixed(d_vars, d_pad.d_agg, d_pad.d_explanation);

  d_pad.d_failure = buildModifiedRow(nid, mir);
  if(d_pad.d_failure){ return true; }

  d_pad.d_failure =  constructMixedKnapsack();
  if(d_pad.d_failure){ return true; }

  d_pad.d_failure = makeRangeForComplemented(nid, mir);
  if(d_pad.d_failure){ return true; }

  d_pad.d_failure = applyCMIRRule(nid, mir);
  if(d_pad.d_failure){ return true; }

  d_pad.d_failure = replaceSlacksOnCuts();
  if(d_pad.d_failure){ return true; }

  removeAuxillaryVariables(d_vars, d_pad.d_cut.lhs);

  d_pad.d_failure = checkCutOnPad(nid, mir);
  if(d_pad.d_failure){ return true; }

  return false;
  //return makeCutNodes(nid, mir);
}

/** Returns true on failure. */
bool ApproxGLPK::loadVB(int nid, int M, int j, int ri, bool wantUb, VirtualBound& tmp){
  if(ri <= 0) { return true; }

  static int instance = 0;
  ++instance;
  Debug("glpk::loadVB") << "loadVB() " << instance << endl;

  ArithVar rowVar = _getArithVar(nid, M, ri);
  ArithVar contVar = _getArithVar(nid, M, j);
  if(rowVar == ARITHVAR_SENTINEL){
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " rowVar is ARITHVAR_SENTINEL " << rowVar << endl;
    return true;
  }
  if(contVar == ARITHVAR_SENTINEL){
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " contVar is ARITHVAR_SENTINEL " << contVar << endl;        
    return true; }

  if(!d_vars.isAuxiliary(rowVar)){
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " rowVar is not auxilliary " << rowVar << endl;    
    return true;
  }
  // is integer is correct here
  if(d_vars.isInteger(contVar)){
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " contVar is integer " << contVar << endl;    
    return true;
  }

  ConstraintP lb = d_vars.getLowerBoundConstraint(rowVar);
  ConstraintP ub = d_vars.getUpperBoundConstraint(rowVar);

  if(lb != NullConstraint && ub != NullConstraint){
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " lb and ub are both NULL " << lb << " " << ub << endl;    
    return true;
  }

  ConstraintP rcon = lb == NullConstraint ? ub : lb;
  if(rcon == NullConstraint) {
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " rcon is NULL " << rcon << endl;    
    return true;
  }

  if(!rcon->getValue().isZero()){
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " rcon value is not 0 " << rcon->getValue() << endl;
    return true;
  }

  if(!d_vars.hasNode(rowVar)){
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " does not have node " << rowVar << endl;
    return true;
  }

  Polynomial p = Polynomial::parsePolynomial(d_vars.asNode(rowVar));
  if(p.size() != 2) {  
    Debug("glpk::loadVB") << "loadVB() " << instance << " polynomial is not binary: " << p.getNode() << endl;
    return true;
  }

  Monomial first = p.getHead(), second = p.getTail().getHead();
  Rational c1 = first.getConstant().getValue();
  Rational c2 = second.getConstant().getValue();
  Node nx1 = first.getVarList().getNode();
  Node nx2 = second.getVarList().getNode();

  if(!d_vars.hasArithVar(nx1)) {
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " does not have a variable for nx1: " << nx1 << endl;
    return true;
  }
  if(!d_vars.hasArithVar(nx2)) {
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " does not have a variable for nx2 " << nx2 << endl;
    return true;
  }
  ArithVar x1 = d_vars.asArithVar(nx1), x2 = d_vars.asArithVar(nx2);

  Assert(x1 != x2);
  Assert(!c1.isZero());
  Assert(!c2.isZero());

  Debug("glpk::loadVB")
    << " lb " << lb
    << " ub " << ub
    << " rcon " << rcon
    << " x1 " << x1
    << " x2 " << x2
    << " c1 " << c1
    << " c2 " << c2 << endl;

  ArithVar iv = (x1 == contVar) ? x2 : x1;
  Rational& cc = (x1 == contVar) ? c1 : c2;
  Rational& ic = (x1 == contVar) ? c2 : c1;

  Debug("glpk::loadVB")
    << " cv " << contVar
    << " cc " << cc
    << " iv " << iv
    << " c2 " << ic << endl;

  if(!d_vars.isIntegerInput(iv)){
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " iv is not an integer input variable " << iv << endl;    
    return true;
  }
  // cc * cv + ic * iv <= 0 or
  // cc * cv + ic * iv <= 0

  if(rcon == ub){ // multiply by -1
    cc = -cc; ic = - ic;
  }
  Debug("glpk::loadVB") << " cv " << contVar
                        << " cc " << cc
                        << " iv " << iv
                        << " c2 " << ic << endl;

  // cc * cv + ic * iv >= 0
  // cc * cv >= -ic * iv
  // if cc < 0:
  //   cv <= -ic/cc * iv
  // elif cc > 0:
  //   cv >= -ic/cc * iv
  Assert(!cc.isZero());
  Rational d = -ic/cc;
  Debug("glpk::loadVB") << d << " " << cc.sgn() << endl;
  bool nowUb = cc.sgn() < 0;
  if(wantUb != nowUb) {
    Debug("glpk::loadVB") << "loadVB() " << instance
                          << " wantUb is not nowUb " << wantUb << " " << nowUb << endl;    
    
    return true;
  }

  Kind rel = wantUb ? kind::LEQ : kind::GEQ;

  tmp = VirtualBound(contVar, rel, d, iv, rcon);
    Debug("glpk::loadVB") << "loadVB() " << instance << " was successful" << endl;    
  return false;
}

bool ApproxGLPK::loadVirtualBoundsIntoPad(int nid, const MirInfo& mir){
  Assert(mir.vlbRows != NULL);
  Assert(mir.vubRows != NULL);

  int N = mir.getN();
  int M = mir.getMAtCreation();

  // Load the virtual bounds first
  VirtualBound tmp;
  for(int j=1; j <= N+M; ++j){
    if(!loadVB(nid, M, j, mir.vlbRows[j], false, tmp)){
      if(d_pad.d_vlb.isKey(tmp.x)){ return true; }
      d_pad.d_vlb.set(tmp.x, tmp);
    }else if(mir.vlbRows[j] > 0){
      Debug("approx::mir") << "expected vlb to work" << endl;
    }
    if(!loadVB(nid, M, j, mir.vubRows[j], true, tmp)){
      if(d_pad.d_vub.isKey(tmp.x)){ return true; }
      d_pad.d_vub.set(tmp.x, tmp);
    }else if(mir.vubRows[j] > 0){
      Debug("approx::mir") << "expected vub to work" << endl;
    }
  }
  return false;
}

bool ApproxGLPK::loadSlacksIntoPad(int nid, const MirInfo& mir){
  Assert(mir.vlbRows != NULL);
  Assert(mir.vubRows != NULL);

  int N = mir.getN();
  int M = mir.getMAtCreation();

  bool useVB;
  // Load the virtual bounds first
  SlackReplace rep;
  bool lb;
  ConstraintP b;
  Debug("approx::mir") << "loadSlacksIntoPad(): N="<<N<<", M=" << M << std::endl;
  for(int j=1; j <= N+M; ++j){
    ArithVar v = _getArithVar(nid, M, j);
    if(v == ARITHVAR_SENTINEL){
      Debug("approx::mir") << " for: " << j << " no variable" << endl;
      continue;
    }
    rep = SlackUndef;
    char sub = mir.subst[j];
    switch(sub){
    case 'L':
    case 'U':
      lb = (sub == 'L');
      useVB = lb ? (mir.vlbRows[j] > 0) : (mir.vubRows[j] > 0);
      if(useVB){
        if(lb ? d_pad.d_vlb.isKey(v) : d_pad.d_vub.isKey(v)){
          rep = lb ? SlackVLB : SlackVUB;
        }
      }else{
        b = lb ? d_vars.getLowerBoundConstraint(v)
          : d_vars.getUpperBoundConstraint(v);
        if(b != NullConstraint){
          if(b->getValue().infinitesimalIsZero()){
            rep = lb ? SlackLB : SlackUB;
          }
        }
      }

      Debug("approx::mir") << " for: " << j << ", " << v;
      Debug("approx::mir") << " " << ((rep != SlackUndef) ? "succ" : "fail") << " ";
      Debug("approx::mir") << sub << " " << rep << " " << mir.vlbRows[j] << " " << mir.vubRows[j]
                           << endl;
      if(rep != SlackUndef){
        d_pad.d_slacks.set(v,rep);
      }
      break;
    case '?':
      continue;
    default:
      Debug("approx::mir") << " for: " << j << " got subst " << (int)sub << endl;
      continue;
    }
  }
  return false;
}

bool ApproxGLPK::replaceSlacksOnCuts(){
  vector<ArithVar> virtualVars;

  DenseMap<Rational>& cut = d_pad.d_cut.lhs;
  Rational& cutRhs = d_pad.d_cut.rhs;

  DenseMap<Rational>::const_iterator iter, iend;
  iter = cut.begin(), iend = cut.end();
  for(; iter != iend; ++iter){
    ArithVar x = *iter;
    SlackReplace rep = d_pad.d_slacks[x];
    if(d_vars.isIntegerInput(x)){
      Assert(rep == SlackLB || rep == SlackUB);
      Rational& a = cut.get(x);

      const DeltaRational& bound = (rep == SlackLB) ?
        d_vars.getLowerBound(x) : d_vars.getUpperBound(x);
      Assert(bound.infinitesimalIsZero());
      Rational prod = a * bound.getNoninfinitesimalPart();
      if(rep == SlackLB){
        cutRhs += prod;
      }else{
        cutRhs -= prod;
        a = -a;
      }
    }else if(rep == SlackVLB){
      virtualVars.push_back(d_pad.d_vlb[x].y);
    }else if(rep == SlackVUB){
      virtualVars.push_back(d_pad.d_vub[x].y);
    }
  }

  for(size_t i = 0; i < virtualVars.size(); ++i){
    ArithVar x = virtualVars[i];
    if(!cut.isKey(x)){
      cut.set(x, Rational(0));
    }
  }

  iter = cut.begin(), iend = cut.end();
  for(; iter != iend; ++iter){
    ArithVar x = *iter;
    if(!d_vars.isIntegerInput(x)){
      SlackReplace rep = d_pad.d_slacks[x];
      Rational& a = cut.get(x);
      switch(rep){
      case SlackLB:
        {
          const DeltaRational& bound = d_vars.getLowerBound(x);
          Assert(bound.infinitesimalIsZero());
          cutRhs += a * bound.getNoninfinitesimalPart();
        }
        break;
      case SlackUB:
        {
          const DeltaRational& bound = d_vars.getUpperBound(x);
          Assert(bound.infinitesimalIsZero());
          cutRhs -= a * bound.getNoninfinitesimalPart();
          a = -a;
        }
        break;
      case SlackVLB:
      case SlackVUB:
        {
          bool lb = (rep == SlackVLB);
          const VirtualBound& vb = lb ?
            d_pad.d_vlb[x] : d_pad.d_vub[x];
          ArithVar y = vb.y;
          Assert(vb.x == x);
          Assert(cut.isKey(y));
          Rational& ycoeff = cut.get(y);
          if(lb){
            ycoeff -= a * vb.d;
          }else{
            ycoeff += a * vb.d;
            a = -a;
          }
        }
        break;
      default:
        return true;
      }
    }
  }
  removeZeroes(cut);
  return false;
}

bool ApproxGLPK::loadRowSumIntoAgg(int nid, int M, const PrimitiveVec& row_sum){
  DenseMap<Rational>& lhs = d_pad.d_agg.lhs;
  d_pad.d_agg.rhs = Rational(0);

  int len = row_sum.len;
  for(int i = 1; i <= len; ++i){
    int aux_ind = row_sum.inds[i]; // auxillary index
    double coeff = row_sum.coeffs[i];
    ArithVar x = _getArithVar(nid, M, aux_ind);
    if(x == ARITHVAR_SENTINEL){ return true; }
    Maybe<Rational> c = estimateWithCFE(coeff);
    if (!c)
    {
      return true;
    }

    if (lhs.isKey(x))
    {
      lhs.get(x) -= c.value();
    }
    else
    {
      lhs.set(x, -c.value());
    }
  }

  Debug("approx::mir") << "beg loadRowSumIntoAgg() 1" << endl;
  if(Debug.isOn("approx::mir")) { DenseVector::print(Debug("approx::mir"), lhs); }
  removeAuxillaryVariables(d_vars, lhs);
  Debug("approx::mir") << "end loadRowSumIntoAgg() 1" << endl;

  if(Debug.isOn("approx::mir")){
    Debug("approx::mir") << "loadRowSumIntoAgg() 2" << endl;
    DenseVector::print(Debug("approx::mir"), lhs);
    Debug("approx::mir") << "end loadRowSumIntoAgg() 2" << endl;
  }

  for(int i = 1; i <= len; ++i){
    int aux_ind = row_sum.inds[i]; // auxillary index
    double coeff = row_sum.coeffs[i];
    ArithVar x = _getArithVar(nid, M, aux_ind);
    Assert(x != ARITHVAR_SENTINEL);
    Maybe<Rational> c = estimateWithCFE(coeff);
    if (!c)
    {
      return true;
    }
    Assert(!lhs.isKey(x));
    lhs.set(x, c.value());
  }

  if(Debug.isOn("approx::mir")){
    Debug("approx::mir") << "loadRowSumIntoAgg() 2" << endl;
    DenseVector::print(Debug("approx::mir"), lhs);
    Debug("approx::mir") << "end loadRowSumIntoAgg() 3" << endl;
  }
  return false;
}

bool ApproxGLPK::buildModifiedRow(int nid, const MirInfo& mir){
  const DenseMap<Rational>& agg = d_pad.d_agg.lhs;
  const Rational& aggRhs = d_pad.d_agg.rhs;
  DenseMap<Rational>& mod = d_pad.d_mod.lhs;
  Rational& modRhs = d_pad.d_mod.rhs;

  Debug("approx::mir")
    << "buildModifiedRow()"
    << " |agg|=" << d_pad.d_agg.lhs.size()
    << " |mod|=" << d_pad.d_mod.lhs.size()
    << " |slacks|=" << d_pad.d_slacks.size()
    << " |vlb|=" << d_pad.d_vub.size()
    << " |vub|=" << d_pad.d_vlb.size() << endl;

  mod.addAll(agg);
  modRhs = aggRhs;
  DenseMap<Rational>::const_iterator iter, iend;
  for(iter = agg.begin(), iend = agg.end(); iter != iend; ++iter){
    ArithVar x = *iter;
    const Rational& c = mod[x];
    if(!d_pad.d_slacks.isKey(x)){
      Debug("approx::mir") << "missed x: " << x << endl;
      return true;
    }
    SlackReplace rep = d_pad.d_slacks[x];
    switch(rep){
    case SlackLB: // skip for now
    case SlackUB:
      break;
    case SlackVLB: /* x[k] = lb[k] * x[kk] + x'[k] */
    case SlackVUB: /* x[k] = ub[k] * x[kk] - x'[k] */
      {
        Assert(!d_vars.isIntegerInput(x));
        bool ub = (rep == SlackVUB);
        const VirtualBound& vb =
          ub ? d_pad.d_vub[x] : d_pad.d_vlb[x];
        Assert(vb.x == x);
        ArithVar y = vb.y;
        Rational prod = c * vb.d;
        if(mod.isKey(y)){
          mod.get(x) += prod;
        }else{
          mod.set(y, prod);
        }
        if(ub){
          mod.set(x, -c);
        }
        Assert(vb.c != NullConstraint);
        d_pad.d_explanation.insert(vb.c);
      }
      break;
    default:
      return true;
    }
  }
  removeZeroes(mod); /* if something cancelled we don't want it in the explanation */
  for(iter = mod.begin(), iend = mod.end(); iter != iend; ++iter){
    ArithVar x = *iter;
    if(!d_pad.d_slacks.isKey(x)){  return true; }

    SlackReplace rep = d_pad.d_slacks[x];
    switch(rep){
    case SlackLB: /* x = lb + x' */
    case SlackUB: /* x = ub - x' */
      {
        bool ub = (rep == SlackUB);
        ConstraintP b = ub ?  d_vars.getUpperBoundConstraint(x):
          d_vars.getLowerBoundConstraint(x);

        Assert(b != NullConstraint);
        Assert(b->getValue().infinitesimalIsZero());
        const Rational& c = mod.get(x);
        modRhs -= c * b->getValue().getNoninfinitesimalPart();
        if(ub){
          mod.set(x, -c);
        }
        d_pad.d_explanation.insert(b);
      }
      break;
    case SlackVLB: /* handled earlier */
    case SlackVUB:
      break;
    default:
      return true;
    }
  }
  removeZeroes(mod);
  return false;
}

bool ApproxGLPK::makeRangeForComplemented(int nid, const MirInfo& mir){
  DenseMap<Rational>& alpha = d_pad.d_alpha.lhs;
  int M = mir.getMAtCreation();
  int N = mir.getN();
  DenseMap<Rational>& compRanges = d_pad.d_compRanges;

  int complemented = 0;

  for(int j = 1; j <= M + N; ++j){
    if(mir.cset[j] != 0){
      complemented++;
      ArithVar x = _getArithVar(nid, M, j);
      if(!alpha.isKey(x)){ return true; }
      if(!d_vars.isIntegerInput(x)){ return true; }
      Assert(d_pad.d_slacks.isKey(x));
      Assert(d_pad.d_slacks[x] == SlackLB || d_pad.d_slacks[x] == SlackUB);

      ConstraintP lb = d_vars.getLowerBoundConstraint(x);
      ConstraintP ub = d_vars.getUpperBoundConstraint(x);

      if(lb == NullConstraint) { return true; }
      if(ub == NullConstraint) { return true; }

      if(!lb->getValue().infinitesimalIsZero()){
        return true;
      }
      if(!ub->getValue().infinitesimalIsZero()){
        return true;
      }

      const Rational& uval = ub->getValue().getNoninfinitesimalPart();
      const Rational& lval = lb->getValue().getNoninfinitesimalPart();

      d_pad.d_explanation.insert(lb);
      d_pad.d_explanation.insert(ub);

      Rational u = uval - lval;
      // u is the same for both rep == LP and rep == UB
      if(compRanges.isKey(x)) { return true; }
      compRanges.set(x,u);
    }
  }

  Debug("approx::mir") <<  "makeRangeForComplemented()" << complemented << endl;
  return false;
}


bool ApproxGLPK::constructMixedKnapsack(){
  const DenseMap<Rational>& mod = d_pad.d_mod.lhs;
  const Rational& modRhs = d_pad.d_mod.rhs;
  DenseMap<Rational>& alpha = d_pad.d_alpha.lhs;
  Rational& beta = d_pad.d_alpha.rhs;

  Assert(alpha.empty());
  beta = modRhs;

  unsigned intVars = 0;
  unsigned remain = 0;
  unsigned dropped = 0;
  DenseMap<Rational>::const_iterator iter, iend;
  for(iter = mod.begin(), iend = mod.end(); iter != iend; ++iter){
    ArithVar v = *iter;
    const Rational& c = mod[v];
    Assert(!c.isZero());
    if(d_vars.isIntegerInput(v)){
      intVars++;
      alpha.set(v, c);
    }else if(c.sgn() < 0){
      remain++;
      alpha.set(v, c);
    }else{
      dropped++;
    }
  }

  Debug("approx::mir")
    << "constructMixedKnapsack() "
    <<" dropped " << dropped
    <<" remain " << remain
    <<" intVars " << intVars
    << endl;
  return intVars == 0; // if this is 0 we have failed
}

bool ApproxGLPK::attemptConstructTableRow(int nid, int M, const PrimitiveVec& vec){
  bool failed = guessCoefficientsConstructTableRow(nid, M, vec);
  if(failed){
    failed = gaussianElimConstructTableRow(nid, M, vec);
  }

  return failed;
}

bool ApproxGLPK::gaussianElimConstructTableRow(int nid, int M, const PrimitiveVec& vec){
  TimerStat::CodeTimer codeTimer(d_stats.d_gaussianElimConstructTime);
  ++d_stats.d_gaussianElimConstruct;

  ArithVar basic = d_pad.d_basic;
  DenseMap<Rational>& tab = d_pad.d_tabRow.lhs;
  tab.purge();
  d_pad.d_tabRow.rhs = Rational(0);
  Assert(basic != ARITHVAR_SENTINEL);
  Assert(tab.empty());
  Assert(d_pad.d_tabRow.rhs.isZero());

  if(d_vars.isAuxiliary(basic)) { return true; }

  if(Debug.isOn("gaussianElimConstructTableRow")){
    Debug("gaussianElimConstructTableRow") << "1 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;
    vec.print(Debug("gaussianElimConstructTableRow"));
    Debug("gaussianElimConstructTableRow") << "match " << basic << "("<<d_vars.asNode(basic)<<")"<<endl;
  }

  set<ArithVar> onrow;
  for(int i = 1; i <= vec.len; ++i){
    int ind = vec.inds[i];
    ArithVar var = _getArithVar(nid, M, ind);
    if(var == ARITHVAR_SENTINEL){
      Debug("gaussianElimConstructTableRow") << "couldn't find" << ind << " " << M << " " << nid << endl;
      return true;
    }
    onrow.insert(var);
  }


  Debug("gaussianElimConstructTableRow") << "2 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;

  Matrix<Rational> A;
  A.increaseSizeTo(d_vars.getNumberOfVariables());
  std::vector< std::pair<RowIndex, ArithVar> > rows;
  set<ArithVar>::const_iterator i, iend;
  // load the rows for auxiliary variables into A
  for(i=onrow.begin(), iend=onrow.end(); i!=iend; ++i){
    ArithVar v = *i;
    if(d_vars.isAuxiliary(v)){
      Assert(d_vars.hasNode(v));

      vector<Rational> coeffs;
      vector<ArithVar> vars;

      coeffs.push_back(Rational(-1));
      vars.push_back(v);

      Node n = d_vars.asNode(v);
      Polynomial p = Polynomial::parsePolynomial(n);
      Polynomial::iterator j = p.begin(), jend=p.end();
      for(j=p.begin(), jend=p.end(); j!=jend; ++j){
        Monomial m = *j;
        if(m.isConstant()) { return true; }
        VarList vl = m.getVarList();
        if(!d_vars.hasArithVar(vl.getNode())){ return true; }
        ArithVar x = d_vars.asArithVar(vl.getNode());
        const Rational& q = m.getConstant().getValue();
        coeffs.push_back(q); vars.push_back(x);
      }
      RowIndex rid = A.addRow(coeffs, vars);
      rows.push_back(make_pair(rid, ARITHVAR_SENTINEL));
    }
  }
  Debug("gaussianElimConstructTableRow") << "3 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;

  for(size_t i=0; i < rows.size(); ++i){
    RowIndex rid = rows[i].first;
    Assert(rows[i].second == ARITHVAR_SENTINEL);

    // substitute previous rows
    for(size_t j=0; j < i; j++){
      RowIndex prevRow = rows[j].first;
      ArithVar other = rows[j].second;
      Assert(other != ARITHVAR_SENTINEL);
      const Matrix<Rational>::Entry& e = A.findEntry(rid, other);
      if(!e.blank()){
        // r_p : 0 = -1 * other + sum a_i x_i
        // rid : 0 =  e * other + sum b_i x_i
        // rid += e * r_p
        //     : 0 = 0 * other + ...
        Assert(!e.getCoefficient().isZero());

        Rational cp = e.getCoefficient();
        Debug("gaussianElimConstructTableRow")
          << "on " << rid << " subst " << cp << "*" << prevRow << " " << other << endl;
        A.rowPlusRowTimesConstant(rid, prevRow, cp);
      }
    }
    if(Debug.isOn("gaussianElimConstructTableRow")){
      A.printMatrix(Debug("gaussianElimConstructTableRow"));
    }

    // solve the row for anything other than non-basics
    bool solveForBasic = (i + 1 == rows.size());
    Rational q;
    ArithVar s = ARITHVAR_SENTINEL;
    Matrix<Rational>::RowIterator k = A.getRow(rid).begin();
    Matrix<Rational>::RowIterator k_end = A.getRow(rid).end();
    for(; k != k_end; ++k){
      const Matrix<Rational>::Entry& e = *k;
      ArithVar colVar = e.getColVar();
      bool selectColVar = false;
      if(colVar == basic){
        selectColVar = solveForBasic;
      }else if(onrow.find(colVar) == onrow.end()) {
        selectColVar = true;
      }
      if(selectColVar){
        s = colVar;
        q = e.getCoefficient();
      }
    }
    if(s == ARITHVAR_SENTINEL || q.isZero()){
      Debug("gaussianElimConstructTableRow") << "3 fail gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;
      return true;
    }else{
      // 0 = q * s + sum c_i * x_i
      Rational mult = -(q.inverse());
      Debug("gaussianElimConstructTableRow") << "selecting " << s << " : " << mult << endl;
      Debug("gaussianElimConstructTableRow") << "selecting " << rid << " " << s << endl;
      //cout << "selecting " << s << " : complexity " << mult.complexity() << " " << mult << endl;
      //cout << "selecting " << rid << " " << s << endl;
      A.multiplyRowByConstant(rid, mult);
      rows[i].second = s;
    }
  }
  Debug("gaussianElimConstructTableRow") << "4 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;

  if(rows.empty()) {
    Debug("gaussianElimConstructTableRow") << "4 fail 1 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;
    return true;
  }
  RowIndex rid_last = rows.back().first;
  ArithVar rid_var = rows.back().second;
  if(rid_var != basic){
    Debug("gaussianElimConstructTableRow") << "4 fail 2 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;
    return true;
  }

  Assert(tab.empty());

  Matrix<Rational>::RowIterator k = A.getRow(rid_last).begin();
  Matrix<Rational>::RowIterator k_end = A.getRow(rid_last).end();
  for(; k != k_end; ++k){
    const Matrix<Rational>::Entry& e = *k;
    tab.set(e.getColVar(), e.getCoefficient());
  }
  Debug("gaussianElimConstructTableRow") << "5 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;
  if(!tab.isKey(basic)){
    Debug("gaussianElimConstructTableRow") << "5 fail 1 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;
    return true;
  }
  if(tab[basic] != Rational(-1)){
    Debug("gaussianElimConstructTableRow") << "5 fail 2 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;
    return true;
  }

  tab.remove(basic);
  Debug("gaussianElimConstructTableRow") << "6 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;

  if(vec.len < 0 ){
    Debug("gaussianElimConstructTableRow") << "6 fail 1 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;
    return true;
  }
  if(tab.size() != ((unsigned)vec.len) ) {
    Debug("gaussianElimConstructTableRow") << "6 fail 2 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<< tab.size() <<  " " << vec.len << endl;
    return true;
  }

  Debug("gaussianElimConstructTableRow") << "7 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;

  for(int i = 1; i <= vec.len; ++i){
    int ind = vec.inds[i];
    double coeff = vec.coeffs[i];
    ArithVar var = _getArithVar(nid, M, ind);
    Assert(var != ARITHVAR_SENTINEL);
    if(!tab.isKey(var)){
      Debug("gaussianElimConstructTableRow") << "7 fail 1 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"<<endl;
      return true;
    }

    double est = tab[var].getDouble();

    if(!ApproximateSimplex::roughlyEqual(coeff, est)){
      Debug("gaussianElimConstructTableRow") << "7 fail 2 gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"
           << " boink on " << ind << " " << var << " " << est <<endl;
      return true;
    }
    Debug("gaussianElimConstructTableRow") << var << " cfe " << coeff << endl;
  }

  Debug("gaussianElimConstructTableRow")
    << "gaussianElimConstructTableRow("<<nid <<", "<< basic<< ")"
    << " superduper" << endl;

  return false;
}
bool ApproxGLPK::guessCoefficientsConstructTableRow(int nid, int M, const PrimitiveVec& vec){
  for(size_t i=0; i < d_denomGuesses.size(); ++i){
    const Integer& D = d_denomGuesses[i];
    if(!guessCoefficientsConstructTableRow(nid, M, vec, D)){
      d_stats.d_averageGuesses.addEntry(i+1);
      Debug("approx::gmi") << "guesseditat " << i << " D=" << D << endl;
      return false;
    }
  }
  return true;
}
bool ApproxGLPK::guessCoefficientsConstructTableRow(int nid, int M, const PrimitiveVec& vec, const Integer& D){
  ArithVar basic = d_pad.d_basic;
  DenseMap<Rational>& tab = d_pad.d_tabRow.lhs;
  tab.purge();
  d_pad.d_tabRow.rhs = Rational(0);
  Assert(basic != ARITHVAR_SENTINEL);
  Assert(tab.empty());
  Assert(d_pad.d_tabRow.rhs.isZero());

  if(Debug.isOn("guessCoefficientsConstructTableRow")){
    Debug("guessCoefficientsConstructTableRow")  << "attemptConstructTableRow("<<nid <<", "<< basic<<",...," << D<< ")"<<endl;
    vec.print(Debug("guessCoefficientsConstructTableRow"));
    Debug("guessCoefficientsConstructTableRow") << "match " << basic << "("<<d_vars.asNode(basic)<<")"<<endl;
  }

  tab.set(basic, Rational(-1));
  for(int i = 1; i <= vec.len; ++i){
    int ind = vec.inds[i];
    double coeff = vec.coeffs[i];
    ArithVar var = _getArithVar(nid, M, ind);
    if(var == ARITHVAR_SENTINEL){
      Debug("guessCoefficientsConstructTableRow") << "couldn't find" << ind << " " << M << " " << nid << endl;
      return true;
    }
    Debug("guessCoefficientsConstructTableRow") << "match " << ind << "," << var << "("<<d_vars.asNode(var)<<")"<<endl;

    Maybe<Rational> cfe = estimateWithCFE(coeff, D);
    if (!cfe)
    {
      return true;
    }
    tab.set(var, cfe.value());
    Debug("guessCoefficientsConstructTableRow") << var << " cfe " << cfe << endl;
  }
  if(!guessIsConstructable(tab)){
    Debug("guessCoefficientsConstructTableRow") << "failed to construct with " << D  << endl;
    return true;
  }
  tab.remove(basic);
  return false;
}

/* Maps an ArithVar to either an upper/lower bound */
bool ApproxGLPK::constructGmiCut(){
  const DenseMap<Rational>& tabRow = d_pad.d_tabRow.lhs;
  const DenseMap<ConstraintP>& toBound = d_pad.d_toBound;
  DenseMap<Rational>& cut = d_pad.d_cut.lhs;
  std::set<ConstraintP>& explanation = d_pad.d_explanation;
  Rational& rhs = d_pad.d_cut.rhs;

  DenseMap<Rational>::const_iterator iter, end;
  Assert(cut.empty());

  // compute beta for a "fake" assignment
  bool anyInf;
  DeltaRational dbeta = sumConstraints(tabRow, toBound, &anyInf);
  const Rational& beta = dbeta.getNoninfinitesimalPart();
  Debug("approx::gmi") << dbeta << endl;
  if(anyInf || beta.isIntegral()){ return true; }

  Rational one = Rational(1);
  Rational fbeta = beta.floor_frac();
  rhs = fbeta;
  Assert(fbeta.sgn() > 0);
  Assert(fbeta < one);
  Rational one_sub_fbeta = one - fbeta;
  for(iter = tabRow.begin(), end = tabRow.end(); iter != end; ++iter){
    ArithVar x = *iter;
    const Rational& psi = tabRow[x];
    ConstraintP c = toBound[x];
    const Rational& bound = c->getValue().getNoninfinitesimalPart();
    if(d_vars.boundsAreEqual(x)){
      // do not add a coefficient
      // implictly substitute the variable w/ its constraint
      std::pair<ConstraintP, ConstraintP> exp = d_vars.explainEqualBounds(x);
      explanation.insert(exp.first);
      if(exp.second != NullConstraint){
        explanation.insert(exp.second);
      }
    }else if(d_vars.isIntegerInput(x) && psi.isIntegral()){
      // do not add a coefficient
      // nothing to explain
      Debug("approx::gmi") << "skipping " << x << endl;
    }else{
      explanation.insert(c);
      Rational phi;
      Rational alpha = (c->isUpperBound() ? psi : -psi);

      // x - ub <= 0 and lb - x <= 0
      if(d_vars.isIntegerInput(x)){
        Assert(!psi.isIntegral());
        // alpha = slack_sgn * psi
        Rational falpha = alpha.floor_frac();
        Assert(falpha.sgn() > 0);
        Assert(falpha < one);
        phi = (falpha <= fbeta) ?
          falpha : ((fbeta / one_sub_fbeta) * (one - falpha));
      }else{
        phi = (alpha >= 0) ?
          alpha : ((fbeta / one_sub_fbeta) * (- alpha));
      }
      Assert(phi.sgn() != 0);
      if(c->isUpperBound()){
        cut.set(x, -phi);
        rhs -= phi * bound;
      }else{
        cut.set(x, phi);
        rhs += phi * bound;
      }
    }
  }
  if(Debug.isOn("approx::gmi")){
    Debug("approx::gmi") << "pre removeSlackVariables";
    d_pad.d_cut.print(Debug("approx::gmi"));
    Debug("approx::gmi") << endl;
  }
  removeAuxillaryVariables(d_vars, cut);

  if(Debug.isOn("approx::gmi")){
    Debug("approx::gmi") << "post removeAuxillaryVariables";
    d_pad.d_cut.print(Debug("approx::gmi"));
    Debug("approx::gmi") << endl;
  }
  removeFixed(d_vars, d_pad.d_cut, explanation);

  if(Debug.isOn("approx::gmi")){
    Debug("approx::gmi") << "post removeFixed";
    d_pad.d_cut.print(Debug("approx::gmi"));
    Debug("approx::gmi") << endl;
  }
  return false;
}

void ApproxGLPK::tryCut(int nid, CutInfo& cut)
{
  Assert(!cut.reconstructed());
  Assert(cut.getKlass() != RowsDeletedKlass);
  bool failure = false;
  switch(cut.getKlass()){
  case GmiCutKlass:
    failure = attemptGmi(nid, static_cast<const GmiInfo&>(cut));
    break;
  case MirCutKlass:
    failure = attemptMir(nid, static_cast<const MirInfo&>(cut));
    break;
  case BranchCutKlass:
    failure = attemptBranchCut(nid, dynamic_cast<const BranchCutInfo&>(cut));
    break;
  default:
    break;
  }
  Assert(failure == d_pad.d_failure);

  if(!failure){
    // move the pad to the cut
    cut.setReconstruction(d_pad.d_cut);

    if(cut.getKlass() != BranchCutKlass){
      std::set<ConstraintP>& exp = d_pad.d_explanation;
      ConstraintCPVec asvec(exp.begin(), exp.end());
      cut.swapExplanation(asvec);
    }
  }else{
    Debug("approx") << "failure " << cut.getKlass() << endl;
  }
}


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
#endif /*#ifdef CVC4_USE_GLPK */
/* End GPLK implementation. */
