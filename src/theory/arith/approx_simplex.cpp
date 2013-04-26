#include "cvc4autoconfig.h"

#include "theory/arith/approx_simplex.h"
#include "theory/arith/normal_form.h"
#include <math.h>
#include <cmath>

using namespace std;

namespace CVC4 {
namespace theory {
namespace arith {

ApproximateSimplex::ApproximateSimplex() :
  d_pivotLimit(std::numeric_limits<int>::max())
{}

void ApproximateSimplex::setPivotLimit(int pivotLimit){
  Assert(pivotLimit >= 0);
  d_pivotLimit = pivotLimit;
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
      //cout << "  cfe["<<i<<"]: " << back << endl;
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

Rational ApproximateSimplex::estimateWithCFE(const Rational& q, int depth){
  std::vector<Integer> cfe = rationalToCfe(q,depth);
  return cfeToRational(cfe);
}

Rational ApproximateSimplex::estimateWithCFE(double d){
  return estimateWithCFE(Rational::fromDouble(d), 10);
}

class ApproxNoOp : public ApproximateSimplex {
public:
  ApproxNoOp(const ArithVariables& vars){}
  ~ApproxNoOp(){}

  virtual ApproxResult solveRelaxation(){
    return ApproxError;
  }
  virtual Solution extractRelaxation() const{
    return Solution();
  }

  virtual ApproxResult solveMIP(){
    return ApproxError;
  }
  virtual Solution extractMIP() const{
    return Solution();
  }

  virtual void setOptCoeffs(const ArithRatPairVec& ref){}
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

/* Begin the declaration of GLPK specific code. */
#ifdef CVC4_USE_GLPK
extern "C" {
#include <glpk.h>
}

namespace CVC4 {
namespace theory {
namespace arith {

class ApproxGLPK : public ApproximateSimplex {
private:
  glp_prob* d_prob;
  const ArithVariables& d_vars;

  DenseMap<int> d_colIndices;
  DenseMap<int> d_rowIndices;


  int d_instanceID;

  bool d_solvedRelaxation;
  bool d_solvedMIP;

public:
  ApproxGLPK(const ArithVariables& vars);
  ~ApproxGLPK();

  virtual ApproxResult solveRelaxation();
  virtual Solution extractRelaxation() const{
    return extractSolution(false);
  }

  virtual ApproxResult solveMIP();
  virtual Solution extractMIP() const{
    return extractSolution(true);
  }
  virtual void setOptCoeffs(const ArithRatPairVec& ref);

private:
  Solution extractSolution(bool mip) const;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
#endif /*#ifdef CVC4_USE_GLPK */
/* End the declaration of GLPK specific code. */

/* Begin GPLK/NOGLPK Glue code. */
namespace CVC4 {
namespace theory {
namespace arith {
ApproximateSimplex* ApproximateSimplex::mkApproximateSimplexSolver(const ArithVariables& vars){
#ifdef CVC4_USE_GLPK
  return new ApproxGLPK(vars);
#else
  return new ApproxNoOp(vars);
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

ApproxGLPK::ApproxGLPK(const ArithVariables& avars) :
  d_vars(avars), d_solvedRelaxation(false), d_solvedMIP(false)
{
  static int instance = 0;
  ++instance;
  d_instanceID = instance;

  d_prob = glp_create_prob();
  glp_set_obj_dir(d_prob, GLP_MAX);
  glp_set_prob_name(d_prob, "ApproximateSimplex::approximateFindModel");

  int numRows = 0;
  int numCols = 0;

  // Assign each variable to a row and column variable as it appears in the input
  for(ArithVariables::var_iterator vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end; ++vi){
    ArithVar v = *vi;

    if(d_vars.isSlack(v)){
      ++numRows;
      d_rowIndices.set(v, numRows);
    }else{
      ++numCols;
      d_colIndices.set(v, numCols);
    }
  }
  glp_add_rows(d_prob, numRows);
  glp_add_cols(d_prob, numCols);

  // Assign the upper/lower bounds and types to each variable
  for(ArithVariables::var_iterator vi = d_vars.var_begin(), vi_end = d_vars.var_end(); vi != vi_end; ++vi){
    ArithVar v = *vi;

    //cout << v  << " ";
    //d_vars.printModel(v, cout);

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

    if(d_vars.isSlack(v)){
      int rowIndex = d_rowIndices[v];
      glp_set_row_bnds(d_prob, rowIndex, type, lb, ub);
    }else{
      int colIndex = d_colIndices[v];
      int kind = d_vars.isInteger(v) ? GLP_IV : GLP_CV;
      glp_set_col_kind(d_prob, colIndex, kind);
      glp_set_col_bnds(d_prob, colIndex, type, lb, ub);
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
  glp_load_matrix(d_prob, numEntries, ia, ja, ar);

  delete[] ia;
  delete[] ja;
  delete[] ar;
}

void ApproxGLPK::setOptCoeffs(const ArithRatPairVec& ref){
  DenseMap<double> nbCoeffs;

  for(ArithRatPairVec::const_iterator i = ref.begin(), iend = ref.end(); i != iend; ++i){
    ArithVar v = (*i).first;
    const Rational& q = (*i).second;

    if(d_vars.isSlack(v)){
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
    glp_set_obj_coef(d_prob, colIndex, coeff);
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

static void printGLPKStatus(int status, std::ostream& out){
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
  glp_delete_prob(d_prob);
}


ApproximateSimplex::Solution ApproxGLPK::extractSolution(bool mip) const{
  Assert(d_solvedRelaxation);
  Assert(!mip  || d_solvedMIP);

  ApproximateSimplex::Solution sol;
  DenseSet& newBasis = sol.newBasis;
  DenseMap<DeltaRational>& newValues = sol.newValues;

  for(ArithVariables::var_iterator i = d_vars.var_begin(), i_end = d_vars.var_end(); i != i_end; ++i){
    ArithVar vi = *i;
    bool isSlack = d_vars.isSlack(vi);
    int glpk_index = isSlack ? d_rowIndices[vi] : d_colIndices[vi];

    int status = isSlack ? glp_get_row_stat(d_prob, glpk_index) : glp_get_col_stat(d_prob, glpk_index);
    //cout << "assignment " << vi << endl;

    switch(status){
    case GLP_BS:
      //cout << "basic" << endl;
      newBasis.add(vi);
      break;
    case GLP_NL:
    case GLP_NS:
      if(!mip){
        //cout << "non-basic lb" << endl;
        newValues.set(vi, d_vars.getLowerBound(vi));
        break;
      }// intentionally fall through otherwise
    case GLP_NU:
      if(!mip){
        // cout << "non-basic ub" << endl;
        newValues.set(vi, d_vars.getUpperBound(vi));
        break;
      }// intentionally fall through otherwise
    default:
      {
        // cout << "non-basic other" << endl;

        double newAssign =
          mip ?
            (isSlack ? glp_mip_row_val(d_prob, glpk_index) :  glp_mip_col_val(d_prob, glpk_index))
          : (isSlack ? glp_get_row_prim(d_prob, glpk_index) :  glp_get_col_prim(d_prob, glpk_index));
        const DeltaRational& oldAssign = d_vars.getAssignment(vi);


        if(d_vars.hasLowerBound(vi) &&
           roughlyEqual(newAssign, d_vars.getLowerBound(vi).approx(SMALL_FIXED_DELTA))){
          //cout << "  to lb" << endl;

          newValues.set(vi, d_vars.getLowerBound(vi));
        }else if(d_vars.hasUpperBound(vi) &&
           roughlyEqual(newAssign, d_vars.getUpperBound(vi).approx(SMALL_FIXED_DELTA))){
          newValues.set(vi, d_vars.getUpperBound(vi));
          // cout << "  to ub" << endl;
        }else{

          double rounded = round(newAssign);
          if(roughlyEqual(newAssign, rounded)){
            // cout << "roughly equal " << rounded << " " << newAssign << " " << oldAssign << endl;
            newAssign = rounded;
          }else{
            // cout << "not roughly equal " << rounded << " " << newAssign << " " << oldAssign << endl;
          }

          DeltaRational proposal = estimateWithCFE(newAssign);


          if(roughlyEqual(newAssign, oldAssign.approx(SMALL_FIXED_DELTA))){
            // cout << "  to prev value" << newAssign << " " << oldAssign << endl;
            proposal = d_vars.getAssignment(vi);
          }


          if(d_vars.strictlyLessThanLowerBound(vi, proposal)){
            //cout << "  round to lb " << d_vars.getLowerBound(vi) << endl;
            proposal = d_vars.getLowerBound(vi);
          }else if(d_vars.strictlyGreaterThanUpperBound(vi, proposal)){
            //cout << "  round to ub " << d_vars.getUpperBound(vi) << endl;
            proposal = d_vars.getUpperBound(vi);
          }else{
            //cout << "  use proposal" << proposal << " " << oldAssign  << endl;
          }
          newValues.set(vi, proposal);
        }
        break;
      }
    }
  }
  return sol;
}

ApproximateSimplex::ApproxResult ApproxGLPK::solveRelaxation(){
  Assert(!d_solvedRelaxation);

  glp_smcp parm;
  glp_init_smcp(&parm);
  parm.presolve = GLP_OFF;
  parm.meth = GLP_PRIMAL;
  parm.pricing = GLP_PT_PSE;
  parm.it_lim = d_pivotLimit;
  //parm.msg_lev = GLP_MSG_ALL;
  parm.msg_lev = GLP_MSG_OFF;

  int res = glp_simplex(d_prob, &parm);
  switch(res){
  case 0:
    {
      int status = glp_get_status(d_prob);
      switch(status){
      case GLP_OPT:
      case GLP_FEAS:
      case GLP_UNBND:
        d_solvedRelaxation = true;
        return ApproxSat;
      case GLP_INFEAS:
      case GLP_NOFEAS:
        d_solvedRelaxation = true;
        return ApproxUnsat;
      default:
        return ApproxError;
      }
    }
  default:
    return ApproxError;
  }
}

void stopAtBingoOrPivotLimit(glp_tree *tree, void *info){
  int pivotLimit = *((int*)info);
  switch(glp_ios_reason(tree)){
  case GLP_IBINGO:
    glp_ios_terminate(tree);
    break;
  default:
    glp_prob* prob = glp_ios_get_prob(tree);
    int iterationcount = lpx_get_int_parm(prob, LPX_K_ITCNT);
    if(iterationcount > pivotLimit){
      glp_ios_terminate(tree);
    }
    break;
  }
}

ApproximateSimplex::ApproxResult ApproxGLPK::solveMIP(){
  Assert(d_solvedRelaxation);
  // Explicitly disable presolving
  // We need the basis thus the presolver must be off!
  // This is default, but this is just being cautious.
  glp_iocp parm;
  glp_init_iocp(&parm);
  parm.presolve = GLP_OFF;
  parm.pp_tech = GLP_PP_NONE;
  parm.fp_heur = GLP_ON;
  parm.gmi_cuts = GLP_ON;
  parm.mir_cuts = GLP_ON;
  parm.cov_cuts = GLP_ON;
  parm.cb_func = stopAtBingoOrPivotLimit;
  parm.cb_info = &d_pivotLimit;
  //parm.msg_lev = GLP_MSG_ALL;
  parm.msg_lev = GLP_MSG_OFF;
  int res = glp_intopt(d_prob, &parm);

  switch(res){
  case 0:
  case GLP_ESTOP:
    {
      int status = glp_mip_status(d_prob);
      switch(status){
      case GLP_OPT:
      case GLP_FEAS:
        d_solvedMIP = true;
        return ApproxSat;
      case GLP_NOFEAS:
        d_solvedMIP = true;
        return ApproxUnsat;
      default:
        return ApproxError;
      }
    }
  default:
    return ApproxError;
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
#endif /*#ifdef CVC4_USE_GLPK */
/* End GPLK implementation. */
