/*****************************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
******************************************************************************/

#ifndef SOLVERCONF_H
#define SOLVERCONF_H

#include "SolverTypes.h"
#include "constants.h"

namespace CMSat {

class SolverConf
{
    public:
        SolverConf();

        double    random_var_freq;    ///<The frequency with which the decision heuristic tries to choose a random variable.        (default 0.02) NOTE: This is really strange. If the number of variables set is large, then the random chance is in fact _far_ lower than this value. This is because the algorithm tries to set one variable randomly, but if that variable is already set, then it _silently_ fails, and moves on (doing non-random flip)!
        double    clause_decay;       ///<Inverse of the clause activity decay factor. Only applies if using MiniSat-style clause activities  (default: 1 / 0.999)
        int       restart_first;      ///<The initial restart limit.                                                                (default 100)
        double    restart_inc;        ///<The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
        double    learntsize_factor;  ///<The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
        double    learntsize_inc;     ///<The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)
        bool      expensive_ccmin;    ///<Should clause minimisation by Sorensson&Biere be used?                                    (default TRUE)
        int       polarity_mode;      ///<Controls which polarity the decision heuristic chooses. Auto means Jeroslow-Wang          (default: polarity_auto)
        int       verbosity;          ///<Verbosity level. 0=silent, 1=some progress report, 2=lots of report, 3 = all report       (default 2)
        Var       restrictPickBranch; ///<Pick variables to branch on preferentally from the highest [0, restrictedPickBranch]. If set to 0, preferentiality is turned off (i.e. picked randomly between [0, all])
        uint32_t simpBurstSConf;
        double simpStartMult;
        double simpStartMMult;
        bool doPerformPreSimp;
        double failedLitMultiplier;

        //Optimisations to do
        bool      doFindXors;         ///<Automatically find non-binary xor clauses and convert them to xor clauses
        bool      doFindEqLits;       ///<Automatically find binary xor clauses (i.e. variable equi- and antivalences)
        bool      doRegFindEqLits;    ///<Regularly find binary xor clauses (i.e. variable equi- and antivalences)
        bool      doReplace;          ///<Should var-replacing be performed? If set to FALSE, equi- and antivalent variables will not be replaced with one another. NOTE: This precludes using a lot of the algorithms!
        bool      doConglXors;        ///<Do variable elimination at the XOR-level (xor-ing 2 xor clauses thereby removing a variable)
        bool      doHeuleProcess;     ///<Perform local subsitutuion as per Heule's theis
        bool      doSchedSimp;        ///<Should simplifyProblem() be scheduled regularly? (if set to FALSE, a lot of opmitisations are disabled)
        bool      doSatELite;         ///<Should try to subsume & self-subsuming resolve & variable-eliminate & block-clause eliminate?
        bool      doXorSubsumption;   ///<Should try to subsume & local-subsitute xor clauses
        bool      doHyperBinRes;      ///<Should try carry out hyper-binary resolution
        bool      doBlockedClause;    ///<Should try to remove blocked clauses
        bool      doVarElim;          ///<Perform variable elimination
        bool      doSubsume1;         ///<Perform self-subsuming resolution
        bool      doClausVivif;      ///<Perform asymmetric branching at the beginning of the solving
        bool      doSortWatched;      ///<Sort watchlists according to size&type: binary, tertiary, normal (>3-long), xor clauses
        bool      doMinimLearntMore;  ///<Perform learnt-clause minimisation using watchists' binary and tertiary clauses? ("strong minimization" in PrecoSat)
        bool      doMinimLMoreRecur;  ///<Always perform recursive/transitive on-the-fly self self-subsuming resolution --> an enhancement of "strong minimization" of PrecoSat
        bool      doFailedLit;        ///<Carry out Failed literal probing + doubly propagated literal detection + 2-long xor clause detection during failed literal probing + hyper-binary resoolution
        bool      doRemUselessBins;   ///<Should try to remove useless binary clauses at the beginning of solving?
        bool      doSubsWBins;
        bool      doSubsWNonExistBins;  ///<Try to do subsumption and self-subsuming resolution with non-existent binary clauses (i.e. binary clauses that don't exist but COULD exists)
        bool      doRemUselessLBins; ///<Try to remove useless learnt binary clauses
        #ifdef ENABLE_UNWIND_GLUE
        bool      doMaxGlueDel;
        #endif //ENABLE_UNWIND_GLUE
        bool      doPrintAvgBranch;
        bool      doCacheOTFSSR;
        bool      doCacheOTFSSRSet;
        bool      doExtendedSCC;
        bool      doCalcReach; ///<Calculate reachability, and influence variable decisions with that
        bool      doBXor;
        bool      doOTFSubsume; ///On-the-fly subsumption
        uint64_t  maxConfl;
        bool      isPlain; ///<We are in 'plain' mode: glues can never be 1

        //interrupting & dumping
        uint32_t  maxRestarts;
        bool      needToDumpLearnts;  ///<If set to TRUE, learnt clauses will be dumped to the file speified by "learntsFilename"
        bool      needToDumpOrig;     ///<If set to TRUE, a simplified version of the original clause-set will be dumped to the file speified by "origFilename". The solution to this file should perfectly satisfy the problem
        std::string learntsFilename;    ///<Dump sorted learnt clauses to this file. Only active if "needToDumpLearnts" is set to TRUE
        std::string origFilename;       ///<Dump simplified original problem CNF to this file. Only active if "needToDumpOrig" is set to TRUE
        uint32_t  maxDumpLearntsSize; ///<When dumping the learnt clauses, this is the maximum clause size that should be dumped
        bool      libraryUsage;       ///<Set to true if not used as a library. In fact, this is TRUE by default, and Main.cpp sets it to "FALSE". Disables some simplifications at the beginning of solving (mostly performStepsBeforeSolve() )
        bool      greedyUnbound;      ///<If set, then variables will be greedily unbounded (set to l_Undef). This is EXPERIMENTAL
        #ifdef ENABLE_UNWIND_GLUE
        uint32_t  maxGlue;            ///< Learnt clauses (when doing dynamic restarts) with glue above this value will be removed immediately on backtracking
        #endif //ENABLE_UNWIND_GLUE
        RestartType fixRestartType;   ///<If set, the solver will always choose the given restart strategy instead of automatically trying to guess a strategy. Note that even if set to dynamic_restart, there will be a few restarts made statically after each full restart.

        uint32_t origSeed;
};

}

#endif //SOLVERCONF_H
