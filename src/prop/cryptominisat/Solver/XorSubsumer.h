/*****************************************************************************
SatELite -- (C) Niklas Een, Niklas Sorensson, 2004
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

Original code by SatELite authors are under an MIT licence.
Modifications for CryptoMiniSat are under GPLv3.
******************************************************************************/

#ifndef XORSIMPLIFIER_H
#define XORSIMPLIFIER_H

#include "Solver.h"
#include "Vec.h"
#include "XSet.h"

namespace CMSat {

class ClauseCleaner;

/**
@brief Handles xor-subsumption and variable elimination at the XOR level

This class achieves three things:

1) it removes variables though XOR-ing of two xors thereby removing their common
variable. If that variable is not used anywere else, the variable is now removed
from the problem

2) It tries to XOR clauses together to get 1-long or 2-long XOR clauses. These
force variables to certain values or replace variables with other variables,
respectively

3) It tries to subsume XOR clauses with other XOR clauses (making 2 XOR clauses
in the process, but one of them is going to be much smaller than it was originally)
*/
class XorSubsumer
{
public:

    XorSubsumer(Solver& S2);
    bool simplifyBySubsumption();
    void unlinkModifiedClause(vec<Lit>& origClause, XorClauseSimp c);
    void unlinkModifiedClauseNoDetachNoNULL(vec<Lit>& origClause, XorClauseSimp c);
    void unlinkClause(XorClauseSimp cc, Var elim = var_Undef);
    XorClauseSimp linkInClause(XorClause& cl);
    void linkInAlreadyClause(XorClauseSimp& c);
    void newVar();
    void extendModel(Solver& solver2);

    uint32_t getNumElimed() const;
    const vec<char>& getVarElimed() const;
    bool unEliminate(const Var var);
    bool checkElimedUnassigned() const;
    double getTotalTime() const;

    struct XorElimedClause
    {
        vector<Lit> lits;
        bool xorEqualFalse;

        void plainPrint(FILE* to = stdout) const
        {
            fprintf(to, "x");
            if (xorEqualFalse) fprintf(to, "-");
            for (size_t i = 0; i < lits.size(); i++) {
                assert(!lits[i].sign());
                fprintf(to, "%d ", lits[i].var() + 1);
            }
            fprintf(to, "0\n");
        }
    };
    const map<Var, vector<XorElimedClause> >& getElimedOutVar() const;

private:

    friend class ClauseCleaner;
    friend class ClauseAllocator;

    //Main
    vec<XorClauseSimp>        clauses;
    vec<vec<XorClauseSimp> >  occur;          // 'occur[index(lit)]' is a list of constraints containing 'lit'.
    Solver&                   solver;         // The Solver

    // Temporaries (to reduce allocation overhead):
    //
    vec<char>                 seen_tmp;       // (used in various places)

    //Start-up
    void addFromSolver(vec<XorClause*>& cs);
    void addBackToSolver();

    // Subsumption:
    void findSubsumed(XorClause& ps, vec<XorClauseSimp>& out_subsumed);
    bool isSubsumed(XorClause& ps);
    void subsume0(XorClauseSimp ps);
    template<class T1, class T2>
    bool subset(const T1& A, const T2& B);
    bool subsetAbst(uint32_t A, uint32_t B);
    template<class T>
    void findUnMatched(const T& A, const T& B, vec<Lit>& unmatchedPart);

    //helper
    void testAllClauseAttach() const;

    //dependent removal
    bool removeDependent();
    void fillCannotEliminate();
    vec<char> cannot_eliminate;
    void addToCannotEliminate(Clause* it);
    void removeWrong(vec<Clause*>& cs);
    void removeWrongBins();
    void removeAssignedVarsFromEliminated();

    //Global stats
    double totalTime;
    map<Var, vector<XorElimedClause> > elimedOutVar;
    vec<char> var_elimed;
    uint32_t numElimed;

    //Heule-process
    template<class T>
    void xorTwoClauses(const T& c1, const T& c2, vec<Lit>& xored);
    bool localSubstitute();
    uint32_t localSubstituteUseful;

    uint32_t clauses_subsumed;
    uint32_t clauses_cut;
    uint32_t origNClauses;
    uint32_t clauseID;
};

inline bool XorSubsumer::subsetAbst(uint32_t A, uint32_t B)
{
    return !(A & ~B);
}

// Assumes 'seen' is cleared (will leave it cleared)
template<class T1, class T2>
bool XorSubsumer::subset(const T1& A, const T2& B)
{
    for (uint32_t i = 0; i != B.size(); i++)
        seen_tmp[B[i].var()] = 1;
    for (uint32_t i = 0; i != A.size(); i++) {
        if (!seen_tmp[A[i].var()]) {
            for (uint32_t i = 0; i != B.size(); i++)
                seen_tmp[B[i].var()] = 0;
            return false;
        }
    }
    for (uint32_t i = 0; i != B.size(); i++)
        seen_tmp[B[i].var()] = 0;
    return true;
}

inline void XorSubsumer::newVar()
{
    occur       .push();
    seen_tmp    .push(0);
    cannot_eliminate.push(0);
    var_elimed.push(0);
}

inline const vec<char>& XorSubsumer::getVarElimed() const
{
    return var_elimed;
}

inline uint32_t XorSubsumer::getNumElimed() const
{
    return numElimed;
}

inline double XorSubsumer::getTotalTime() const
{
    return totalTime;
}

inline const map<Var, vector<XorSubsumer::XorElimedClause> >& XorSubsumer::getElimedOutVar() const
{
    return elimedOutVar;
}

}

#endif //XORSIMPLIFIER_H
