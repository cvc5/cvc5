/***********************************************************************************
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
**************************************************************************************************/

#include "MatrixFinder.h"

#include "Solver.h"
#include "Gaussian.h"
#include "GaussianConfig.h"
#include "ClauseCleaner.h"
#include "time_mem.h"

#include <set>
#include <map>
#include <iomanip>
#include <math.h>

//#define VERBOSE_DEBUG
//#define PART_FINDING

using namespace CMSat;

using std::set;
using std::map;

MatrixFinder::MatrixFinder(Solver& _solver) :
    solver(_solver)
{
}

inline Var MatrixFinder::fingerprint(const XorClause& c) const
{
    Var fingerprint = 0;

    for (const Lit* a = &c[0], *end = a + c.size(); a != end; a++)
        fingerprint |= a->var();

    return fingerprint;
}

inline bool MatrixFinder::firstPartOfSecond(const XorClause& c1, const XorClause& c2) const
{
    uint32_t i1, i2;
    for (i1 = 0, i2 = 0; i1 < c1.size() && i2 < c2.size();) {
        if (c1[i1].var() != c2[i2].var())
            i2++;
        else {
            i1++;
            i2++;
        }
    }

    return (i1 == c1.size());
}

bool MatrixFinder::findMatrixes()
{
    assert(solver.decisionLevel() == 0);
    assert(solver.ok);

    table.clear();
    table.resize(solver.nVars(), var_Undef);
    reverseTable.clear();
    matrix_no = 0;
    double myTime = cpuTime();

    if (solver.xorclauses.size() < MIN_GAUSS_XOR_CLAUSES ||
        solver.gaussconfig.decision_until <= 0 ||
        solver.xorclauses.size() > MAX_GAUSS_XOR_CLAUSES
        ) {
        return true;
    }

    solver.clauseCleaner->cleanClauses(solver.xorclauses, ClauseCleaner::xorclauses);
    if (!solver.ok) return false;

    if (solver.gaussconfig.noMatrixFind) {
        if (solver.conf.verbosity >=1)
            std::cout << "c Matrix finding disabled through switch. Putting all xors into matrix." << std::endl;
        vector<XorClause*> xorclauses;
        xorclauses.reserve(solver.xorclauses.size());
        for (uint32_t i = 0; i < solver.xorclauses.size(); i++)
            xorclauses.push_back(solver.xorclauses[i]);
        solver.gauss_matrixes.push_back(new Gaussian(solver, solver.gaussconfig, 0, xorclauses));
        return true;
    }

    for (XorClause** c = solver.xorclauses.getData(), **end = c + solver.xorclauses.size(); c != end; c++) {
        set<uint32_t> tomerge;
        vector<Var> newSet;
        for (Lit *l = &(**c)[0], *end2 = l + (**c).size(); l != end2; l++) {
            if (table[l->var()] != var_Undef)
                tomerge.insert(table[l->var()]);
            else
                newSet.push_back(l->var());
        }
        if (tomerge.size() == 1) {
            const uint32_t into = *tomerge.begin();
            map<uint32_t, vector<Var> >::iterator intoReverse = reverseTable.find(into);
            for (uint32_t i = 0; i < newSet.size(); i++) {
                intoReverse->second.push_back(newSet[i]);
                table[newSet[i]] = into;
            }
            continue;
        }

        for (set<uint32_t>::iterator it = tomerge.begin(); it != tomerge.end(); it++) {
            newSet.insert(newSet.end(), reverseTable[*it].begin(), reverseTable[*it].end());
            reverseTable.erase(*it);
        }
        for (uint32_t i = 0; i < newSet.size(); i++)
            table[newSet[i]] = matrix_no;
        reverseTable[matrix_no] = newSet;
        matrix_no++;
    }

    #ifdef VERBOSE_DEBUG
    for (map<uint32_t, vector<Var> >::iterator it = reverseTable.begin(), end = reverseTable.end(); it != end; it++) {
        std::cout << "-- set begin --" << std::endl;
        for (vector<Var>::iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
            std::cout << *it2 << ", ";
        }
        std::cout << "-------" << std::endl;
    }
    #endif

    uint32_t numMatrixes = setMatrixes();

    if (solver.conf.verbosity >=1)
        std::cout << "c Finding matrixes :    " << cpuTime() - myTime
        << " s (found  " << numMatrixes << ")"
        << std::endl;

    for (vector<Gaussian*>::iterator gauss = solver.gauss_matrixes.begin(), end = solver.gauss_matrixes.end(); gauss != end; gauss++) {
        if (!(*gauss)->full_init()) return false;
    }

    return true;
}

uint32_t MatrixFinder::setMatrixes()
{
    vector<pair<uint32_t, uint32_t> > numXorInMatrix;
    for (uint32_t i = 0; i < matrix_no; i++)
        numXorInMatrix.push_back(std::make_pair(i, 0));

    vector<uint32_t> sumXorSizeInMatrix(matrix_no, 0);
    vector<vector<uint32_t> > xorSizesInMatrix(matrix_no);
    vector<vector<XorClause*> > xorsInMatrix(matrix_no);

    #ifdef PART_FINDING
    vector<vector<Var> > xorFingerprintInMatrix(matrix_no);
    #endif

    for (XorClause** c = solver.xorclauses.getData(), **end = c + solver.xorclauses.size(); c != end; c++) {
        XorClause& x = **c;
        const uint32_t matrix = table[x[0].var()];
        assert(matrix < matrix_no);

        //for stats
        numXorInMatrix[matrix].second++;
        sumXorSizeInMatrix[matrix] += x.size();
        xorSizesInMatrix[matrix].push_back(x.size());
        xorsInMatrix[matrix].push_back(&x);

        #ifdef PART_FINDING
        xorFingerprintInMatrix[matrix].push_back(fingerprint(x));
        #endif //PART_FINDING
    }

    std::sort(numXorInMatrix.begin(), numXorInMatrix.end(), mysorter());

    #ifdef PART_FINDING
    for (uint32_t i = 0; i < matrix_no; i++)
        findParts(xorFingerprintInMatrix[i], xorsInMatrix[i]);
    #endif //PART_FINDING

    uint32_t realMatrixNum = 0;
    for (int a = matrix_no-1; a != -1; a--) {
        uint32_t i = numXorInMatrix[a].first;

        if (numXorInMatrix[a].second < 3)
            continue;

        const uint32_t totalSize = reverseTable[i].size()*numXorInMatrix[a].second;
        const double density = (double)sumXorSizeInMatrix[i]/(double)totalSize*100.0;
        double avg = (double)sumXorSizeInMatrix[i]/(double)numXorInMatrix[a].second;
        double variance = 0.0;
        for (uint32_t i2 = 0; i2 < xorSizesInMatrix[i].size(); i2++)
            variance += pow((double)xorSizesInMatrix[i][i2]-avg, 2);
        variance /= (double)xorSizesInMatrix.size();
        const double stdDeviation = sqrt(variance);

        if (numXorInMatrix[a].second >= solver.gaussconfig.minMatrixRows
            && numXorInMatrix[a].second <= solver.gaussconfig.maxMatrixRows
            && realMatrixNum <= solver.gaussconfig.maxNumMatrixes)
        {
            if (solver.conf.verbosity >=1)
                std::cout << "c Matrix no " << std::setw(2) << realMatrixNum;
            solver.gauss_matrixes.push_back(new Gaussian(solver, solver.gaussconfig, realMatrixNum, xorsInMatrix[i]));
            realMatrixNum++;

        } else {
            if (solver.conf.verbosity >=1  /*&& numXorInMatrix[a].second >= 20*/)
                std::cout << "c Unused Matrix ";
        }
        if (solver.conf.verbosity >=1 /*&& numXorInMatrix[a].second >= 20*/) {
            std::cout << std::setw(7) << numXorInMatrix[a].second << " x" << std::setw(5) << reverseTable[i].size();
            std::cout << "  density:" << std::setw(5) << std::fixed << std::setprecision(1) << density << "%";
            std::cout << "  xorlen avg:" << std::setw(5) << std::fixed << std::setprecision(2)  << avg;
            std::cout << " stdev:" << std::setw(6) << std::fixed << std::setprecision(2) << stdDeviation << std::endl;
        }
    }

    return realMatrixNum;
}

void MatrixFinder::findParts(vector<Var>& xorFingerprintInMatrix, vector<XorClause*>& xorsInMatrix)
{
    uint32_t ai = 0;
    for (XorClause **a = &xorsInMatrix[0], **end = a + xorsInMatrix.size(); a != end; a++, ai++) {
        const Var fingerprint = xorFingerprintInMatrix[ai];
        uint32_t ai2 = 0;
        for (XorClause **a2 = &xorsInMatrix[0]; a2 != end; a2++, ai2++) {
            if (ai == ai2) continue;
            const Var fingerprint2 = xorFingerprintInMatrix[ai2];
            if (((fingerprint & fingerprint2) == fingerprint) && firstPartOfSecond(**a, **a2)) {
                std::cout << "First part of second:" << std::endl;
                (*a)->plainPrint();
                (*a2)->plainPrint();
                std::cout << "END" << std::endl;
            }
        }
    }
}
