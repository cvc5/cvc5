/***************************************************************************
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
****************************************************************************/

#include "Solver.h"
#include "VarReplacer.h"
#include "Subsumer.h"
#include "XorSubsumer.h"
#include "time_mem.h"
#include "DimacsParser.h"
#include "FailedLitSearcher.h"
#include "DataSync.h"
#include "SCCFinder.h"
#include <iomanip>
#include <omp.h>

#ifdef USE_GAUSS
#include "Gaussian.h"
#endif

#ifndef _MSC_VER
#include <sys/time.h>
#include <sys/resource.h>
#endif

using namespace CMSat;

static const int space = 10;

bool Solver::dumpSortedLearnts(const std::string& fileName, const uint32_t maxSize)
{
    FILE* outfile = fopen(fileName.c_str(), "w");
    if (!outfile)
        return false;

    fprintf(outfile, "c \nc ---------\n");
    fprintf(outfile, "c unitaries\n");
    fprintf(outfile, "c ---------\n");
    for (uint32_t i = 0, end = (trail_lim.size() > 0) ? trail_lim[0] : trail.size() ; i < end; i++) {
        trail[i].printFull(outfile);
    }

    fprintf(outfile, "c conflicts %lu\n", (unsigned long)conflicts);
    if (maxSize == 1) goto end;

    fprintf(outfile, "c \nc ---------------------------------\n");
    fprintf(outfile, "c learnt binary clauses (extracted from watchlists)\n");
    fprintf(outfile, "c ---------------------------------\n");
    dumpBinClauses(true, false, outfile);

    fprintf(outfile, "c \nc ---------------------------------------\n");
    fprintf(outfile, "c clauses representing 2-long XOR clauses\n");
    fprintf(outfile, "c ---------------------------------------\n");
    {
        const vector<Lit>& table = varReplacer->getReplaceTable();
        for (Var var = 0; var != table.size(); var++) {
            Lit lit = table[var];
            if (lit.var() == var)
                continue;

            fprintf(outfile, "%s%d %d 0\n", (!lit.sign() ? "-" : ""), lit.var()+1, var+1);
            fprintf(outfile, "%s%d -%d 0\n", (lit.sign() ? "-" : ""), lit.var()+1, var+1);
        }
    }
    fprintf(outfile, "c \nc --------------------\n");
    fprintf(outfile, "c clauses from learnts\n");
    fprintf(outfile, "c --------------------\n");
    if (lastSelectedRestartType == dynamic_restart)
        std::sort(learnts.getData(), learnts.getData()+learnts.size(), reduceDB_ltGlucose());
    else
        std::sort(learnts.getData(), learnts.getData()+learnts.size(), reduceDB_ltMiniSat());
    for (int i = learnts.size()-1; i >= 0 ; i--) {
        if (learnts[i]->size() <= maxSize) {
            learnts[i]->print(outfile);
        }
    }

    end:

    fclose(outfile);
    return true;
}

void Solver::printStrangeBinLit(const Lit lit) const
{
    const vec<Watched>& ws = watches[(~lit).toInt()];
    for (vec<Watched>::const_iterator it2 = ws.getData(), end2 = ws.getDataEnd(); it2 != end2; it2++) {
        if (it2->isBinary()) {
            std::cout << "bin: " << lit << " , " << it2->getOtherLit() << " learnt : " <<  (it2->getLearnt()) << std::endl;
        } else if (it2->isTriClause()) {
            std::cout << "tri: " << lit << " , " << it2->getOtherLit() << " , " <<  (it2->getOtherLit2()) << std::endl;
        } else if (it2->isClause()) {
            std::cout << "cla:" << it2->getNormOffset() << std::endl;
        } else {
            assert(it2->isXorClause());
            std::cout << "xor:" << it2->getXorOffset() << std::endl;
        }
    }
}

uint32_t Solver::countNumBinClauses(const bool alsoLearnt, const bool alsoNonLearnt) const
{
    uint32_t num = 0;

    uint32_t wsLit = 0;
    for (const vec<Watched> *it = watches.getData(), *end = watches.getDataEnd(); it != end; it++, wsLit++) {
        const vec<Watched>& ws = *it;
        for (vec<Watched>::const_iterator it2 = ws.getData(), end2 = ws.getDataEnd(); it2 != end2; it2++) {
            if (it2->isBinary()) {
                if (it2->getLearnt()) num += alsoLearnt;
                else num+= alsoNonLearnt;
            }
        }
    }

    assert(num % 2 == 0);
    return num/2;
}

void Solver::dumpBinClauses(const bool alsoLearnt, const bool alsoNonLearnt, FILE* outfile) const
{
    uint32_t wsLit = 0;
    for (const vec<Watched> *it = watches.getData(), *end = watches.getDataEnd(); it != end; it++, wsLit++) {
        Lit lit = ~Lit::toLit(wsLit);
        const vec<Watched>& ws = *it;
        for (vec<Watched>::const_iterator it2 = ws.getData(), end2 = ws.getDataEnd(); it2 != end2; it2++) {
            if (it2->isBinary() && lit.toInt() < it2->getOtherLit().toInt()) {
                bool toDump = false;
                if (it2->getLearnt() && alsoLearnt) toDump = true;
                if (!it2->getLearnt() && alsoNonLearnt) toDump = true;

                if (toDump) it2->dump(outfile, lit);
            }
        }
    }
}

uint32_t Solver::getBinWatchSize(const bool alsoLearnt, const Lit lit)
{
    uint32_t num = 0;
    const vec<Watched>& ws = watches[lit.toInt()];
    for (vec<Watched>::const_iterator it2 = ws.getData(), end2 = ws.getDataEnd(); it2 != end2; it2++) {
        if (it2->isBinary() && (alsoLearnt || !it2->getLearnt())) {
            num++;
        }
    }

    return num;
}

void Solver::printBinClause(const Lit litP1, const Lit litP2, FILE* outfile) const
{
    if (value(litP1) == l_True) {
        litP1.printFull(outfile);
    } else if (value(litP1) == l_False) {
        litP2.printFull(outfile);
    } else if (value(litP2) == l_True) {
        litP2.printFull(outfile);
    } else if (value(litP2) == l_False) {
        litP1.printFull(outfile);
    } else {
        litP1.print(outfile);
        litP2.printFull(outfile);
    }
}

bool Solver::dumpOrigClauses(const std::string& fileName) const
{
    FILE* outfile;
    if (fileName != std::string("stdout")) {
        outfile = fopen(fileName.c_str(), "w");
        if (!outfile)
            return false;
    } else  {
        outfile = stdout;
    }

    uint32_t numClauses = 0;
    //unitary clauses
    for (uint32_t i = 0, end = (trail_lim.size() > 0) ? trail_lim[0] : trail.size() ; i < end; i++)
        numClauses++;

    //binary XOR clauses
    const vector<Lit>& table = varReplacer->getReplaceTable();
    for (Var var = 0; var != table.size(); var++) {
        Lit lit = table[var];
        if (lit.var() == var)
            continue;
        numClauses += 2;
    }

    //binary normal clauses
    numClauses += countNumBinClauses(false, true);

    //normal clauses
    numClauses += clauses.size();

    //xor clauses
    numClauses += xorclauses.size();

    //previously eliminated clauses
    const map<Var, vector<vector<Lit> > >& elimedOutVar = subsumer->getElimedOutVar();
    for (map<Var, vector<vector<Lit> > >::const_iterator it = elimedOutVar.begin(); it != elimedOutVar.end(); it++) {
        const vector<vector<Lit> >& cs = it->second;
        numClauses += cs.size();
    }
    const map<Var, vector<std::pair<Lit, Lit> > >& elimedOutVarBin = subsumer->getElimedOutVarBin();
    for (map<Var, vector<std::pair<Lit, Lit> > >::const_iterator it = elimedOutVarBin.begin(); it != elimedOutVarBin.end(); it++) {
        numClauses += it->second.size();
    }

    const map<Var, vector<XorSubsumer::XorElimedClause> >& xorElimedOutVar = xorSubsumer->getElimedOutVar();
    for (map<Var, vector<XorSubsumer::XorElimedClause> >::const_iterator it = xorElimedOutVar.begin(); it != xorElimedOutVar.end(); it++) {
        const vector<XorSubsumer::XorElimedClause>& cs = it->second;
        numClauses += cs.size();
    }

    fprintf(outfile, "p cnf %d %d\n", nVars(), numClauses);

    ////////////////////////////////////////////////////////////////////

    fprintf(outfile, "c \nc ---------\n");
    fprintf(outfile, "c unitaries\n");
    fprintf(outfile, "c ---------\n");
    for (uint32_t i = 0, end = (trail_lim.size() > 0) ? trail_lim[0] : trail.size() ; i < end; i++) {
        trail[i].printFull(outfile);
    }

    fprintf(outfile, "c \nc ---------------------------------------\n");
    fprintf(outfile, "c clauses representing 2-long XOR clauses\n");
    fprintf(outfile, "c ---------------------------------------\n");
    for (Var var = 0; var != table.size(); var++) {
        Lit lit = table[var];
        if (lit.var() == var)
            continue;

        Lit litP1 = ~lit;
        Lit litP2 = Lit(var, false);
        printBinClause(litP1, litP2, outfile);
        printBinClause(~litP1, ~litP2, outfile);
    }

    fprintf(outfile, "c \nc ------------\n");
    fprintf(outfile, "c binary clauses\n");
    fprintf(outfile, "c ---------------\n");
    dumpBinClauses(false, true, outfile);

    fprintf(outfile, "c \nc ------------\n");
    fprintf(outfile, "c normal clauses\n");
    fprintf(outfile, "c ---------------\n");
    for (Clause *const *i = clauses.getData(); i != clauses.getDataEnd(); i++) {
        assert(!(*i)->learnt());
        (*i)->print(outfile);
    }

    fprintf(outfile, "c \nc ------------\n");
    fprintf(outfile, "c xor clauses\n");
    fprintf(outfile, "c ---------------\n");
    for (XorClause *const *i = xorclauses.getData(); i != xorclauses.getDataEnd(); i++) {
        assert(!(*i)->learnt());
        (*i)->print(outfile);
    }

    fprintf(outfile, "c -------------------------------\n");
    fprintf(outfile, "c previously eliminated variables\n");
    fprintf(outfile, "c -------------------------------\n");
    for (map<Var, vector<vector<Lit> > >::const_iterator it = elimedOutVar.begin(); it != elimedOutVar.end(); it++) {
        fprintf(outfile, "c ########### cls for eliminated var %d ### start\n", it->first + 1);
        const vector<vector<Lit> >& cs = it->second;
        for (vector<vector<Lit> >::const_iterator it2 = cs.begin(); it2 != cs.end(); it2++) {
            printClause(outfile, *it2);
        }
        fprintf(outfile, "c ########### cls for eliminated var %d ### finish\n", it->first + 1);
    }
    for (map<Var, vector<std::pair<Lit, Lit> > >::const_iterator it = elimedOutVarBin.begin(); it != elimedOutVarBin.end(); it++) {
        for (uint32_t i = 0; i < it->second.size(); i++) {
            it->second[i].first.print(outfile);
            it->second[i].second.printFull(outfile);
        }
    }

    fprintf(outfile, "c -------------------------------\n");
    fprintf(outfile, "c previously xor-eliminated variables\n");
    fprintf(outfile, "c -------------------------------\n");
    for (map<Var, vector<XorSubsumer::XorElimedClause> >::const_iterator it = xorElimedOutVar.begin(); it != xorElimedOutVar.end(); it++) {
        for (vector<XorSubsumer::XorElimedClause>::const_iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
            it2->plainPrint(outfile);
        }
    }

    if (fileName != "stdout") fclose(outfile);
    return true;
}

vector<Lit> Solver::get_unitary_learnts() const
{
    vector<Lit> unitaries;
    if (decisionLevel() > 0) {
        for (uint32_t i = 0; i != trail_lim[0]; i++) {
            unitaries.push_back(trail[i]);
        }
    }

    return unitaries;
}

const vec<Clause*>& Solver::get_learnts() const
{
    return learnts;
}

const vec<Clause*>& Solver::get_sorted_learnts()
{
    if (lastSelectedRestartType == dynamic_restart)
        std::sort(learnts.getData(), learnts.getData()+learnts.size(), reduceDB_ltGlucose());
    else
        std::sort(learnts.getData(), learnts.getData()+learnts.size(), reduceDB_ltMiniSat());
    return learnts;
}

uint32_t Solver::getNumElimSubsume() const
{
    return subsumer->getNumElimed();
}

uint32_t Solver::getNumElimXorSubsume() const
{
    return xorSubsumer->getNumElimed();
}

uint32_t Solver::getNumXorTrees() const
{
    return varReplacer->getNumTrees();
}

uint32_t Solver::getNumXorTreesCrownSize() const
{
    return varReplacer->getNumReplacedVars();
}

double Solver::getTotalTimeSubsumer() const
{
    return subsumer->getTotalTime();
}

double Solver::getTotalTimeFailedLitSearcher() const
{
    return failedLitSearcher->getTotalTime();
}

double Solver::getTotalTimeXorSubsumer() const
{
    return xorSubsumer->getTotalTime();
}

double Solver::getTotalTimeSCC() const
{
    return  sCCFinder->getTotalTime();
}

void Solver::printStatHeader() const
{
    if (conf.verbosity >= 2) {
        std::cout << "c "
        << "========================================================================================="
        << std::endl;
        std::cout << "c"
        << " types(t): F = full restart, N = normal restart" << std::endl;
        std::cout << "c"
        << " types(t): S = simplification begin/end, E = solution found" << std::endl;
        std::cout << "c"
        << " restart types(rt): st = static, dy = dynamic" << std::endl;

        std::cout << "c "
        << std::setw(2) << "t"
        << std::setw(3) << "rt"
        << std::setw(6) << "Rest"
        << std::setw(space) << "Confl"
        << std::setw(space) << "Vars"
        << std::setw(space) << "NormCls"
        << std::setw(space) << "XorCls"
        << std::setw(space) << "BinCls"
        << std::setw(space) << "Learnts"
        << std::setw(space) << "ClLits"
        << std::setw(space) << "LtLits"
        << std::setw(space) << "LGlueHist"
        << std::setw(space) << "SGlueHist"
        << std::endl;
    }
}

void Solver::printRestartStat(const char* type)
{
    if (conf.verbosity >= 2) {
        //printf("c | %9d | %7d %8d %8d | %8d %8d %6.0f |", (int)conflicts, (int)order_heap.size(), (int)(nClauses()-nbBin), (int)clauses_literals, (int)(nbclausesbeforereduce*curRestart+nbCompensateSubsumer), (int)(nLearnts()+nbBin), (double)learnts_literals/(double)(nLearnts()+nbBin));

        std::cout << "c "
        << std::setw(2) << type
        << std::setw(3) << ((restartType == static_restart) ? "st" : "dy")
        << std::setw(6) << starts
        << std::setw(space) << conflicts
        << std::setw(space) << order_heap.size()
        << std::setw(space) << clauses.size()
        << std::setw(space) << xorclauses.size()
        << std::setw(space) << numBins
        << std::setw(space) << learnts.size()
        << std::setw(space) << clauses_literals
        << std::setw(space) << learnts_literals;

        if (glueHistory.getTotalNumeElems() > 0) {
            std::cout << std::setw(space) << std::fixed << std::setprecision(2) << glueHistory.getAvgAllDouble();
        } else {
            std::cout << std::setw(space) << "no data";
        }
        if (glueHistory.isvalid()) {
            std::cout << std::setw(space) << std::fixed << std::setprecision(2) << glueHistory.getAvgDouble();
        } else {
            std::cout << std::setw(space) << "no data";
        }

        #ifdef RANDOM_LOOKAROUND_SEARCHSPACE
        if (conf.doPrintAvgBranch) {
            if (avgBranchDepth.isvalid())
                std::cout << std::setw(space) << avgBranchDepth.getAvgUInt();
            else
                std::cout << std::setw(space) << "no data";
        }
        #endif //RANDOM_LOOKAROUND_SEARCHSPACE

        #ifdef USE_GAUSS
        print_gauss_sum_stats();
        #endif //USE_GAUSS

        std::cout << std::endl;
    }
}

void Solver::printEndSearchStat()
{
    if (conf.verbosity >= 1) {
        printRestartStat("E");
    }
}

#ifdef USE_GAUSS
void Solver::print_gauss_sum_stats()
{
    if (gauss_matrixes.size() == 0 && conf.verbosity >= 2) {
        std::cout << "  --";
        return;
    }

    uint32_t called = 0;
    uint32_t useful_prop = 0;
    uint32_t useful_confl = 0;
    uint32_t disabled = 0;
    for (vector<Gaussian*>::const_iterator gauss = gauss_matrixes.begin(), end= gauss_matrixes.end(); gauss != end; gauss++) {
        disabled += (*gauss)->get_disabled();
        called += (*gauss)->get_called();
        useful_prop += (*gauss)->get_useful_prop();
        useful_confl += (*gauss)->get_useful_confl();
        sum_gauss_unit_truths += (*gauss)->get_unit_truths();
        //gauss->print_stats();
        //gauss->print_matrix_stats();
    }
    sum_gauss_called += called;
    sum_gauss_confl += useful_confl;
    sum_gauss_prop += useful_prop;

    if (conf.verbosity >= 2) {
        if (called == 0) {
            std::cout << " --";
        } else {
            std::cout << " "
            << std::fixed << std::setprecision(1) << std::setw(5)
            << ((double)useful_prop/(double)called*100.0) << "% "
            << std::fixed << std::setprecision(1) << std::setw(5)
            << ((double)useful_confl/(double)called*100.0) << "% "
            << std::fixed << std::setprecision(1) << std::setw(5)
            << (100.0-(double)disabled/(double)gauss_matrixes.size()*100.0) << "%";
        }
    }
}
#endif //USE_GAUSS

/**
@brief Sorts the watchlists' clauses as: binary, tertiary, normal, xor
*/
void Solver::sortWatched()
{
    #ifdef VERBOSE_DEBUG
    std::cout << "Sorting watchlists:" << std::endl;
    #endif
    double myTime = cpuTime();
    for (vec<Watched> *i = watches.getData(), *end = watches.getDataEnd(); i != end; i++) {
        if (i->size() == 0) continue;
        #ifdef VERBOSE_DEBUG
        vec<Watched>& ws = *i;
        std::cout << "Before sorting:" << std::endl;
        for (uint32_t i2 = 0; i2 < ws.size(); i2++) {
            if (ws[i2].isBinary()) std::cout << "Binary,";
            if (ws[i2].isTriClause()) std::cout << "Tri,";
            if (ws[i2].isClause()) std::cout << "Normal,";
            if (ws[i2].isXorClause()) std::cout << "Xor,";
        }
        std::cout << std::endl;
        #endif //VERBOSE_DEBUG

        std::sort(i->getData(), i->getDataEnd(), WatchedSorter());

        #ifdef VERBOSE_DEBUG
        std::cout << "After sorting:" << std::endl;
        for (uint32_t i2 = 0; i2 < ws.size(); i2++) {
            if (ws[i2].isBinary()) std::cout << "Binary,";
            if (ws[i2].isTriClause()) std::cout << "Tri,";
            if (ws[i2].isClause()) std::cout << "Normal,";
            if (ws[i2].isXorClause()) std::cout << "Xor,";
        }
        std::cout << std::endl;
        #endif //VERBOSE_DEBUG
    }

    if (conf.verbosity >= 3) {
        std::cout << "c watched "
        << "sorting time: " << cpuTime() - myTime
        << std::endl;
    }
}

void Solver::addSymmBreakClauses()
{
    if (xorclauses.size() > 0) {
        std::cout << "c xor clauses present -> no saucy" << std::endl;
        return;
    }
    double myTime = cpuTime();
    std::cout << "c Doing saucy" << std::endl;
    dumpOrigClauses("origProblem.cnf");

    int rvalue;
    rvalue= system("grep -v \"^c\" origProblem.cnf > origProblem2.cnf");
    if (rvalue >= 2) { // unsuccessful grep in POSIX standard
        std::cout << "c impossible to complete saucy" << std::endl;
        return;
    }
    rvalue= system("python saucyReader.py origProblem2.cnf > output");
    if (rvalue != 0) { // unsuccessful saucyReader.py
        std::cout << "c impossible to complete saucy" << std::endl;
        return;
    }


    DimacsParser parser(this, false, false, false, true);

    #ifdef DISABLE_ZLIB
    FILE * in = fopen("output", "rb");
    #else
    gzFile in = gzopen("output", "rb");
    #endif // DISABLE_ZLIB
    parser.parse_DIMACS(in);
    #ifdef DISABLE_ZLIB
    fclose(in);
    #else
    gzclose(in);
    #endif // DISABLE_ZLIB
    std::cout << "c Finished saucy, time: " << (cpuTime() - myTime) << std::endl;
}

/**
@brief Pretty-prints a literal
*/
void Solver::printLit(const Lit l) const
{
    printf("%s%d:%c", l.sign() ? "-" : "", l.var()+1, value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
}

/**
@brief Sets that we need a CNF file that documents all commands

newVar() and addClause(), addXorClause() commands are logged to this CNF
file and then can be re-read with special arguments to the main program. This
can help simulate a segfaulting library-call
*/
bool Solver::needLibraryCNFFile(const std::string& fileName)
{
    libraryCNFFile = fopen(fileName.c_str(), "w");
    return libraryCNFFile != NULL;
}

template<class T, class T2>
void Solver::printStatsLine(std::string left, T value, T2 value2, std::string extra)
{
    std::cout << std::fixed << std::left << std::setw(27) << left << ": " << std::setw(11) << std::setprecision(2) << value << " (" << std::left << std::setw(9) << std::setprecision(2) << value2 << " " << extra << ")" << std::endl;
}

template<class T>
void Solver::printStatsLine(std::string left, T value, std::string extra)
{
    std::cout << std::fixed << std::left << std::setw(27) << left << ": " << std::setw(11) << std::setprecision(2) << value << extra << std::endl;
}

/**
@brief prints the statistics line at the end of solving

Prints all sorts of statistics, like number of restarts, time spent in
SatELite-type simplification, number of unit claues found, etc.
*/
void Solver::printStats()
{
    double   cpu_time = cpuTime();
    uint64_t mem_used = memUsed();

    int numThreads = omp_get_num_threads();
    if (numThreads > 1) {
        std::cout << "c Following stats are for *FIRST FINISHED THREAD ONLY*" << std::endl;
        #if !defined(_MSC_VER) && !defined(RUSAGE_THREAD)
        std::cout << "c There is no platform-independent way to measure time per thread" << std::endl;
        std::cout << "c All times indicated are sum of ALL threads" << std::endl;
        std::cout << "c Use a utilty provided by your platform to get total thread time, etc." << std::endl;
        #endif
    }
    printStatsLine("c num threads" , numThreads);

    //Restarts stats
    printStatsLine("c restarts", starts);
    printStatsLine("c dynamic restarts", dynStarts);
    printStatsLine("c static restarts", staticStarts);
    printStatsLine("c full restarts", fullStarts);
    printStatsLine("c total simplify time", totalSimplifyTime);

    //Learnts stats
    printStatsLine("c learnts DL2", nbGlue2);
    printStatsLine("c learnts size 2", numNewBin);
    printStatsLine("c learnts size 1", get_unitary_learnts_num(), (double)get_unitary_learnts_num()/(double)nVars()*100.0, "% of vars");
    printStatsLine("c filedLit time", getTotalTimeFailedLitSearcher(), getTotalTimeFailedLitSearcher()/cpu_time*100.0, "% time");

    //Subsumer stats
    printStatsLine("c v-elim SatELite", getNumElimSubsume(), (double)getNumElimSubsume()/(double)nVars()*100.0, "% vars");
    printStatsLine("c SatELite time", getTotalTimeSubsumer(), getTotalTimeSubsumer()/cpu_time*100.0, "% time");

    //XorSubsumer stats
    printStatsLine("c v-elim xor", getNumElimXorSubsume(), (double)getNumElimXorSubsume()/(double)nVars()*100.0, "% vars");
    printStatsLine("c xor elim time", getTotalTimeXorSubsumer(), getTotalTimeXorSubsumer()/cpu_time*100.0, "% time");

    //VarReplacer stats
    printStatsLine("c num binary xor trees", getNumXorTrees());
    printStatsLine("c binxor trees' crown", getNumXorTreesCrownSize(), (double)getNumXorTreesCrownSize()/(double)getNumXorTrees(), "leafs/tree");
    printStatsLine("c bin xor find time", getTotalTimeSCC());

    //OTF clause improvement stats
    printStatsLine("c OTF clause improved", improvedClauseNo, (double)improvedClauseNo/(double)conflicts, "clauses/conflict");
    printStatsLine("c OTF impr. size diff", improvedClauseSize, (double)improvedClauseSize/(double)improvedClauseNo, " lits/clause");

    //Clause-shrinking through watchlists
    printStatsLine("c OTF cl watch-shrink", numShrinkedClause, (double)numShrinkedClause/(double)conflicts, "clauses/conflict");
    printStatsLine("c OTF cl watch-sh-lit", numShrinkedClauseLits, (double)numShrinkedClauseLits/(double)numShrinkedClause, " lits/clause");
    printStatsLine("c tried to recurMin cls", moreRecurMinLDo, (double)moreRecurMinLDo/(double)conflicts*100.0, " % of conflicts");
    printStatsLine("c updated cache", updateTransCache, updateTransCache/(double)moreRecurMinLDo, " lits/tried recurMin");

    //Multi-threading
    if (numThreads > 1) {
        printStatsLine("c unit cls received", dataSync->getRecvUnitData(), (double)dataSync->getRecvUnitData()/(double)get_unitary_learnts_num()*100.0, "% of units");
        printStatsLine("c unit cls sent", dataSync->getSentUnitData(), (double)dataSync->getSentUnitData()/(double)get_unitary_learnts_num()*100.0, "% of units");
        printStatsLine("c bin cls received", dataSync->getRecvBinData());
        printStatsLine("c bin cls sent", dataSync->getSentBinData());
    }

    #ifdef USE_GAUSS
    if (gaussconfig.decision_until > 0) {
        std::cout << "c " << std::endl;
        printStatsLine("c gauss unit truths ", get_sum_gauss_unit_truths());
        printStatsLine("c gauss called", get_sum_gauss_called());
        printStatsLine("c gauss conflicts ", get_sum_gauss_confl(), (double)get_sum_gauss_confl() / (double)get_sum_gauss_called() * 100.0, " %");
        printStatsLine("c gauss propagations ", get_sum_gauss_prop(), (double)get_sum_gauss_prop() / (double)get_sum_gauss_called() * 100.0, " %");
        printStatsLine("c gauss useful", ((double)get_sum_gauss_prop() + (double)get_sum_gauss_confl())/ (double)get_sum_gauss_called() * 100.0, " %");
        std::cout << "c " << std::endl;
    }
    #endif

    printStatsLine("c clauses over max glue", nbClOverMaxGlue, (double)nbClOverMaxGlue/(double)conflicts*100.0, "% of all clauses");

    //Search stats
    printStatsLine("c conflicts", conflicts, (double)conflicts/cpu_time, "/ sec");
    printStatsLine("c decisions", decisions, (double)rnd_decisions*100.0/(double)decisions, "% random");
    printStatsLine("c bogo-props", propagations, (double)propagations/cpu_time, "/ sec");
    printStatsLine("c conflict literals", tot_literals, (double)(max_literals - tot_literals)*100.0/ (double)max_literals, "% deleted");

    //General stats
    printStatsLine("c Memory used", (double)mem_used / 1048576.0, " MB");
    if (numThreads > 1) {
        #if !defined(_MSC_VER) && defined(RUSAGE_THREAD)
        printStatsLine("c single-thread CPU time", cpu_time, " s");
        printStatsLine("c all-threads sum CPU time", cpuTimeTotal(), " s");
        #else
        printStatsLine("c all-threads sum CPU time", cpu_time, " s");
        #endif
    } else {
        printStatsLine("c CPU time", cpu_time, " s");
    }
}
