/*****************************************************************************
CryptoMiniSat -- Copyright (c) 2010 Mate Soos

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

#include "DataSync.h"
#include "Subsumer.h"
#include "VarReplacer.h"
#include "XorSubsumer.h"
#include <iomanip>

using namespace CMSat;

DataSync::DataSync(Solver& _solver, SharedData* _sharedData) :
    lastSyncConf(0)
    , sentUnitData(0)
    , recvUnitData(0)
    , sharedData(_sharedData)
    , solver(_solver)
{}

void DataSync::newVar()
{
    syncFinish.push(0);
    syncFinish.push(0);
    seen.push(false);
    seen.push(false);
}

bool DataSync::syncData()
{
    if (sharedData == NULL
        || lastSyncConf + SYNC_EVERY_CONFL >= solver.conflicts) return true;

    assert(sharedData != NULL);
    assert(solver.decisionLevel() == 0);

    bool ok;
    #pragma omp critical (unitData)
    ok = shareUnitData();
    if (!ok) return false;

    #pragma omp critical (binData)
    ok = shareBinData();
    if (!ok) return false;

    lastSyncConf = solver.conflicts;

    return true;
}

bool DataSync::shareBinData()
{
    uint32_t oldRecvBinData = recvBinData;
    uint32_t oldSentBinData = sentBinData;

    SharedData& shared = *sharedData;
    if (shared.bins.size() != solver.nVars()*2)
        shared.bins.resize(solver.nVars()*2);

    for (uint32_t wsLit = 0; wsLit < solver.nVars()*2; wsLit++) {
        Lit lit1 = ~Lit::toLit(wsLit);
        lit1 = solver.varReplacer->getReplaceTable()[lit1.var()] ^ lit1.sign();
        if (solver.subsumer->getVarElimed()[lit1.var()]
            || solver.xorSubsumer->getVarElimed()[lit1.var()]
            || solver.value(lit1.var()) != l_Undef
            ) continue;

        vector<Lit>& bins = shared.bins[wsLit];
        vec<Watched>& ws = solver.watches[wsLit];

        if (bins.size() > syncFinish[wsLit]
            && !syncBinFromOthers(lit1, bins, syncFinish[wsLit], ws)) return false;
    }

    syncBinToOthers();

    if (solver.conf.verbosity >= 3) {
        std::cout << "c got bins " << std::setw(10) << (recvBinData - oldRecvBinData)
        << std::setw(10) << " sent bins " << (sentBinData - oldSentBinData) << std::endl;
    }

    return true;
}

bool DataSync::syncBinFromOthers(const Lit lit, const vector<Lit>& bins, uint32_t& finished, vec<Watched>& ws)
{
    assert(solver.varReplacer->getReplaceTable()[lit.var()].var() == lit.var());
    assert(solver.subsumer->getVarElimed()[lit.var()] == false);
    assert(solver.xorSubsumer->getVarElimed()[lit.var()] == false);

    vec<Lit> addedToSeen;
    for (vec<Watched>::iterator it = ws.getData(), end = ws.getDataEnd(); it != end; it++) {
        if (it->isBinary()) {
            addedToSeen.push(it->getOtherLit());
            seen[it->getOtherLit().toInt()] = true;
        }
    }

    vec<Lit> lits(2);
    for (uint32_t i = finished; i < bins.size(); i++) {
        if (!seen[bins[i].toInt()]) {
            Lit otherLit = bins[i];
            otherLit = solver.varReplacer->getReplaceTable()[otherLit.var()] ^ otherLit.sign();
            if (solver.subsumer->getVarElimed()[otherLit.var()]
                || solver.xorSubsumer->getVarElimed()[otherLit.var()]
                || solver.value(otherLit.var()) != l_Undef
                ) continue;

            recvBinData++;
            lits[0] = lit;
            lits[1] = otherLit;
            solver.addClauseInt(lits, true, 2, 0, true);
            lits.clear();
            lits.growTo(2);
            if (!solver.ok) goto end;
        }
    }
    finished = bins.size();

    end:
    for (uint32_t i = 0; i < addedToSeen.size(); i++)
        seen[addedToSeen[i].toInt()] = false;

    return solver.ok;
}

void DataSync::syncBinToOthers()
{
    for(vector<std::pair<Lit, Lit> >::const_iterator it = newBinClauses.begin(), end = newBinClauses.end(); it != end; it++) {
        addOneBinToOthers(it->first, it->second);
    }

    newBinClauses.clear();
}

void DataSync::addOneBinToOthers(const Lit lit1, const Lit lit2)
{
    assert(lit1.toInt() < lit2.toInt());

    vector<Lit>& bins = sharedData->bins[(~lit1).toInt()];
    for (vector<Lit>::const_iterator it = bins.begin(), end = bins.end(); it != end; it++) {
        if (*it == lit2) return;
    }

    bins.push_back(lit2);
    sentBinData++;
}

bool DataSync::shareUnitData()
{
    uint32_t thisGotUnitData = 0;
    uint32_t thisSentUnitData = 0;

    SharedData& shared = *sharedData;
    shared.value.growTo(solver.nVars(), l_Undef);
    for (uint32_t var = 0; var < solver.nVars(); var++) {
        Lit thisLit = Lit(var, false);
        thisLit = solver.varReplacer->getReplaceTable()[thisLit.var()] ^ thisLit.sign();
        const lbool thisVal = solver.value(thisLit);
        const lbool otherVal = shared.value[var];

        if (thisVal == l_Undef && otherVal == l_Undef) continue;
        if (thisVal != l_Undef && otherVal != l_Undef) {
            if (thisVal != otherVal) {
                solver.ok = false;
                return false;
            } else {
                continue;
            }
        }

        if (otherVal != l_Undef) {
            assert(thisVal == l_Undef);
            Lit litToEnqueue = thisLit ^ (otherVal == l_False);
            if (solver.subsumer->getVarElimed()[litToEnqueue.var()]
                || solver.xorSubsumer->getVarElimed()[litToEnqueue.var()]
                ) continue;

            solver.uncheckedEnqueue(litToEnqueue);
            solver.ok = solver.propagate<false>().isNULL();
            if (!solver.ok) return false;
            thisGotUnitData++;
            continue;
        }

        if (thisVal != l_Undef) {
            assert(otherVal == l_Undef);
            shared.value[var] = thisVal;
            thisSentUnitData++;
            continue;
        }
    }

    if (solver.conf.verbosity >= 3 && (thisGotUnitData > 0 || thisSentUnitData > 0)) {
        std::cout << "c got units " << std::setw(8) << thisGotUnitData
        << " sent units " << std::setw(8) << thisSentUnitData << std::endl;
    }

    recvUnitData += thisGotUnitData;
    sentUnitData += thisSentUnitData;

    return true;
}
