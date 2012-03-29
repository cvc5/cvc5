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

#include "SharedData.h"
#include "Solver.h"

namespace CMSat {

class DataSync
{
    public:
        DataSync(Solver& solver, SharedData* sharedData);
        void newVar();
        bool syncData();


        template <class T> void signalNewBinClause(T& ps);
        void signalNewBinClause(Lit lit1, Lit lit2);

        uint32_t getSentUnitData() const;
        uint32_t getRecvUnitData() const;
        uint32_t getSentBinData() const;
        uint32_t getRecvBinData() const;

    private:
        //functions
        bool shareUnitData();
        bool syncBinFromOthers(const Lit lit, const vector<Lit>& bins, uint32_t& finished, vec<Watched>& ws);
        void syncBinToOthers();
        void addOneBinToOthers(const Lit lit1, const Lit lit2);
        bool shareBinData();

        //stuff to sync
        vector<std::pair<Lit, Lit> > newBinClauses;

        //stats
        uint64_t lastSyncConf;
        vec<uint32_t> syncFinish;
        uint32_t sentUnitData;
        uint32_t recvUnitData;
        uint32_t sentBinData;
        uint32_t recvBinData;

        //misc
        vec<char> seen;

        //main data
        SharedData* sharedData;
        Solver& solver;
};

inline uint32_t DataSync::getSentUnitData() const
{
    return sentUnitData;
}

inline uint32_t DataSync::getRecvUnitData() const
{
    return recvUnitData;
}

inline uint32_t DataSync::getSentBinData() const
{
    return sentBinData;
}

inline uint32_t DataSync::getRecvBinData() const
{
    return recvBinData;
}

template <class T>
inline void DataSync::signalNewBinClause(T& ps)
{
    if (sharedData == NULL) return;
    assert(ps.size() == 2);
    signalNewBinClause(ps[0], ps[1]);
}

inline void DataSync::signalNewBinClause(Lit lit1, Lit lit2)
{
    if (sharedData == NULL) return;
    if (lit1.toInt() > lit2.toInt()) std::swap(lit1, lit2);
    newBinClauses.push_back(std::make_pair(lit1, lit2));
}

}
