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

#ifndef XORFINDER_H
#define XORFINDER_H

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#define DEBUG_XORFIND
//#define DEBUG_XORFIND2

#include "Clause.h"
#include "VarReplacer.h"
#include "ClauseCleaner.h"

namespace CMSat {

class Solver;

using std::pair;

/**
@brief Finds xors given a set of clauses

It basically sorts clauses' literals, sorts clauses according to size and
variable content, then idetifies continious reagions that could be an XOR
clause, finds the xor clause by counting the number of unique negation
permutations of the literals, then removes the clauses, and inserts the xor
clause
*/
class XorFinder
{
    public:
        XorFinder(Solver& _solver, vec<Clause*>& cls);
        bool fullFindXors(const uint32_t minSize, const uint32_t maxSize);
        void addAllXorAsNorm();

    private:
        typedef vector<pair<Clause*, uint32_t> > ClauseTable;

        bool findXors(uint32_t& sumLengths);
        bool getNextXor(ClauseTable::iterator& begin, ClauseTable::iterator& end, bool& impair);

        /**
        @brief For sorting clauses according to their size&their var content. Clauses' variables must already be sorted
        */
        struct clause_sorter_primary {
            bool operator()(const pair<Clause*, uint32_t>& c11, const pair<Clause*, uint32_t>& c22)
            {
                if (c11.first->size() != c22.first->size())
                    return (c11.first->size() < c22.first->size());

                #ifdef DEBUG_XORFIND2
                Clause& c1 = *c11.first;
                for (uint32_t i = 0; i+1 < c1.size(); i++)
                    assert(c1[i].var() <= c1[i+1].var());

                Clause& c2 = *c22.first;
                for (uint32_t i = 0; i+1 < c2.size(); i++)
                    assert(c2[i].var() <= c2[i+1].var());
                #endif //DEBUG_XORFIND2

                for (a = c11.first->getData(), b = c22.first->getData(), end = c11.first->getDataEnd(); a != end; a++, b++) {
                    if (a->var() != b->var())
                        return (a->var() > b->var());
                }

                return false;
            }

            Lit const *a;
            Lit const *b;
            Lit const *end;
        };

        /**
        @brief Sorts clauses with equal length and variable content according to their literals' signs

        NOTE: the length and variable content of c11 and c22 MUST be the same

        Used to avoid the problem of having 2 clauses with exactly the same
        content being counted as two different clauses (when counting the
        (im)pairedness of XOR being searched)
        */
        struct clause_sorter_secondary {
            bool operator()(const pair<Clause*, uint32_t>& c11, const pair<Clause*, uint32_t>& c22) const
            {
                const Clause& c1 = *(c11.first);
                const Clause& c2 = *(c22.first);
                assert(c1.size() == c2.size());

                for (uint32_t i = 0, size = c1.size(); i < size; i++) {
                    assert(c1[i].var() == c2[i].var());
                    if (c1[i].sign() !=  c2[i].sign())
                        return c1[i].sign();
                }

                return false;
            }
        };

        /**
        @brief Returns whether vars in clauses are the same -- clauses' literals must be identically sorted
        */
        bool clause_vareq(const Clause* c1, const Clause* c2) const
        {
            if (c1->size() != c2->size())
                return false;

            for (uint32_t i = 0, size = c1->size(); i < size; i++)
                if ((*c1)[i].var() != (*c2)[i].var())
                    return false;

            return true;
        }

        ClauseTable table;
        vector<bool> toRemove;
        vector<bool> toLeaveInPlace;
        void clearToRemove();
        uint32_t foundXors;

        //For adding xor clause as normal clause
        void addXorAsNormal3(XorClause& c);
        void addXorAsNormal4(XorClause& c);

        vec<Clause*>& cls;

        bool clauseEqual(const Clause& c1, const Clause& c2) const;
        bool impairSigns(const Clause& c) const;
        void countImpairs(const ClauseTable::iterator& begin, const ClauseTable::iterator& end, uint32_t& numImpair, uint32_t& numPair) const;
        bool isXor(const uint32_t size, const ClauseTable::iterator& begin, const ClauseTable::iterator& end, bool& impair);

        Solver& solver;
};

}

#endif //XORFINDER_H
