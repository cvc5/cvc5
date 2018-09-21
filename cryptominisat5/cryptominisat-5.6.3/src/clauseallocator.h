/******************************************
Copyright (c) 2016, Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#ifndef CLAUSEALLOCATOR_H
#define CLAUSEALLOCATOR_H


#include "constants.h"
#include "cloffset.h"
#include "watched.h"
#include "clause.h"

#include <stdlib.h>
#include <map>
#include <vector>

namespace CMSat {

class Clause;
class Solver;
class PropEngine;

using std::map;
using std::vector;

/**
@brief Allocates memory for (xor) clauses

This class allocates memory in large chunks, then distributes it to clauses when
needed. When instructed, it consolidates the unused space (i.e. clauses free()-ed).
Essentially, it is a stack-like allocator for clauses. It is useful to have
this, because this way, we can address clauses according to their number,
which is 32-bit, instead of their address, which might be 64-bit
*/
class ClauseAllocator {
    public:
        ClauseAllocator();
        ~ClauseAllocator();

        template<class T>
        Clause* Clause_new(const T& ps, const uint32_t conflictNum
            #ifdef STATS_NEEDED
            , const int64_t ID
            #endif
        ) {
            if (ps.size() > (0x01UL << 28)) {
                throw CMSat::TooLongClauseError();
            }

            void* mem = allocEnough(ps.size());
            Clause* real = new (mem) Clause(ps, conflictNum
            #ifdef STATS_NEEDED
            , ID
            #endif
            );

            return real;
        }

        ClOffset get_offset(const Clause* ptr) const;

        inline Clause* ptr(const ClOffset offset) const
        {
            return (Clause*)(&dataStart[offset]);
        }

        void clauseFree(Clause* c); ///Frees memory and associated clause number
        void clauseFree(ClOffset offset);

        void consolidate(
            Solver* solver
            , const bool force = false
        );

        size_t mem_used() const;

    private:
        void update_offsets(vector<ClOffset>& offsets);

        ClOffset move_cl(
            ClOffset* newDataStart
            , ClOffset*& new_ptr
            , Clause* old
        ) const;

        BASE_DATA_TYPE* dataStart; ///<Stack starts at these positions
        uint64_t size; ///<The number of BASE_DATA_TYPE datapieces currently used in each stack
        /**
        @brief Clauses in the stack had this size when they were allocated
        This my NOT be their current size: the clauses may be shrinked during
        the running of the solver. Therefore, it is imperative that their orignal
        size is saved. This way, we can later move clauses around.
        */
        uint64_t capacity; ///<The number of BASE_DATA_TYPE datapieces allocated
        /**
        @brief The estimated used size of the stack
        This is incremented by clauseSize each time a clause is allocated, and
        decremetented by clauseSize each time a clause is deallocated. The
        problem is, that clauses can shrink, and thus this value will be an
        overestimation almost all the time
        */
        uint64_t currentlyUsedSize;

        void* allocEnough(const uint32_t num_lits);
};

} //end namespace

#endif //CLAUSEALLOCATOR_H
