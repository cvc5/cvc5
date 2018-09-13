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

#include "clauseallocator.h"

#include <stdlib.h>
#include <algorithm>
#include <string.h>
#include <limits>
#include <cassert>
#include <cmath>
#include "solvertypes.h"
#include "clause.h"
#include "solver.h"
#include "searcher.h"
#include "time_mem.h"
#include "sqlstats.h"
#ifdef USE_GAUSS
#include "EGaussian.h"
#endif

#ifdef USE_VALGRIND
#include "valgrind/valgrind.h"
#include "valgrind/memcheck.h"
#endif

using namespace CMSat;

using std::pair;
using std::cout;
using std::endl;


//For mild debug info:
//#define DEBUG_CLAUSEALLOCATOR

//For listing each and every clause location:
//#define DEBUG_CLAUSEALLOCATOR2

#define MIN_LIST_SIZE (50000 * (sizeof(Clause) + 4*sizeof(Lit))/sizeof(BASE_DATA_TYPE))
#define ALLOC_GROW_MULT 1.5

#define MAXSIZE ((1ULL << (EFFECTIVELY_USEABLE_BITS))-1)

ClauseAllocator::ClauseAllocator() :
    dataStart(NULL)
    , size(0)
    , capacity(0)
    , currentlyUsedSize(0)
{
    assert(MIN_LIST_SIZE < MAXSIZE);
}

/**
@brief Frees all stacks
*/
ClauseAllocator::~ClauseAllocator()
{
    free(dataStart);
}

void* ClauseAllocator::allocEnough(
    uint32_t num_lits
) {
    //Try to quickly find a place at the end of a dataStart
    uint64_t neededbytes = sizeof(Clause) + sizeof(Lit)*num_lits;
    uint64_t needed
        = neededbytes/sizeof(BASE_DATA_TYPE) + (bool)(neededbytes % sizeof(BASE_DATA_TYPE));

    if (size + needed > capacity) {
        //Grow by default, but don't go under or over the limits
        uint64_t newcapacity = capacity * ALLOC_GROW_MULT;
        newcapacity = std::max<size_t>(newcapacity, MIN_LIST_SIZE);
        while (newcapacity < size+needed) {
            newcapacity *= ALLOC_GROW_MULT;
        }
        assert(newcapacity >= size+needed);
        newcapacity = std::min<size_t>(newcapacity, MAXSIZE);

        //Oops, not enough space anyway
        if (newcapacity < size + needed) {
            std::cerr
            << "ERROR: memory manager can't handle the load."
#ifndef LARGE_OFFSETS
            << " **PLEASE RECOMPILE WITH -DLARGEMEM=ON**"
#endif
            << " size: " << size
            << " needed: " << needed
            << " newcapacity: " << newcapacity
            << endl;
            std::cout
            << "ERROR: memory manager can't handle the load."
#ifndef LARGE_OFFSETS
            << " **PLEASE RECOMPILE WITH -DLARGEMEM=ON**"
#endif
            << " size: " << size
            << " needed: " << needed
            << " newcapacity: " << newcapacity
            << endl;

            throw std::bad_alloc();
        }

        //Reallocate data
        BASE_DATA_TYPE* new_dataStart;
        new_dataStart = (BASE_DATA_TYPE*)realloc(
            dataStart
            , newcapacity*sizeof(BASE_DATA_TYPE)
        );

        //Realloc failed?
        if (new_dataStart == NULL) {
            std::cerr
            << "ERROR: while reallocating clause space"
            << endl;

            throw std::bad_alloc();
        }
        dataStart = new_dataStart;

        //Update capacity to reflect the update
        capacity = newcapacity;
    }

    //Add clause to the set
    Clause* pointer = (Clause*)(dataStart + size);
    size += needed;
    currentlyUsedSize += needed;

    return pointer;
}

/**
@brief Given the pointer of the clause it finds a 32-bit offset for it

Calculates the stack frame and the position of the pointer in the stack, and
rerturns a 32-bit value that is a concatenation of these two
*/
ClOffset ClauseAllocator::get_offset(const Clause* ptr) const
{
    return ((BASE_DATA_TYPE*)ptr - dataStart);
}

/**
@brief Frees a clause

If clause was binary, it frees it in quite a normal way. If it isn't, then it
needs to set the data in the Clause that it has been freed, and updates the
stack it belongs to such that the stack can now that its effectively used size
is smaller

NOTE: The size of claues can change. Therefore, currentlyUsedSizes can in fact
be incorrect, since it was incremented by the ORIGINAL size of the clause, but
when the clause is "freed", it is decremented by the POTENTIALLY SMALLER size
of the clause. Therefore, the "currentlyUsedSizes" is an overestimation!!
*/
void ClauseAllocator::clauseFree(Clause* cl)
{
    assert(!cl->freed());

    bool quick_freed = false;
    #ifdef USE_GAUSS
    if (cl->gauss_temp_cl()) {
        uint64_t neededbytes = (sizeof(Clause) + sizeof(Lit)*cl->size());
        uint64_t needed
            = neededbytes/sizeof(BASE_DATA_TYPE) + (bool)(neededbytes % sizeof(BASE_DATA_TYPE));

        if (((BASE_DATA_TYPE*)cl + needed) == (dataStart + size)) {
            size -= needed;
            currentlyUsedSize -= needed;
            quick_freed = true;
        }
    }
    #endif

    if (!quick_freed) {
        cl->setFreed();
        uint64_t est_num_cl = cl->size();
        est_num_cl = std::max(est_num_cl, (uint64_t)3); //we sometimes allow gauss to allocate 3-long clauses
        uint64_t bytes_freed = sizeof(Clause) + est_num_cl*sizeof(Lit);
        uint64_t elems_freed = bytes_freed/sizeof(BASE_DATA_TYPE) + (bool)(bytes_freed % sizeof(BASE_DATA_TYPE));
        currentlyUsedSize -= elems_freed;
    }

    #ifdef VALGRIND_MAKE_MEM_UNDEFINED
    VALGRIND_MAKE_MEM_UNDEFINED(((char*)cl)+sizeof(Clause), cl->size()*sizeof(Lit));
    #endif
}

void ClauseAllocator::clauseFree(ClOffset offset)
{
    Clause* cl = ptr(offset);
    clauseFree(cl);
}

ClOffset ClauseAllocator::move_cl(
    ClOffset* newDataStart
    , ClOffset*& new_ptr
    , Clause* old
) const {
    uint64_t bytesNeeded = sizeof(Clause) + old->size()*sizeof(Lit);
    uint64_t sizeNeeded = bytesNeeded/sizeof(BASE_DATA_TYPE) + (bool)(bytesNeeded % sizeof(BASE_DATA_TYPE));
    memcpy(new_ptr, old, sizeNeeded*sizeof(BASE_DATA_TYPE));

    ClOffset new_offset = new_ptr-newDataStart;
    (*old)[0] = Lit::toLit(new_offset & 0xFFFFFFFF);
    #ifdef LARGE_OFFSETS
    (*old)[1] = Lit::toLit((new_offset>>32) & 0xFFFFFFFF);
    #endif
    old->reloced = true;

    new_ptr += sizeNeeded;
    return new_offset;
}

/**
@brief If needed, compacts stacks, removing unused clauses

Firstly, the algorithm determines if the number of useless slots is large or
small compared to the problem size. If it is small, it does nothing. If it is
large, then it allocates new stacks, copies the non-freed clauses to these new
stacks, updates all pointers and offsets, and frees the original stacks.
*/
void ClauseAllocator::consolidate(
    Solver* solver
    , const bool force
) {
    //If re-allocation is not really neccessary, don't do it
    //Neccesities:
    //1) There is too much memory allocated. Re-allocation will save space
    //   Avoiding segfault (max is 16 outerOffsets, more than 10 is near)
    //2) There is too much empty, unused space (>30%)
    if (!force
        && (float_div(currentlyUsedSize, size) > 0.8 || currentlyUsedSize < (100ULL*1000ULL))
    ) {
        if (solver->conf.verbosity >= 3) {
            cout << "c Not consolidating memory." << endl;
        }
        return;
    }
    const double myTime = cpuTime();

    //Pointers that will be moved along
    BASE_DATA_TYPE * const newDataStart = (BASE_DATA_TYPE*)malloc(currentlyUsedSize*sizeof(BASE_DATA_TYPE));
    BASE_DATA_TYPE * new_ptr = newDataStart;

    assert(sizeof(BASE_DATA_TYPE) % sizeof(Lit) == 0);
    for(auto& ws: solver->watches) {
        for(Watched& w: ws) {
            if (w.isClause()) {
                Clause* old = ptr(w.get_offset());
                assert(!old->freed());
                Lit blocked = w.getBlockedLit();
                if (old->reloced) {
                    ClOffset new_offset = (*old)[0].toInt();
                    #ifdef LARGE_OFFSETS
                    new_offset += ((uint64_t)(*old)[1].toInt())<<32;
                    #endif
                    w = Watched(new_offset, blocked);
                } else {
                    ClOffset new_offset = move_cl(newDataStart, new_ptr, old);
                    w = Watched(new_offset, blocked);
                }
            }
        }
    }

    #ifdef USE_GAUSS
    for (EGaussian* gauss : solver->gmatrixes) {
        for(auto& gcl: gauss->clauses_toclear) {
            Clause* old = ptr(gcl.first);
            if (old->reloced) {
                ClOffset new_offset = (*old)[0].toInt();
                #ifdef LARGE_OFFSETS
                new_offset += ((uint64_t)(*old)[1].toInt())<<32;
                #endif
                gcl.first = new_offset;
            } else {
                ClOffset new_offset = move_cl(newDataStart, new_ptr, old);
                gcl.first = new_offset;
            }
            assert(!old->freed());
        }
    }
    #endif //USE_GAUSS

    update_offsets(solver->longIrredCls);
    for(auto& lredcls: solver->longRedCls) {
        update_offsets(lredcls);
    }

    //Fix up propBy
    for (size_t i = 0; i < solver->nVars(); i++) {
        VarData& vdata = solver->varData[i];
        if (vdata.reason.isClause()) {
            if (vdata.removed == Removed::none
                && solver->decisionLevel() >= vdata.level
                && vdata.level != 0
                && solver->value(i) != l_Undef
            ) {
                Clause* old = ptr(vdata.reason.get_offset());
                assert(!old->freed());
                ClOffset new_offset = (*old)[0].toInt();
                #ifdef LARGE_OFFSETS
                new_offset += ((uint64_t)(*old)[1].toInt())<<32;
                #endif
                vdata.reason = PropBy(new_offset);
            } else {
                vdata.reason = PropBy();
            }
        }
    }

    //Update sizes
    const uint64_t old_size = size;
    size = new_ptr-newDataStart;
    capacity = currentlyUsedSize;
    currentlyUsedSize = size;
    free(dataStart);
    dataStart = newDataStart;

    const double time_used = cpuTime() - myTime;
    if (solver->conf.verbosity >= 2) {
        cout << "c [mem] Consolidated memory ";
        cout << " old size "; print_value_kilo_mega(old_size*sizeof(BASE_DATA_TYPE));
        cout << "B new size"; print_value_kilo_mega(size*sizeof(BASE_DATA_TYPE));
        cout << "B bits of offset:" << std::fixed << std::setprecision(2) << std::log2(size);
        cout << solver->conf.print_times(time_used)
        << endl;
    }
    if (solver->sqlStats) {
        solver->sqlStats->time_passed_min(
            solver
            , "consolidate"
            , time_used
        );
    }
}

void ClauseAllocator::update_offsets(
    vector<ClOffset>& offsets
) {

    for(ClOffset& offs: offsets) {
        Clause* old = ptr(offs);
        assert(old->reloced);
        offs = (*old)[0].toInt();
        #ifdef LARGE_OFFSETS
        offs += ((uint64_t)(*old)[1].toInt())<<32;
        #endif
    }
}

size_t ClauseAllocator::mem_used() const
{
    uint64_t mem = 0;
    mem += capacity*sizeof(BASE_DATA_TYPE);

    return mem;
}
