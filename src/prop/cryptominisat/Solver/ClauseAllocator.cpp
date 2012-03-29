/***********************************************************************
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
************************************************************************/

#include "ClauseAllocator.h"

#include <string.h>
#include <limits>
#include "assert.h"
#include "SolverTypes.h"
#include "Clause.h"
#include "Solver.h"
#include "time_mem.h"
#include "Subsumer.h"
#include "XorSubsumer.h"
//#include "VarReplacer.h"
#include "Gaussian.h"

#ifndef _MSC_VER
#include <sys/mman.h>
#endif //_MSC_VER


//For mild debug info:
//#define DEBUG_CLAUSEALLOCATOR

//For listing each and every clause location:
//#define DEBUG_CLAUSEALLOCATOR2

#define MIN_LIST_SIZE (300000 * (sizeof(Clause) + 4*sizeof(Lit))/sizeof(BASE_DATA_TYPE))
//#define MIN_LIST_SIZE (100 * (sizeof(Clause) + 4*sizeof(Lit))/sizeof(BASE_DATA_TYPE))
#define ALLOC_GROW_MULT 8
//We shift stuff around in Watched, so not all of 32 bits are useable.
#define EFFECTIVELY_USEABLE_BITS 30
#define MAXSIZE ((1 << (EFFECTIVELY_USEABLE_BITS-NUM_BITS_OUTER_OFFSET))-1)

using namespace CMSat;

ClauseAllocator::ClauseAllocator()
{
    assert(MIN_LIST_SIZE < MAXSIZE);
    assert(sizeof(Clause) + 2*sizeof(Lit) >= sizeof(NewPointerAndOffset));
}

/**
@brief Frees all stacks
*/
ClauseAllocator::~ClauseAllocator()
{
    for (uint32_t i = 0; i < dataStarts.size(); i++) {
        free(dataStarts[i]);
    }
}

/**
@brief Allocates space&initializes a clause
*/
template<class T>
Clause* ClauseAllocator::Clause_new(const T& ps, const bool learnt)
{
    assert(ps.size() > 2);
    void* mem = allocEnough(ps.size());
    Clause* real= new (mem) Clause(ps, learnt);
    //assert(!(ps.size() == 2 && !real->wasBin()));

    return real;
}

template Clause* ClauseAllocator::Clause_new(const vec<Lit>& ps, const bool learnt);
template Clause* ClauseAllocator::Clause_new(const Clause& ps, const bool learnt);
template Clause* ClauseAllocator::Clause_new(const XorClause& ps, const bool learnt);

/**
@brief Allocates space&initializes an xor clause
*/
template<class T>
XorClause* ClauseAllocator::XorClause_new(const T& ps, const bool xorEqualFalse)
{
    assert(ps.size() > 2);
    void* mem = allocEnough(ps.size());
    XorClause* real= new (mem) XorClause(ps, xorEqualFalse);

    return real;
}
template XorClause* ClauseAllocator::XorClause_new(const vec<Lit>& ps, const bool inverted);
template XorClause* ClauseAllocator::XorClause_new(const XorClause& ps, const bool inverted);

/**
@brief Allocates space for a new clause & copies a give clause to it
*/
Clause* ClauseAllocator::Clause_new(Clause& c)
{
    assert(c.size() > 2);
    void* mem = allocEnough(c.size());
    memcpy(mem, &c, sizeof(Clause)+sizeof(Lit)*c.size());

    return (Clause*)mem;
}

/**
@brief Allocates enough space for a new clause

It tries to add the clause to the end of any already created stacks
if that is impossible, it creates a new stack, and adds the clause there
*/
void* ClauseAllocator::allocEnough(const uint32_t size) throw (std::bad_alloc)
{
    assert(sizes.size() == dataStarts.size());
    assert(maxSizes.size() == dataStarts.size());
    assert(origClauseSizes.size() == dataStarts.size());

    assert(size > 2 && "Clause size cannot be 2 or less, those are stored natively");

    const uint32_t needed = sizeof(Clause) + sizeof(Lit)*size;
    bool found = false;
    uint32_t which = std::numeric_limits<uint32_t>::max();
    for (uint32_t i = 0; i < sizes.size(); i++) {
        if (sizes[i] + needed < maxSizes[i]) {
            found = true;
            which = i;
            break;
        }
    }

    if (!found) {
        //Checking whether we are out of memory, because the offset that we can
        //store is too little
        if (dataStarts.size() == (1<<NUM_BITS_OUTER_OFFSET))
            throw std::bad_alloc();

        uint32_t nextSize; //number of BYTES to allocate
        if (maxSizes.size() != 0) {
            nextSize = std::min((uint32_t)(maxSizes[maxSizes.size()-1]*ALLOC_GROW_MULT), (uint32_t)MAXSIZE);
            nextSize = std::max(nextSize, (uint32_t)MIN_LIST_SIZE*2);
        } else {
            nextSize = (uint32_t)MIN_LIST_SIZE;
        }
        assert(needed <  nextSize);
        assert(nextSize <= MAXSIZE);

        #ifdef DEBUG_CLAUSEALLOCATOR
        std::cout << "c New list in ClauseAllocator. Size: " << nextSize
        << " (maxSize: " << MAXSIZE
        << ")" << std::endl;
        #endif //DEBUG_CLAUSEALLOCATOR

        BASE_DATA_TYPE *dataStart;
        dataStart = (BASE_DATA_TYPE *)malloc(sizeof(BASE_DATA_TYPE) * nextSize);

        dataStarts.push(dataStart);
        sizes.push(0);
        maxSizes.push(nextSize);
        origClauseSizes.push();
        currentlyUsedSizes.push(0);
        which = dataStarts.size()-1;
    }
    #ifdef DEBUG_CLAUSEALLOCATOR2
    std::cout
    << "selected list = " << which
    << " size = " << sizes[which]
    << " maxsize = " << maxSizes[which]
    << " diff = " << maxSizes[which] - sizes[which] << std::endl;
    #endif //DEBUG_CLAUSEALLOCATOR

    assert(which != std::numeric_limits<uint32_t>::max());
    Clause* pointer = (Clause*)(dataStarts[which] + sizes[which]);
    sizes[which] += needed;
    currentlyUsedSizes[which] += needed;
    origClauseSizes[which].push(needed);

    return pointer;
}

/**
@brief Given the pointer of the clause it finds a 32-bit offset for it

Calculates the stack frame and the position of the pointer in the stack, and
rerturns a 32-bit value that is a concatenation of these two
*/
ClauseOffset ClauseAllocator::getOffset(const Clause* ptr) const
{
    uint32_t outerOffset = getOuterOffset(ptr);
    uint32_t interOffset = getInterOffset(ptr, outerOffset);
    return combineOuterInterOffsets(outerOffset, interOffset);
}

/**
@brief Combines the stack number and the internal offset into one 32-bit number
*/
inline ClauseOffset ClauseAllocator::combineOuterInterOffsets(const uint32_t outerOffset, const uint32_t interOffset) const
{
    return (outerOffset | (interOffset << NUM_BITS_OUTER_OFFSET));
}

/**
@brief Given a pointer, finds which stack it's in
*/
inline uint32_t ClauseAllocator::getOuterOffset(const Clause* ptr) const
{
    uint32_t which = std::numeric_limits<uint32_t>::max();
    for (uint32_t i = 0; i < sizes.size(); i++) {
        if ((BASE_DATA_TYPE*)ptr >= dataStarts[i] && (BASE_DATA_TYPE*)ptr < dataStarts[i] + maxSizes[i]) {
            which = i;
            break;
        }
    }
    assert(which != std::numeric_limits<uint32_t>::max());

    return which;
}

/**
@brief Given a pointer and its stack number, returns its position inside the stack
*/
inline uint32_t ClauseAllocator::getInterOffset(const Clause* ptr, uint32_t outerOffset) const
{
    return ((BASE_DATA_TYPE*)ptr - dataStarts[outerOffset]);
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
void ClauseAllocator::clauseFree(Clause* c)
{
    assert(!c->getFreed());

    c->setFreed();
    uint32_t outerOffset = getOuterOffset(c);
    //uint32_t interOffset = getInterOffset(c, outerOffset);
    currentlyUsedSizes[outerOffset] -= sizeof(Clause) + c->size()*sizeof(Lit);
    //above should be
    //origClauseSizes[outerOffset][interOffset]
    //but it cannot be :(
}

/**
@brief If needed, compacts stacks, removing unused clauses

Firstly, the algorithm determines if the number of useless slots is large or
small compared to the problem size. If it is small, it does nothing. If it is
large, then it allocates new stacks, copies the non-freed clauses to these new
stacks, updates all pointers and offsets, and frees the original stacks.
*/
void ClauseAllocator::consolidate(Solver* solver, const bool force) throw (std::bad_alloc)
{
    double myTime = cpuTime();
    #ifdef DEBUG_PROPAGATEFROM
    checkGoodPropBy(solver);
    #endif

    uint32_t sum = 0;
    for (uint32_t i = 0; i < sizes.size(); i++) {
        sum += currentlyUsedSizes[i];
    }
    uint32_t sumAlloc = 0;
    for (uint32_t i = 0; i < sizes.size(); i++) {
        sumAlloc += sizes[i];
    }

    #ifdef DEBUG_CLAUSEALLOCATOR
    std::cout << "c ratio:" << (double)sum/(double)sumAlloc << std::endl;
    #endif //DEBUG_CLAUSEALLOCATOR

    //If re-allocation is not really neccessary, don't do it
    //Neccesities:
    //1) There is too much memory allocated. Re-allocation will save space
    //   Avoiding segfault (max is 16 outerOffsets, more than 10 is near)
    //2) There is too much empty, unused space (>30%)
    if (!force
        && ((double)sum/(double)sumAlloc > 0.7 && sizes.size() < 10)
       ) {
        if (solver->conf.verbosity >= 3) {
            std::cout << "c Not consolidating memory." << std::endl;
        }
        return;
    }

    #ifdef DEBUG_CLAUSEALLOCATOR
    std::cout << "c ------ Consolidating Memory ------------" << std::endl;
    #endif //DEBUG_CLAUSEALLOCATOR
    int64_t newMaxSizeNeed = (double)sum*1.2 + MIN_LIST_SIZE;
    #ifdef DEBUG_CLAUSEALLOCATOR
    std::cout << "c newMaxSizeNeed = " << newMaxSizeNeed << std::endl;
    #endif //DEBUG_CLAUSEALLOCATOR
    vec<uint32_t> newMaxSizes;
    for (uint32_t i = 0; i < (1 << NUM_BITS_OUTER_OFFSET); i++) {
        if (newMaxSizeNeed <= 0) break;

        uint32_t thisMaxSize = std::min(newMaxSizeNeed, (int64_t)MAXSIZE);
        if (i == 0) {
            thisMaxSize = std::max(thisMaxSize, (uint32_t)MIN_LIST_SIZE);
        } else {
            assert(i > 0);
            thisMaxSize = std::max(thisMaxSize, newMaxSizes[i-1]/2);
            thisMaxSize = std::max(thisMaxSize, (uint32_t)MIN_LIST_SIZE*2);
        }
        newMaxSizeNeed -= thisMaxSize;
        assert(thisMaxSize <= MAXSIZE);
        newMaxSizes.push(thisMaxSize);
        //because the clauses don't always fit
        //it might occur that there is enough place in total
        //but the very last clause would need to be fragmented
        //over multiple lists' ends :O
        //So this "magic" constant could take care of that....
        //or maybe not (if _very_ large clauses are used, always
        //bad chance, etc. :O )
        //NOTE: the + MIN_LIST_SIZE should take care of this above at
        // newMaxSizeNeed = sum + MIN_LIST_SIZE;
        #ifdef DEBUG_CLAUSEALLOCATOR
        std::cout << "c NEW MaxSizes:" << newMaxSizes[i] << std::endl;
        #endif //DEBUG_CLAUSEALLOCATOR
    }
    #ifdef DEBUG_CLAUSEALLOCATOR
    std::cout << "c ------------------" << std::endl;
    #endif //DEBUG_CLAUSEALLOCATOR

    if (newMaxSizeNeed > 0)
        throw std::bad_alloc();

    vec<uint32_t> newSizes;
    vec<vec<uint32_t> > newOrigClauseSizes;
    vec<BASE_DATA_TYPE*> newDataStartsPointers;
    vec<BASE_DATA_TYPE*> newDataStarts;
    for (uint32_t i = 0; i < newMaxSizes.size(); i++) {
        newSizes.push(0);
        newOrigClauseSizes.push();
        BASE_DATA_TYPE* pointer;
        pointer = (BASE_DATA_TYPE*)malloc(newMaxSizes[i]);
        newDataStartsPointers.push(pointer);
        newDataStarts.push(pointer);
    }

    vector<Clause*> clauses;
    for (uint32_t i = 0; i < dataStarts.size(); i++) {
        uint32_t currentLoc = 0;
        for (uint32_t i2 = 0; i2 < origClauseSizes[i].size(); i2++) {
            Clause* oldPointer = (Clause*)(dataStarts[i] + currentLoc);
            if (!oldPointer->getFreed()) {
                clauses.push_back(oldPointer);
            } else {
                (*((NewPointerAndOffset*)(oldPointer))).newOffset = std::numeric_limits<uint32_t>::max();
            }
            currentLoc += origClauseSizes[i][i2];
        }
    }

    putClausesIntoDatastruct(clauses);

    uint32_t outerPart = 0;
    //uint64_t skippedNum = 0;
    for (uint32_t i = 0; i < clauses.size(); i++) {
        Clause* clause = getClause();

        uint32_t sizeNeeded = (sizeof(Clause) + clause->size()*sizeof(Lit))/sizeof(BASE_DATA_TYPE);

        //Next line is needed, because in case of isRemoved()
        //, the size of the clause could become 0, thus having less
        // than enough space to carry the NewPointerAndOffset info
        sizeNeeded = std::max(sizeNeeded, (uint32_t)((sizeof(Clause) + 2*sizeof(Lit))/sizeof(BASE_DATA_TYPE)));

        if (newSizes[outerPart] + sizeNeeded > newMaxSizes[outerPart]) {
            outerPart++;
            assert(outerPart < newMaxSizes.size());
        }
        memcpy(newDataStartsPointers[outerPart], (BASE_DATA_TYPE*)clause, sizeNeeded*sizeof(BASE_DATA_TYPE));

        NewPointerAndOffset& ptr = *((NewPointerAndOffset*)clause);
        ptr.newOffset = combineOuterInterOffsets(outerPart, newSizes[outerPart]);
        ptr.newPointer = (Clause*)newDataStartsPointers[outerPart];

        newSizes[outerPart] += sizeNeeded;
        newOrigClauseSizes[outerPart].push(sizeNeeded);
        newDataStartsPointers[outerPart] += sizeNeeded;
    }

    updateAllOffsetsAndPointers(solver);

    for (uint32_t i = 0; i < dataStarts.size(); i++)
        free(dataStarts[i]);

    dataStarts.clear();
    maxSizes.clear();
    sizes.clear();
    origClauseSizes.clear();
    currentlyUsedSizes.clear();
    origClauseSizes.clear();

    for (uint32_t i = 0; i < newMaxSizes.size(); i++) {
        dataStarts.push(newDataStarts[i]);
        maxSizes.push(newMaxSizes[i]);
        sizes.push(newSizes[i]);
        currentlyUsedSizes.push(newSizes[i]);
    }
    newOrigClauseSizes.moveTo(origClauseSizes);

    if (solver->conf.verbosity >= 3) {
        std::cout << "c Consolidated memory. Time: "
        << cpuTime() - myTime << std::endl;
    }
}

void ClauseAllocator::putClausesIntoDatastruct(std::vector<Clause*>& clauses)
{
    otherClauses.clear();
    threeLongClauses.clear();
    for (uint32_t i = 0; i < clauses.size(); i++) {
        Clause* c = clauses[i];
        if (c->size() <= 3) {
            threeLongClauses.push_back(c);
        } else {
            otherClauses.push_back(c);
        }
    }
}

Clause* ClauseAllocator::getClause()
{
    if (!threeLongClauses.empty()) {
        Clause* tmp = threeLongClauses[threeLongClauses.size()-1];
        threeLongClauses.pop_back();
        return tmp;
    }

    assert(!otherClauses.empty());
    Clause* tmp = otherClauses[otherClauses.size()-1];
    otherClauses.pop_back();
    return tmp;
}

void ClauseAllocator::checkGoodPropBy(const Solver* solver)
{
    const vec<PropBy>& reason = solver->reason;
    Var var = 0;
    for (const PropBy *it = reason.getData(), *end = reason.getDataEnd(); it != end; it++, var++) {
        if ((uint32_t)solver->level[var] > solver->decisionLevel()
            || solver->level[var] == 0
            || solver->value(var) == l_Undef
        ) {
            continue;
        }

        if (it->isClause() && !it->isNULL()) {
            assert(!getPointer(it->getClause())->getFreed());
            assert(!getPointer(it->getClause())->getRemoved());
        }
    }
}


void ClauseAllocator::updateAllOffsetsAndPointers(Solver* solver)
{
    updateOffsets(solver->watches);

    updatePointers(solver->clauses);
    updatePointers(solver->learnts);
    updatePointers(solver->xorclauses);
    updatePointers(solver->freeLater);
    #ifdef ENABLE_UNWIND_GLUE
    updatePointers(solver->unWindGlue);
    #endif //ENABLE_UNWIND_GLUE

    //No need to update varreplacer, since it only stores binary clauses that
    //must have been allocated such as to use the pool
    //updatePointers(solver->varReplacer->clauses, oldToNewPointer);

    #ifdef USE_GAUSS
    for (uint32_t i = 0; i < solver->gauss_matrixes.size(); i++) {
        updatePointers(solver->gauss_matrixes[i]->xorclauses);
        updatePointers(solver->gauss_matrixes[i]->clauses_toclear);
    }
    #endif //USE_GAUSS

    vec<PropBy>& reason = solver->reason;
    Var var = 0;
    for (PropBy *it = reason.getData(), *end = reason.getDataEnd(); it != end; it++, var++) {
        if ((uint32_t)solver->level[var] > solver->decisionLevel()
            || solver->level[var] == 0
            || solver->value(var) == l_Undef) {
            *it = PropBy();
            continue;
        }

        if (it->isClause() && !it->isNULL()) {
            assert(((NewPointerAndOffset*)(getPointer(it->getClause())))->newOffset != std::numeric_limits<uint32_t>::max());
            *it = PropBy(((NewPointerAndOffset*)(getPointer(it->getClause())))->newOffset);
        }
    }
}

/**
@brief A dumb helper function to update offsets
*/
void ClauseAllocator::updateOffsets(vec<vec<Watched> >& watches)
{
    for (uint32_t i = 0;  i < watches.size(); i++) {
        vec<Watched>& list = watches[i];
        for (vec<Watched>::iterator it = list.getData(), end = list.getDataEnd(); it != end; it++) {
            if (!it->isClause() && !it->isXorClause()) continue;
            if (it->isClause()) {
                it->setNormOffset(((NewPointerAndOffset*)(getPointer(it->getNormOffset())))->newOffset);
            } else {
                it->setXorOffset(((NewPointerAndOffset*)(getPointer(it->getXorOffset())))->newOffset);
            }
        }
    }
}

/**
@brief A dumb helper function to update pointers
*/
template<class T>
void ClauseAllocator::updatePointers(vec<T*>& toUpdate)
{
    for (T **it = toUpdate.getData(), **end = toUpdate.getDataEnd(); it != end; it++) {
        if (*it != NULL) {
            *it = (T*)(((NewPointerAndOffset*)(*it))->newPointer);
        }
    }
}

/**
@brief A dumb helper function to update pointers
*/
void ClauseAllocator::updatePointers(vector<Clause*>& toUpdate)
{
    for (vector<Clause*>::iterator it = toUpdate.begin(), end = toUpdate.end(); it != end; it++) {
        *it = (((NewPointerAndOffset*)(*it))->newPointer);
    }
}

/**
@brief A dumb helper function to update pointers
*/
void ClauseAllocator::updatePointers(vector<XorClause*>& toUpdate)
{
    for (vector<XorClause*>::iterator it = toUpdate.begin(), end = toUpdate.end(); it != end; it++) {
        *it = (XorClause*)(((NewPointerAndOffset*)(*it))->newPointer);
    }
}

/**
@brief A dumb helper function to update pointers
*/
void ClauseAllocator::updatePointers(vector<pair<Clause*, uint32_t> >& toUpdate)
{
    for (vector<pair<Clause*, uint32_t> >::iterator it = toUpdate.begin(), end = toUpdate.end(); it != end; it++) {
        it->first = (((NewPointerAndOffset*)(it->first))->newPointer);
    }
}
