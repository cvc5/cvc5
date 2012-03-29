/****************************************************************************************[Solver.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
glucose -- Gilles Audemard, Laurent Simon (2008)

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#define release_assert(a) \
    do { \
        if (!(a)) {\
            fprintf(stderr, "*** ASSERTION FAILURE in %s() [%s:%d]: %s\n", \
            __FUNCTION__, __FILE__, __LINE__, #a); \
            abort(); \
        } \
    } while (0)

///////////////////
// Settings (magic constants)
///////////////////

//#define DUMP_STATS_FULL
//#define DUMP_STATS

//#define DEBUG_UNCHECKEDENQUEUE_LEVEL0

#ifdef DUMP_STATS_FULL
#define DUMP_STATS
#endif //DUMP_STATS_FULL

//Parameters for learnt-clause cleaning
#define RATIOREMOVECLAUSES 1.0/2.0
#define NBCLAUSESBEFOREREDUCE 20000

#define FIXCLEANREPLACE 30U
#define PERCENTAGEPERFORMREPLACE 0.003
#define PERCENTAGECLEANCLAUSES 0.01

//Parameters for xor-finding (binary and non-binary)
#define MAX_CLAUSENUM_XORFIND 1500000
#define BINARY_TO_XOR_APPROX 6.0

#define UPDATE_TRANSOTFSSR_CACHE 200000

//Parameters controlling simplification rounds
#define SIMPLIFY_MULTIPLIER 300
#define SIMPLIFY_MULTIPLIER_MULTIPLIER 1.5
#define MAX_CONFL_BETWEEN_SIMPLIFY 500000
#define BURST_SEARCH
#define NUM_CONFL_BURST_SEARCH 500

//Parameters controlling full restarts
#define FULLRESTART_MULTIPLIER 250
#define FULLRESTART_MULTIPLIER_MULTIPLIER 3.5
#define RESTART_TYPE_DECIDER_FROM 2
#define RESTART_TYPE_DECIDER_UNTIL 7

//Gaussian elimination parameters
#define MIN_GAUSS_XOR_CLAUSES 5
#define MAX_GAUSS_XOR_CLAUSES 30000

//Parameters regarding glues
#define DEFAULT_MAX_GLUE 24
#define MAX_GLUE_BITS 7
#define MAX_THEORETICAL_GLUE ((uint32_t)((1 << MAX_GLUE_BITS)-1))
#define MIN_GLUE_RESTART 100

#ifndef DUMP_STATS_FULL
#define DYNAMICALLY_UPDATE_GLUE
#endif //DUMP_STATS_FULL

//#define ENABLE_UNWIND_GLUE

//Parameters for syncing between threads
#define SYNC_EVERY_CONFL 6000

///////////////////
// Verbose Debug
///////////////////

//#define VERBOSE_DEBUG_XOR
//#define VERBOSE_DEBUG
#ifdef VERBOSE_DEBUG
#define SILENT_DEBUG
#define DEBUG_USELESS_LEARNT_BIN_REMOVAL
#define DEBUG_ATTACH_FULL
#endif


///////////////////
// Silent Debug
///////////////////

#ifndef NDEBUG
#define SILENT_DEBUG
#endif

#ifdef SILENT_DEBUG
#define DEBUG_VARELIM
#define DEBUG_PROPAGATEFROM
#define DEBUG_WATCHED
#define DEBUG_ATTACH
#define DEBUG_REPLACER
//#define DEBUG_USELESS_LEARNT_BIN_REMOVAL
#endif

//#define MORE_DEBUG

#ifdef MORE_DEBUG
#define DEBUG_ATTACH_FULL
#define DEBUG_FAILEDLIT
#define DEBUG_HYPERBIN
#endif

///////////////////
//  For Automake tools
///////////////////

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif //HAVE_CONFIG_H

#ifdef _MSC_VER
#define __builtin_prefetch
#endif //_MSC_VER
