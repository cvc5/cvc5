/*********************************************************
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

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
***********************************************************/

#ifndef TIME_MEM_H
#define TIME_MEM_H
#include "constants.h"
#include <cassert>
#include <time.h>

#include <ios>
#include <iostream>
#include <fstream>
#include <string>
#include <signal.h>

// note: MinGW64 defines both __MINGW32__ and __MINGW64__
#if defined (_MSC_VER) || defined (__MINGW32__) || defined(_WIN32)
#include <ctime>
static inline double cpuTime(void)
{
    return (double)clock() / CLOCKS_PER_SEC;
}
static inline double cpuTimeTotal(void)
{
    return (double)clock() / CLOCKS_PER_SEC;
}

#else //_MSC_VER
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

static inline double cpuTime(void)
{
    struct rusage ru;
    #ifdef RUSAGE_THREAD
    int ret = getrusage(RUSAGE_THREAD, &ru);
    #else
    int ret = getrusage(RUSAGE_SELF, &ru);
    #endif

    //NOTE: This is needed because Windows' Linux subsystem returns non-zero
    //and I can't figure out a way to detect Windows.
    if (ret != 0) {
        return (double)clock() / CLOCKS_PER_SEC;
    }

    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000.0;
}

static inline double cpuTimeTotal(void)
{
    struct rusage ru;
    int ret = getrusage(RUSAGE_SELF, &ru);
    assert(ret == 0);

    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000.0;
}

#endif

#if defined(__linux__)
// process_mem_usage(double &, double &) - takes two doubles by reference,
// attempts to read the system-dependent data for a process' virtual memory
// size and resident set size, and return the results in KB.
//
// On failure, returns 0.0, 0.0
static inline uint64_t memUsedTotal(double& vm_usage)
{
   //double& vm_usage
   using std::ios_base;
   using std::ifstream;
   using std::string;

   vm_usage     = 0.0;

   // 'file' stat seems to give the most reliable results
   //
   ifstream stat_stream("/proc/self/stat",ios_base::in);

   // dummy vars for leading entries in stat that we don't care about
   //
   string pid, comm, state, ppid, pgrp, session, tty_nr;
   string tpgid, flags, minflt, cminflt, majflt, cmajflt;
   string utime, stime, cutime, cstime, priority, nice;
   string O, itrealvalue, starttime;

   // the two fields we want
   //
   unsigned long vsize;
   long rss;

   stat_stream >> pid >> comm >> state >> ppid >> pgrp >> session >> tty_nr
               >> tpgid >> flags >> minflt >> cminflt >> majflt >> cmajflt
               >> utime >> stime >> cutime >> cstime >> priority >> nice
               >> O >> itrealvalue >> starttime >> vsize >> rss; // don't care about the rest

   stat_stream.close();

   long page_size_kb = sysconf(_SC_PAGE_SIZE); // in case x86-64 is configured to use 2MB pages
   vm_usage     = vsize;
   double resident_set = (double)rss * (double)page_size_kb;

   return resident_set;
}
#elif defined(__FreeBSD__)
#include <sys/types.h>
inline uint64_t memUsedTotal(double& vm_usage)
{
    vm_usage = 0;

    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return ru.ru_maxrss*1024;
}
#else //Windows
static inline size_t memUsedTotal(double& vm_usage)
{
    vm_usage = 0;
    return 0;
}
#endif

#endif //TIME_MEM_H
