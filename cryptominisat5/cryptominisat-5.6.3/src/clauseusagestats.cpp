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

#include "clauseusagestats.h"

#include <iostream>
#include <iomanip>

using std::cout;
using std::endl;

using namespace CMSat;

void ClauseUsageStats::print() const
{
    cout
    #ifdef STATS_NEEDED
    << " cls visit: "
    << std::setw(7) << sumLookedAt/1000UL
    << "K"
    #endif

    << " prop: "
    << std::setw(5) << sumProp/1000UL
    << "K"

    << " conf: "
    << std::setw(5) << sumConfl/1000UL
    << "K"

    << " UIP used: "
    << std::setw(5) << sumUsedUIP/1000UL
    << "K"
    << endl;
}
