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

#include "sqlstats.h"
using namespace CMSat;


#ifndef _MSC_VER
#include <fcntl.h>
#include <unistd.h>
void SQLStats::getRandomID()
{
    //Generate random ID for SQL
    int randomData = open("/dev/urandom", O_RDONLY);
    if (randomData == -1) {
        cout << "Error reading from /dev/urandom !" << endl;
        std::exit(-1);
    }
    ssize_t ret = read(randomData, &runID, sizeof(runID));

    //Can only be <8 bytes long, some PHP-related limit
    //Make it 6-byte long then (good chance to collide after 2^24 entries)
    runID &= 0xffffffULL;

    if (ret != sizeof(runID)) {
        cout << "Couldn't read from /dev/urandom!" << endl;
        std::exit(-1);
    }
    close(randomData);

    if (runID == 0)
        runID = 1;
}
#else
#include <ctime>
void SQLStats::getRandomID()
{
    srand((unsigned) time(NULL));
    runID = rand();
    if (runID == 0) {
        runID = 1;
    }
}
#endif
