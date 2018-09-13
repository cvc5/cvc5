/*************************************************************
MiniSat       --- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat --- Copyright (c) 2014, Mate Soos

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
***************************************************************/

#include <string.h>
#include "cryptominisat5/cryptominisat.h"
#include "dimacsparser.h"

struct MyText {
    const unsigned char* txt = 0;
    size_t size = 0;
    size_t at = 0;
};

typedef size_t(*fread_op_text)(void*, size_t, size_t, MyText&);

using namespace CMSat;

static size_t text_read(void* buf, size_t num, size_t count, MyText& f)
{
    if (f.size == f.at) {
        return EOF;
    }

    size_t toread = num*count;
    if (toread > f.size-f.at) {
        toread = f.size-f.at;
    }
    memcpy(buf, f.txt + f.at, toread);
    //cout << "read in" << toread << endl;
    f.at += toread;

    return toread;
}

extern "C" int LLVMFuzzerTestOneInput(const unsigned char *data, size_t size) {
    SATSolver S;
    S.set_verbosity(0);
    //solver->set_num_threads(num_threads);

    DimacsParser<StreamBuffer<MyText, fread_op_text, text_read> > parser(&S, "", 0);
    parser.max_var = 1000;
    MyText t;
    t.at = 0;
    t.size = size;
    t.txt = data;
    if (!parser.parse_DIMACS(t)) {
        return 0;
    }
    S.solve();
    //cout << "Ret is sat: " << (ret == l_True) << endl;
    return 0;
}
