/*
Copyright (c) 2010-2015 Mate Soos
Copyright (c) Kuldeep S. Meel, Daniel J. Fremont

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
*/

#include "main.h"
#include "signalcode.h"
#include <signal.h>
#include <fenv.h>

int main(int argc, char** argv)
{
    #if defined(__GNUC__) && defined(__linux__)
    feenableexcept(FE_INVALID   |
                   FE_DIVBYZERO |
                   FE_OVERFLOW
    );
    #endif

    int ret = -1;
    try {
        Main main(argc, argv);
        main.conf.verbosity = 1;
        main.conf.verbStats = 1;
        main.parseCommandLine();

        signal(SIGINT, SIGINT_handler);
        ret = main.solve();
    } catch (CMSat::TooManyVarsError& e) {
        std::cerr << "ERROR! Variable requested is far too large" << std::endl;
        exit(-1);
    } catch (CMSat::TooLongClauseError& e) {
        std::cerr << "ERROR! Too long clause inserted" << std::endl;
        exit(-1);
    };

    return ret;
}
