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

#ifndef SHARED_DATA_H
#define SHARED_DATA_H

#include "cryptominisat5/solvertypesmini.h"

#include <vector>
#include <mutex>
using std::vector;
using std::mutex;

namespace CMSat {

class SharedData
{
    public:
        SharedData(const uint32_t _num_threads) :
            num_threads(_num_threads)
        {}

        struct Spec {
            Spec() :
                data(new vector<Lit>)
            {}

            Spec(const Spec&) {
                assert(false);
            }
            Spec(Spec&& other)
            #ifndef _MSC_VER
            noexcept
            #endif
            :
                data(std::move(other.data))
            {
                other.data = NULL;
            }
            ~Spec() {
                clear();
            }
            vector<Lit>* data = NULL;

            void clear()
            {
                delete data;
                data = NULL;
            }
        };
        vector<lbool> value;
        vector<Spec> bins;
        std::mutex unit_mutex;
        std::mutex bin_mutex;

        uint32_t num_threads;

        size_t calc_memory_use_bins()
        {
            size_t mem = 0;
            mem += bins.capacity()*sizeof(Spec);
            for(size_t i = 0; i < bins.size(); i++) {
                if (bins[i].data) {
                    mem += bins[i].data->capacity()*sizeof(Lit);
                    mem += sizeof(vector<Lit>);
                }
            }
            return mem;
        }
};

}

#endif //SHARED_DATA_H
