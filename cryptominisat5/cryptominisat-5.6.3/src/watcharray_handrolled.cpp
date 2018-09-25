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

#include "watcharray.h"
#include <algorithm>
using namespace CMSat;

void watch_array::consolidate()
{
    size_t total_needed = total_needed_during_consolidate();

    vector<Mem> newmems;
    size_t at_watches = 0;
    //size_t last_needed = 0;
    while(total_needed > 0) {
        Mem newmem;
        size_t needed = std::min<size_t>(total_needed, WATCH_MAX_SIZE_ONE_ALLOC);
        assert(needed > 0);

        //If last one was larger than this, let's take the last one
        //needed = std::max<size_t>(needed, last_needed/2);
        //last_needed = needed;
        total_needed -= needed;

        newmem.alloc = needed;
        newmem.base_ptr = (Watched*)malloc(newmem.alloc*sizeof(Watched));
        for(; at_watches < watches.size(); at_watches++) {
            //Not used
            if (watches[at_watches].size == 0) {
                watches[at_watches] = Elem();
                continue;
            }

            Elem& ws = watches[at_watches];

            //Allow for some space to breathe
            size_t toalloc = extra_space_during_consolidate(ws.size);

            //Does not fit into this 'newmem'
            if (newmem.next_space_offset + toalloc > newmem.alloc) {
                break;
            }

            ws.alloc = toalloc;
            Watched* orig_ptr = mems[ws.num].base_ptr + ws.offset;
            Watched* new_ptr = newmem.base_ptr + newmem.next_space_offset;
            memmove(new_ptr, orig_ptr, ws.size * sizeof(Watched));
            ws.num = newmems.size();
            ws.offset = newmem.next_space_offset;
            //ws.accessed = 0;
            newmem.next_space_offset += ws.alloc;
        }
        newmems.push_back(newmem);
    }
    assert(at_watches == watches.size());
    assert(total_needed == 0);

    for(size_t i = 0; i < mems.size(); i++) {
        free(mems[i].base_ptr);
    }

    mems = newmems;
    for(auto& mem: free_mem) {
        mem.clear();
    }
    free_mem_used = 0;
    free_mem_not_used = 0;
}

void watch_array::print_stat(bool detailed) const
{
    cout
    << "c [watch] mems.size(): " << mems.size()
    << " free mem used/unused:"
    << free_mem_used << "/" << free_mem_not_used
    << " ("
    << std::fixed << std::setprecision(2)
    << stats_line_percent(free_mem_used, free_mem_not_used+free_mem_used)
    << "%)"
    << endl;

    if (detailed) {
        for(size_t i = 0; i < mems.size(); i++) {
            const Mem& mem = mems[i];
            cout
            << " c [watch] mem " << i
            << " alloc: " << mem.alloc
            << " next_space_offset: " << mem.next_space_offset
            << " base_ptr: " << mem.base_ptr
            << endl;
        }

            cout << "c [watch] free stats:" << endl;
            for(size_t i = 0; i < free_mem.size(); i++)
            {
                cout << "c [watch] ->free_mem[" << i << "]: " << free_mem[i].size() << endl;
            }
        }

    /*for(size_t i = 0; i < watches.size(); i++) {
        cout << "ws[" << i << "] accessed: " << watches[i].accessed << " size: " << watches[i].size << endl;
    }*/
}
