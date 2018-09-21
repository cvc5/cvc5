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

#ifndef NO_MUTEX_H
#define NO_MUTEX_H

namespace std {
    struct mutex {
        void lock() {}
        void unlock() {}
    };

    static const bool memory_order_relaxed = true;
    static const bool memory_order_acquire = true;

    inline void atomic_thread_fence(bool)
    {}

    template<class T>
    struct atomic {
        atomic()
        {}

        atomic(bool _val) :
        val(_val)
        {}

        void store(bool _val, bool) {
            val = _val;
        }
        bool load(bool) const {
            return val;
        }
        operator bool() {
            return val;
        }
        T val;
    };
}

#endif //NO_MUTEX_H
