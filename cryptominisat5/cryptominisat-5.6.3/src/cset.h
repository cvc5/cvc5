/*
Based on SatELite -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
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
#ifndef CSET_H
#define CSET_H

#include <limits>
#include "constants.h"

#include "clause.h"

namespace CMSat {
using std::vector;

/**
@brief Used to quicky add, remove and iterate through a clause set

Used in OccSimplifier to put into a set all clauses that need to be treated
*/
class CSet {
    vector<uint32_t>       where;  ///<Map clause ID to position in 'which'.
    vector<ClOffset>   which;  ///< List of clauses (for fast iteration). May contain 'Clause_NULL'.
    vector<uint32_t>       free;   ///<List of positions holding 'Clause_NULL'.

    public:
        //ClauseSimp& operator [] (uint32_t index) { return which[index]; }
        void reserve(uint32_t size) {
            where.reserve(size);
            which.reserve(size);
        }
        //uint32_t size(void) const { return which.size(); }
        ///@brief Number of elements in the set
        uint32_t nElems(void) const { return which.size() - free.size(); }

        /**
        @brief Add a clause to the set
        */
        bool add(const ClOffset offs) {
            //Don't check for special value
            assert(offs != std::numeric_limits< uint32_t >::max());

            if (where.size() < offs+1)
                where.resize(offs+1, std::numeric_limits<uint32_t>::max());

            if (where[offs] != std::numeric_limits<uint32_t>::max()) {
                return false;
            }
            if (free.size() > 0){
                where[offs] = free.back();
                which[free.back()] = offs;
                free.pop_back();
            }else{
                where[offs] = which.size();
                which.push_back(offs);
            }
            return true;
        }

        bool alreadyIn(const ClOffset offs) const
        {
            //Don't check for special value
            assert(offs != std::numeric_limits< uint32_t >::max());

            if (where.size() < offs+1)
                return false;

            return where[offs] != std::numeric_limits<uint32_t>::max();
        }

        /**
        @brief Fully clear the set
        */
        void clear(void) {
            where.clear();
            which.clear();
            free.clear();
        }

        /**
        @brief A normal iterator to iterate through the set

        No other way exists of iterating correctly.
        */
        class iterator
        {
            public:
                explicit iterator(vector<ClOffset>::iterator _it) :
                it(_it)
                {}

                void operator++()
                {
                    it++;
                }

                bool operator!=(const iterator& iter) const
                {
                    return (it != iter.it);
                }

                ClOffset& operator*() {
                    return *it;
                }

                vector<ClOffset>::iterator& operator->() {
                    return it;
                }
            private:
                vector<ClOffset>::iterator it;
        };

        /**
        @brief A constant iterator to iterate through the set

        No other way exists of iterating correctly.
        */
        class const_iterator
        {
            public:
                explicit const_iterator(vector<ClOffset>::const_iterator _it) :
                it(_it)
                {}

                void operator++()
                {
                    it++;
                }

                bool operator!=(const const_iterator& iter) const
                {
                    return (it != iter.it);
                }

                const ClOffset& operator*() {
                    return *it;
                }

                vector<ClOffset>::const_iterator& operator->() {
                    return it;
                }
            private:
                vector<ClOffset>::const_iterator it;
        };

        ///@brief Get starting iterator
        iterator begin()
        {
            return iterator(which.begin());
        }

        ///@brief Get ending iterator
        iterator end()
        {
            return iterator(which.begin() + which.size());
        }

        ///@brief Get starting iterator (constant version)
        const_iterator begin() const
        {
            return const_iterator(which.begin());
        }

        ///@brief Get ending iterator (constant version)
        const_iterator end() const
        {
            return const_iterator(which.begin() + which.size());
        }
};

} //end namespace

#endif //CSET_H
