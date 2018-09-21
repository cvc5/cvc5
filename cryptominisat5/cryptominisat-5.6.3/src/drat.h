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

#ifndef __DRAT_H__
#define __DRAT_H__

#include "clause.h"
#include <iostream>

namespace CMSat {

enum DratFlag{fin, deldelay, del, findelay, add};

struct Drat
{
    Drat()
    {
    }

    virtual ~Drat()
    {
    }

    virtual bool enabled()
    {
        return false;
    }

    virtual void forget_delay()
    {
    }

    virtual bool get_conf_id() {
        return false;
    }

    virtual bool something_delayed()
    {
        return false;
    }

    #ifdef STATS_NEEDED
    virtual Drat& operator<<(const uint64_t)
    {
        return *this;
    }
    #endif

    virtual Drat& operator<<(const Lit)
    {
        return *this;
    }

    virtual Drat& operator<<(const Clause&)
    {
        return *this;
    }

    virtual Drat& operator<<(const vector<Lit>&)
    {
        return *this;
    }

    virtual Drat& operator<<(const DratFlag)
    {
        return *this;
    }

    virtual void setFile(std::ostream*)
    {
    }

    virtual void flush()
    {
    }

    int buf_len;
    unsigned char* drup_buf = 0;
    unsigned char* buf_ptr;
};

template<bool add_ID>
struct DratFile: public Drat
{
    DratFile()
    {
        drup_buf = new unsigned char[2 * 1024 * 1024];
        buf_ptr = drup_buf;
        buf_len = 0;
        memset(drup_buf, 0, 2 * 1024 * 1024);

        del_buf = new unsigned char[2 * 1024 * 1024];
        del_ptr = del_buf;
        del_len = 0;
    }

    virtual ~DratFile()
    {
        delete[] drup_buf;
        delete[] del_buf;
    }

    #ifdef STATS_NEEDED
    virtual Drat& operator<<(const uint64_t clauseID_or_sumConflicts) override
    {
        if (!id_set) {
            ID = clauseID_or_sumConflicts;
            id_set = true;
        } else {
            sumConflicts = clauseID_or_sumConflicts;
        }
        return *this;
    }
    #endif

    void byteDRUPa(const Lit l)
    {
        unsigned int u = 2 * (l.var() + 1) + l.sign();
        do {
            *buf_ptr++ = (u & 0x7f) | 0x80;
            buf_len++;
            u = u >> 7;
        } while (u);

        // End marker of this unsigned number
        *(buf_ptr - 1) &= 0x7f;
    }

    void byteDRUPaID(const uint64_t id)
    {
        for(unsigned i = 0; i < 6; i++) {
            *buf_ptr++ = (id>>(8*i))&0xff;
            buf_len++;
        }
    }

    void byteDRUPd(const Lit l)
    {
        unsigned int u = 2 * (l.var() + 1) + l.sign();
        do {
            *del_ptr++ = (u & 0x7f) | 0x80;
            del_len++;
            u = u >> 7;
        } while (u);

        // End marker of this unsigned number
        *(del_ptr - 1) &= 0x7f;
    }

    void flush() override
    {
        binDRUP_flush();
    }

    void binDRUP_flush() {
        drup_file->write((const char*)drup_buf, buf_len);
        buf_ptr = drup_buf;
        buf_len = 0;
    }

    void setFile(std::ostream* _file) override
    {
        drup_file = _file;
    }

    bool get_conf_id() override {
        return add_ID;
    }

    bool something_delayed() override
    {
        return delete_filled;
    }

    void forget_delay() override
    {
        del_ptr = del_buf;
        del_len = 0;
        must_delete_next = false;
        delete_filled = false;
    }

    bool enabled() override
    {
        return true;
    }

    int del_len = 0;
    unsigned char* del_buf;
    unsigned char* del_ptr;

    bool delete_filled = false;
    bool must_delete_next = false;

    Drat& operator<<(const Lit lit) override
    {
        if (must_delete_next) {
            byteDRUPd(lit);
        } else {
            byteDRUPa(lit);
        }

        return *this;
    }

    Drat& operator<<(const Clause& cl) override
    {
        if (must_delete_next) {
            for(const Lit l: cl)
                byteDRUPd(l);
        } else {
            for(const Lit l: cl)
                byteDRUPa(l);

            #ifdef STATS_NEEDED
            id_set = true;
            if (is_add && add_ID) {
                ID = cl.stats.ID;

                // actually... for on-the-fly subsumed irred clauses can have an ID.
                //assert(!(ID != 0 && !cl.red()));

                //redundant clauses MUST have a valid ID
                assert(!(ID == 0 && cl.red()));
            }
            #endif
        }

        return *this;
    }

    Drat& operator<<(const vector<Lit>& cl) override
    {
        if (must_delete_next) {
            for(const Lit l: cl)
                byteDRUPd(l);
        } else {
            for(const Lit l: cl)
                byteDRUPa(l);
        }

        return *this;
    }

    Drat& operator<<(const DratFlag flag) override
    {
        switch (flag)
        {
            case DratFlag::fin:
                if (must_delete_next) {
                    *del_ptr++ = 0;
                    del_len++;
                    delete_filled = true;
                } else {
                    *buf_ptr++ = 0;
                    buf_len++;
                    #ifdef STATS_NEEDED
                    if (is_add && add_ID) {
                        byteDRUPaID(ID);
                        ID = 0;
                        id_set = false;

                        assert(sumConflicts != std::numeric_limits<int64_t>::max());
                        byteDRUPaID(sumConflicts);
                        sumConflicts = std::numeric_limits<int64_t>::max();
                    }
                    #endif
                    if (buf_len > 1048576) {
                        binDRUP_flush();
                    }
                }
                must_delete_next = false;
                break;

            case DratFlag::deldelay:
                assert(!delete_filled);
                forget_delay();
                *del_ptr++ = 'd';
                del_len++;
                delete_filled = false;
                must_delete_next = true;
                break;

            case DratFlag::findelay:
                assert(delete_filled);
                memcpy(buf_ptr, del_buf, del_len);
                buf_len += del_len;
                buf_ptr += del_len;
                if (buf_len > 1048576) {
                    binDRUP_flush();
                }

                forget_delay();
                break;

            case DratFlag::add:
                #ifdef STATS_NEEDED
                is_add = true;
                ID = 0;
                id_set = false;
                sumConflicts = std::numeric_limits<int64_t>::max();
                #endif
                *buf_ptr++ = 'a';
                buf_len++;
                break;

            case DratFlag::del:
                #ifdef STATS_NEEDED
                is_add = false;
                ID = 0;
                id_set = false;
                #endif
                forget_delay();
                *buf_ptr++ = 'd';
                buf_len++;
                break;
        }

        return *this;
    }

    std::ostream* drup_file = NULL;
    #ifdef STATS_NEEDED
    int64_t ID = 0;
    int64_t sumConflicts = std::numeric_limits<int64_t>::max();
    bool is_add = true;
    bool id_set = false;
    #endif
};

}

#endif //__DRAT_H__
