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

#include "stamp.h"
#include "varupdatehelper.h"

using namespace CMSat;

void Stamp::save_on_var_memory(const uint32_t newNumVars)
{
    tstamp.resize(newNumVars*2);
    tstamp.shrink_to_fit();
}

bool Stamp::stampBasedClRem(
    const vector<Lit>& lits
) const {
    StampSorter sortNorm(tstamp, STAMP_IRRED, false);
    StampSorterInv sortInv(tstamp, STAMP_IRRED, false);

    stampNorm = lits;
    stampInv = lits;

    std::sort(stampNorm.begin(), stampNorm.end(), sortNorm);
    std::sort(stampInv.begin(), stampInv.end(), sortInv);

    #ifdef DEBUG_STAMPING
    cout << "NORM sorted clause: " << stampNorm << endl;
    cout << "Timestamps: ";
    for(Lit l: stampNorm) {
        cout
        << " " << tstamp[l.toInt()].start[STAMP_IRRED]
        << "," << tstamp[l.toInt()].end[STAMP_IRRED];
    }
    cout << endl;

    cout << "INV sorted clause: " << stampInv << endl;
    cout << "Timestamps: ";
    for(Lit l: stampInv) {
        cout
        << " " << tstamp[l.toInt()].start[STAMP_IRRED]
        << "," << tstamp[l.toInt()].end[STAMP_IRRED];
    }
    cout << endl;
    #endif

    assert(lits.size() > 0);
    vector<Lit>::const_iterator lpos = stampNorm.begin();
    vector<Lit>::const_iterator lneg = stampInv.begin();

    while(true) {
        if (tstamp[(~*lneg).toInt()].start[STAMP_IRRED]
            >= tstamp[lpos->toInt()].start[STAMP_IRRED]
        ) {
            lpos++;

            if (lpos == stampNorm.end())
                return false;
        } else if (tstamp[(~*lneg).toInt()].end[STAMP_IRRED]
            <= tstamp[lpos->toInt()].end[STAMP_IRRED]
        ) {
            lneg++;

            if (lneg == stampInv.end())
                return false;
        } else {
            return true;
        }
    }

    assert(false);
}

void Stamp::updateVars(
    const vector<uint32_t>& /*outerToInter*/
    , const vector<uint32_t>& interToOuter2
    , vector<uint16_t>& seen
) {
    //Update the stamp. Stamp can be very large, so update by swapping
    updateBySwap(tstamp, seen, interToOuter2);
}

std::pair<size_t, size_t> Stamp::stampBasedLitRem(
    vector<Lit>& lits
    , StampType stampType
) const {
    size_t remLitTimeStamp = 0;
    StampSorter sorter(tstamp, stampType, true);

    #ifdef DEBUG_STAMPING
    cout << "Ori clause: " << lits << endl;
    #endif

    std::sort(lits.begin(), lits.end(), sorter);

    #ifdef DEBUG_STAMPING
    cout << "sorted clause: " << lits << endl;
    cout << "Timestamps: ";
    for(size_t i = 0; i < lits.size(); i++) {
        cout
        << " " << tstamp[lits[i].toInt()].start[stampType]
        << "," << tstamp[lits[i].toInt()].end[stampType];
    }
    cout << endl;
    #endif

    assert(!lits.empty());
    Lit lastLit = lits[0];
    for(size_t i = 1; i < lits.size(); i++) {
        if (tstamp[lastLit.toInt()].end[stampType]
            < tstamp[lits[i].toInt()].end[stampType]
        ) {
            lits[i] = lit_Undef;
            remLitTimeStamp++;
        } else {
            lastLit = lits[i];
        }
    }

    if (remLitTimeStamp) {
        //First literal cannot be removed
        assert(lits.front() != lit_Undef);

        //At least 1 literal must remain
        assert(remLitTimeStamp < lits.size());

        //Remove lit_Undef-s
        size_t at = 0;
        for(size_t i = 0; i < lits.size(); i++) {
            if (lits[i] != lit_Undef) {
                lits[at++] = lits[i];
            }
        }
        lits.resize(lits.size()-remLitTimeStamp);

        #ifdef DEBUG_STAMPING
        cout << "New clause: " << lits << endl;
        #endif
    }

    size_t remLitTimeStampInv = 0;
    StampSorterInv sorterInv(tstamp, stampType, false);
    std::sort(lits.begin(), lits.end(), sorterInv);
    assert(!lits.empty());
    lastLit = lits[0];

    for(size_t i = 1; i < lits.size(); i++) {
        if (tstamp[(~lastLit).toInt()].end[stampType]
            > tstamp[(~lits[i]).toInt()].end[stampType]
        ) {
            lits[i] = lit_Undef;
            remLitTimeStampInv++;
        } else {
            lastLit = lits[i];
        }
    }

    if (remLitTimeStampInv) {
        //First literal cannot be removed
        assert(lits.front() != lit_Undef);

        //At least 1 literal must remain
        assert(remLitTimeStampInv < lits.size());

        //Remove lit_Undef-s
        size_t at = 0;
        for(size_t i = 0; i < lits.size(); i++) {
            if (lits[i] != lit_Undef) {
                lits[at++] = lits[i];
            }
        }
        lits.resize(lits.size()-remLitTimeStampInv);

        #ifdef DEBUG_STAMPING
        cout << "New clause: " << lits << endl;
        #endif
    }


    return std::make_pair(remLitTimeStamp, remLitTimeStampInv);
}

void Stamp::clearStamps()
{
    for(vector<Timestamp>::iterator
        it = tstamp.begin(), end = tstamp.end()
        ; it != end
        ; ++it
    ) {
        *it = Timestamp();
    }
}
