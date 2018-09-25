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


#ifndef SOLVERTYPES_H
#define SOLVERTYPES_H

#include "constants.h"

#include <sstream>
#include <algorithm>
#include <limits>
#include <vector>
#include <iostream>
#include <iomanip>
#include <string>
#include <limits>
#include <cassert>
#include "solverconf.h"
#include "cryptominisat5/solvertypesmini.h"

namespace CMSat {

using std::vector;
using std::cout;
using std::endl;
using std::string;

enum class gret{confl, unit_confl, prop, unit_prop, nothing, nothing_fnewwatch};

inline std::string restart_type_to_string(const Restart type)
{
    switch(type) {
        case Restart::glue:
            return "glue-based";

        case Restart::geom:
            return "geometric";

        case Restart::luby:
            return "luby";

        case Restart::glue_geom:
            return "switch-glue-geom";

        case Restart::never:
            return "never restart";
    }

    assert(false && "oops, one of the restart types has no string name");

    return "Ooops, undefined!";
}

inline std::string restart_type_to_short_string(const Restart type)
{
    switch(type) {
        case Restart::glue:
            return "glue";

        case Restart::geom:
            return "geom";

        case Restart::luby:
            return "luby";

        case Restart::glue_geom:
            return "gl/geo";

        case Restart::never:
            return "never";
    }

        assert(false && "oops, one of the restart types has no string name");

        return "ERR: undefined!";
}

//Removed by which algorithm. NONE = not eliminated
enum class Removed : unsigned char {
    none
    , elimed
    , replaced
    , decomposed
};

inline std::string removed_type_to_string(const Removed removed) {
    switch(removed) {
        case Removed::none:
            return "not removed";

        case Removed::elimed:
            return "variable elimination";

        case Removed::replaced:
            return "variable replacement";

        case Removed::decomposed:
            return "decomposed into another component";
    }

    assert(false && "oops, one of the elim types has no string name");
    return "Oops, undefined!";
}

class BinaryClause {
    public:
        BinaryClause(const Lit _lit1, const Lit _lit2, const bool _red) :
            lit1(_lit1)
            , lit2(_lit2)
            , red(_red)
        {
            if (lit1 > lit2) std::swap(lit1, lit2);
        }

        bool operator<(const BinaryClause& other) const
        {
            if (lit1 < other.lit1) return true;
            if (lit1 > other.lit1) return false;

            if (lit2 < other.lit2) return true;
            if (lit2 > other.lit2) return false;
            return (red && !other.red);
        }

        bool operator==(const BinaryClause& other) const
        {
            return (lit1 == other.lit1
                    && lit2 == other.lit2
                    && red == other.red);
        }

        const Lit getLit1() const
        {
            return lit1;
        }

        const Lit getLit2() const
        {
            return lit2;
        }

        bool isRed() const
        {
            return red;
        }

    private:
        Lit lit1;
        Lit lit2;
        bool red;
};


inline std::ostream& operator<<(std::ostream& os, const BinaryClause val)
{
    os << val.getLit1() << " , " << val.getLit2()
    << " red: " << std::boolalpha << val.isRed() << std::noboolalpha;
    return os;
}

inline double ratio_for_stat(double a, double b)
{
    if (b == 0)
        return 0;
    return a/b;
}

inline double stats_line_percent(double num, double total)
{
    if (total == 0) {
        return 0;
    } else {
        return num/total*100.0;
    }
}

inline void print_value_kilo_mega(const uint64_t value)
{
    if (value > 20*1000ULL*1000ULL) {
        cout << " " << std::setw(4) << value/(1000ULL*1000ULL) << "M";
    } else if (value > 20ULL*1000ULL) {
        cout << " " << std::setw(4) << value/1000 << "K";
    } else {
        cout << " " << std::setw(5) << value;
    }
}

template<class T, class T2> void print_stats_line(
    string left
    , T value
    , T2 value2
    , string extra
) {
    cout
    << std::fixed << std::left << std::setw(27) << left
    << ": " << std::setw(11) << std::setprecision(2) << value
    << " (" << std::left << std::setw(9) << std::setprecision(2) << value2
    << " " << extra << ")"
    << std::right
    << endl;
}

inline void print_stats_line(
    string left
    , uint64_t value
    , uint64_t value2
    , uint64_t value3
) {
    cout
    << std::fixed << std::left << std::setw(27) << left
    << ": " << std::setw(11) << std::setprecision(2) << value
    << "/" << value2
    << "/" << value3
    << std::right
    << endl;
}

template<class T, class T2> void print_stats_line(
    string left
    , T value
    , string extra1
    , T2 value2
    , string extra2
) {
    cout
    << std::fixed << std::left << std::setw(27) << left
    << ": " << std::setw(11) << std::setprecision(2) << value
    << " " << extra1
    << " (" << std::left << std::setw(9) << std::setprecision(2) << value2
    << " " << extra2 << ")"
    << std::right
    << endl;
}

template<class T> void print_stats_line(
    string left
    , T value
    , string extra = ""
) {
    cout
    << std::fixed << std::left << std::setw(27) << left
    << ": " << std::setw(11) << std::setprecision(2)
    << value
    << " " << extra
    << std::right
    << endl;
}

struct AssignStats
{
    AssignStats() :
        sumAssignPos(0)
        , sumAssignNeg(0)
        , sumFlippedPolar(0)
        , sumFlippedPolarByDecider(0)
    {}

    uint64_t sumAssignPos;
    uint64_t sumAssignNeg;
    uint64_t sumFlippedPolar;
    uint64_t sumFlippedPolarByDecider;

};

struct PropStats
{
    void clear()
    {
        PropStats tmp;
        *this = tmp;
    }

    PropStats& operator+=(const PropStats& other)
    {
        propagations += other.propagations;
        bogoProps += other.bogoProps;
        otfHyperTime += other.otfHyperTime;
        otfHyperPropCalled += other.otfHyperPropCalled;
        #ifdef STATS_NEEDED
        propsUnit += other.propsUnit;
        propsBinIrred += other.propsBinIrred;
        propsBinRed += other.propsBinRed;
        propsLongIrred += other.propsLongIrred;
        propsLongRed += other.propsLongRed;

        //Var settings
        varSetPos += other.varSetPos;
        varSetNeg += other.varSetNeg;
        varFlipped += other.varFlipped;
        #endif

        return *this;
    }

    PropStats& operator-=(const PropStats& other)
    {
        propagations -= other.propagations;
        bogoProps -= other.bogoProps;
        otfHyperTime -= other.otfHyperTime;
        otfHyperPropCalled -= other.otfHyperPropCalled;
        #ifdef STATS_NEEDED
        propsUnit -= other.propsUnit;
        propsBinIrred -= other.propsBinIrred;
        propsBinRed -= other.propsBinRed;
        propsLongIrred -= other.propsLongIrred;
        propsLongRed -= other.propsLongRed;

        //Var settings
        varSetPos -= other.varSetPos;
        varSetNeg -= other.varSetNeg;
        varFlipped -= other.varFlipped;
        #endif

        return *this;
    }

    PropStats operator-(const PropStats& other) const
    {
        PropStats result = *this;
        result -= other;
        return result;
    }

    PropStats operator+(const PropStats& other) const
    {
        PropStats result = *this;
        result += other;
        return result;
    }

    void print(const double cpu_time) const
    {
        cout << "c PROP stats" << endl;
        print_stats_line("c Mbogo-props", (double)bogoProps/(1000.0*1000.0)
            , ratio_for_stat(bogoProps, cpu_time*1000.0*1000.0)
            , "/ sec"
        );

        print_stats_line("c MHyper-props", (double)otfHyperTime/(1000.0*1000.0)
            , ratio_for_stat(otfHyperTime, cpu_time*1000.0*1000.0)
            , "/ sec"
        );

        print_stats_line("c Mprops", (double)propagations/(1000.0*1000.0)
            , ratio_for_stat(propagations, cpu_time*1000.0*1000.0)
            , "/ sec"
        );

        #ifdef STATS_NEEDED
        print_stats_line("c propsUnit", propsUnit
            , stats_line_percent(propsUnit, propagations)
            , "% of propagations"
        );

        print_stats_line("c propsBinIrred", propsBinIrred
            , stats_line_percent(propsBinIrred, propagations)
            , "% of propagations"
        );

        print_stats_line("c propsBinRed", propsBinRed
            , stats_line_percent(propsBinRed, propagations)
            , "% of propagations"
        );

        print_stats_line("c propsLongIrred", propsLongIrred
            , stats_line_percent(propsLongIrred, propagations)
            , "% of propagations"
        );

        print_stats_line("c propsLongRed", propsLongRed
            , stats_line_percent(propsLongRed, propagations)
            , "% of propagations"
        );

        print_stats_line("c varSetPos", varSetPos
            , stats_line_percent(varSetPos, propagations)
            , "% of propagations"
        );

        print_stats_line("c varSetNeg", varSetNeg
            , stats_line_percent(varSetNeg, propagations)
            , "% of propagations"
        );

        print_stats_line("c flipped", varFlipped
            , stats_line_percent(varFlipped, propagations)
            , "% of propagations"
        );
        #endif

    }

    uint64_t propagations = 0; ///<Number of propagations made
    uint64_t bogoProps = 0;    ///<An approximation of time
    uint64_t otfHyperTime = 0;
    uint32_t otfHyperPropCalled = 0;

    #ifdef STATS_NEEDED
    //Stats for propagations
    uint64_t propsUnit = 0;
    uint64_t propsBinIrred = 0;
    uint64_t propsBinRed = 0;
    uint64_t propsLongIrred = 0;
    uint64_t propsLongRed = 0;

    //Var settings
    uint64_t varSetPos = 0;
    uint64_t varSetNeg = 0;
    uint64_t varFlipped = 0;
    #endif
};

enum class ConflCausedBy {
    longirred
    , longred
    , binred
    , binirred
};

struct ConflStats
{
    void clear()
    {
        ConflStats tmp;
        *this = tmp;
    }

    ConflStats& operator+=(const ConflStats& other)
    {
        conflsBinIrred += other.conflsBinIrred;
        conflsBinRed += other.conflsBinRed;
        conflsLongIrred += other.conflsLongIrred;
        conflsLongRed += other.conflsLongRed;

        numConflicts += other.numConflicts;

        return *this;
    }

    ConflStats& operator-=(const ConflStats& other)
    {
        conflsBinIrred -= other.conflsBinIrred;
        conflsBinRed -= other.conflsBinRed;
        conflsLongIrred -= other.conflsLongIrred;
        conflsLongRed -= other.conflsLongRed;

        numConflicts -= other.numConflicts;

        return *this;
    }

    void update(const ConflCausedBy lastConflictCausedBy)
    {
        switch(lastConflictCausedBy) {
            case ConflCausedBy::binirred :
                conflsBinIrred++;
                break;
            case ConflCausedBy::binred :
                conflsBinRed++;
                break;
            case ConflCausedBy::longirred :
                conflsLongIrred++;
                break;
            case ConflCausedBy::longred :
                conflsLongRed++;
                break;
            default:
                assert(false);
        }
    }

    void print_short(double cpu_time, bool do_print_times) const
    {
        //Search stats
        if (!do_print_times) {
            print_stats_line("c conflicts", numConflicts);
        } else {
            print_stats_line("c conflicts", numConflicts
                , ratio_for_stat(numConflicts, cpu_time)
                , "/ sec"
            );
        }
    }

    void print(double cpu_time, bool do_print_times) const
    {
        //Search stats
        cout << "c CONFLS stats" << endl;
        print_short(cpu_time, do_print_times);

        print_stats_line("c conflsBinIrred", conflsBinIrred
            , stats_line_percent(conflsBinIrred, numConflicts)
            , "%"
        );

        print_stats_line("c conflsBinRed", conflsBinRed
            , stats_line_percent(conflsBinRed, numConflicts)
            , "%"
        );

        print_stats_line("c conflsLongIrred" , conflsLongIrred
            , stats_line_percent(conflsLongIrred, numConflicts)
            , "%"
        );

        print_stats_line("c conflsLongRed", conflsLongRed
            , stats_line_percent(conflsLongRed, numConflicts)
            , "%"
        );

        long diff = (long)numConflicts
            - (long)(conflsBinIrred + (long)conflsBinRed
                + (long)conflsLongIrred + (long)conflsLongRed
            );

        if (diff != 0) {
            cout
            << "c DEBUG"
            << "((int)numConflicts - (int)(conflsBinIrred + conflsBinRed"
            << endl
            << "c  + conflsLongIrred + conflsLongRed)"
            << " = "
            << (((int)numConflicts - (int)(conflsBinIrred + conflsBinRed
                + conflsLongIrred + conflsLongRed)))
            << endl;

            //assert(diff == 0);
        }
    }

    uint64_t conflsBinIrred = 0;
    uint64_t conflsBinRed = 0;
    uint64_t conflsLongIrred = 0;
    uint64_t conflsLongRed = 0;

    ///Number of conflicts
    uint64_t  numConflicts = 0;
};

inline void orderLits(
    Lit& lit1
    , Lit& lit2
    , Lit& lit3
 ) {
    if (lit1 > lit3)
        std::swap(lit1, lit3);

    if (lit1 > lit2)
        std::swap(lit1, lit2);

    if (lit2 > lit3)
        std::swap(lit2, lit3);

    //They are now ordered
    assert(lit1 < lit2);
    assert(lit2 < lit3);
}

inline vector<Lit> sortLits(const vector<Lit>& lits)
{
    vector<Lit> tmp(lits);

    std::sort(tmp.begin(), tmp.end());
    return tmp;
}

template<typename T>
inline vector<Lit> vars_to_lits(const T& vars)
{
    vector<Lit> ret;
    for(uint32_t var: vars) {
        ret.push_back(Lit(var, false));
    }
    return ret;
}

inline double float_div(const double a, const double b)
{
    if (b != 0)
        return a/b;

    return 0;
}

} //end namespace

#endif //SOLVERTYPES_H
