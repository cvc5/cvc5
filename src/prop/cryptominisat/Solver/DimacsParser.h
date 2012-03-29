/*****************************************************************************
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

Original code by MiniSat authors are under an MIT licence.
Modifications for CryptoMiniSat are under GPLv3 licence.
******************************************************************************/

#ifndef DIMACSPARSER_H
#define DIMACSPARSER_H

#include <stdexcept>
#include <string>
#include "SolverTypes.h"
#include "constants.h"
#include "StreamBuffer.h"
#include "Vec.h"

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#ifndef DISABLE_ZLIB
#include <zlib.h>
#endif // DISABLE_ZLIB

namespace CMSat {

class Solver;

class DimacsParseError : public std::runtime_error
{
    public:
        explicit DimacsParseError(const std::string& arg);
        virtual ~DimacsParseError() throw();
};

/**
@brief Parses up a DIMACS file that my be zipped
*/
class DimacsParser
{
    public:
        DimacsParser(Solver* solver, const bool debugLib, const bool debugNewVar, const bool grouping, const bool addAsLearnt = false);

        template <class T>
        void parse_DIMACS(T input_stream);

    private:
        void parse_DIMACS_main(StreamBuffer& in);
        void skipWhitespace(StreamBuffer& in);
        void skipLine(StreamBuffer& in);
        std::string untilEnd(StreamBuffer& in);
        int32_t parseInt(StreamBuffer& in, uint32_t& len) throw (DimacsParseError);
        float parseFloat(StreamBuffer& in) throw (DimacsParseError);
        void parseString(StreamBuffer& in, std::string& str);
        void readClause(StreamBuffer& in, vec<Lit>& lits) throw (DimacsParseError);
        void parseClauseParameters(StreamBuffer& in, bool& learnt, uint32_t& glue, float& miniSatAct);
        void readFullClause(StreamBuffer& in) throw (DimacsParseError);
        void readBranchingOrder(StreamBuffer& in);
        bool match(StreamBuffer& in, const char* str);
        void printHeader(StreamBuffer& in) throw (DimacsParseError);
        void parseComments(StreamBuffer& in, const std::string str) throw (DimacsParseError);
        std::string stringify(uint32_t x);


        Solver *solver;
        const bool debugLib;
        const bool debugNewVar;
        const bool grouping;
        const bool addAsLearnt;

        uint32_t debugLibPart; ///<printing partial solutions to debugLibPart1..N.output when "debugLib" is set to TRUE
        vec<Lit> lits; ///<To reduce temporary creation overhead
        uint32_t numLearntClauses; ///<Number of learnt non-xor clauses added
        uint32_t numNormClauses; ///<Number of non-learnt, non-xor claues added
        uint32_t numXorClauses; ///<Number of non-learnt xor clauses added
};

}

#endif //DIMACSPARSER_H
