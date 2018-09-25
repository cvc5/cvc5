/******************************************
Copyright (c) 2016, @Storyyeller

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

#pragma once
#include <stddef.h>
#include <stdint.h>

typedef struct c_Lit { uint32_t x; } c_Lit;
typedef struct c_lbool { uint8_t x; } c_lbool;
typedef struct slice_Lit { const c_Lit* vals; size_t num_vals; } slice_Lit;
typedef struct slice_lbool { const c_lbool* vals; size_t num_vals; } slice_lbool;

#ifdef __cplusplus
    #define NOEXCEPT noexcept

    namespace CMSat{ struct SATSolver; }
    using CMSat::SATSolver;

    extern "C" {
#else
    // c stuff
    #include <stdbool.h>
    #define NOEXCEPT

    #define L_TRUE (0u)
    #define L_FALSE (1u)
    #define L_UNDEF (2u)

    // forward declaration
    typedef struct SATSolver SATSolver;
#endif

#if defined _WIN32
    #define CMS_DLL_PUBLIC __declspec(dllexport)
#else
    #define CMS_DLL_PUBLIC __attribute__ ((visibility ("default")))
#endif

CMS_DLL_PUBLIC SATSolver* cmsat_new(void) NOEXCEPT;
CMS_DLL_PUBLIC void cmsat_free(SATSolver* s) NOEXCEPT;

CMS_DLL_PUBLIC unsigned cmsat_nvars(const SATSolver* self) NOEXCEPT;
CMS_DLL_PUBLIC bool cmsat_add_clause(SATSolver* self, const c_Lit* lits, size_t num_lits) NOEXCEPT;
CMS_DLL_PUBLIC bool cmsat_add_xor_clause(SATSolver* self, const unsigned* vars, size_t num_vars, bool rhs) NOEXCEPT;
CMS_DLL_PUBLIC void cmsat_new_vars(SATSolver* self, const size_t n) NOEXCEPT;

CMS_DLL_PUBLIC c_lbool cmsat_solve(SATSolver* self) NOEXCEPT;
CMS_DLL_PUBLIC c_lbool cmsat_solve_with_assumptions(SATSolver* self, const c_Lit* assumptions, size_t num_assumptions) NOEXCEPT;
CMS_DLL_PUBLIC slice_lbool cmsat_get_model(const SATSolver* self) NOEXCEPT;
CMS_DLL_PUBLIC slice_Lit cmsat_get_conflict(const SATSolver* self) NOEXCEPT;

CMS_DLL_PUBLIC void cmsat_set_num_threads(SATSolver* self, unsigned n) NOEXCEPT;

#ifdef __cplusplus
} // end extern c
#endif
