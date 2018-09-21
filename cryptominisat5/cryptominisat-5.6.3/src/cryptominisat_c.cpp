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

#include "cryptominisat5/cryptominisat_c.h"
#include "constants.h"
#include "cryptominisat5/cryptominisat.h"


// C wrappers for SATSolver so that it can be used from other languages (e.g. Rust)
using namespace CMSat;

// Make sure the types we expose are C compatible and don't change unexpectedly
static_assert(sizeof(Lit) == sizeof(c_Lit), "Lit layout not c-compatible");
static_assert(alignof(Lit) == alignof(c_Lit), "Lit layout not c-compatible");
static_assert(sizeof(lbool) == sizeof(c_lbool), "lbool layout not c-compatible");
static_assert(alignof(lbool) == alignof(c_lbool), "lbool layout not c-compatible");

const Lit* fromc(const c_Lit* x)
{
    return reinterpret_cast<const Lit*>(x);
}
const lbool* fromc(const c_lbool* x)
{
    return reinterpret_cast<const lbool*>(x);
}
const c_lbool* toc(const lbool* x)
{
    return reinterpret_cast<const c_lbool*>(x);
}
const c_Lit* toc(const Lit* x)
{
    return reinterpret_cast<const c_Lit*>(x);
}
c_lbool toc(lbool x)
{
    return {x.getValue()};
}

template<typename T>
std::vector<T> wrap(const T* vals, size_t num_vals)
{
    return std::vector<T>(vals, vals + num_vals);
}

template<typename Dest, typename T>
Dest unwrap(const std::vector<T>& vec)
{
    return Dest {toc(vec.data()), vec.size()};
}

#define NOEXCEPT_START noexcept { try {
#define NOEXCEPT_END } catch(...) { \
    std::cerr << "ERROR: exception thrown past FFI boundary" << std::endl;\
    std::exit(-1);\
} }

extern "C"
{

    DLL_PUBLIC SATSolver* cmsat_new(void) NOEXCEPT_START {
            return new SATSolver();
    } NOEXCEPT_END

    DLL_PUBLIC void cmsat_free(SATSolver* s) NOEXCEPT_START {
        delete s;
    } NOEXCEPT_END

    DLL_PUBLIC unsigned cmsat_nvars(const SATSolver* self) NOEXCEPT_START {
        return self->nVars();
    } NOEXCEPT_END

    DLL_PUBLIC bool cmsat_add_clause(SATSolver* self, const c_Lit* lits, size_t num_lits) NOEXCEPT_START {
        return self->add_clause(wrap(fromc(lits), num_lits));
    } NOEXCEPT_END

    DLL_PUBLIC bool cmsat_add_xor_clause(SATSolver* self, const unsigned* vars, size_t num_vars, bool rhs) NOEXCEPT_START {
        return self->add_xor_clause(wrap(vars, num_vars), rhs);
    } NOEXCEPT_END

    DLL_PUBLIC void cmsat_new_vars(SATSolver* self, const size_t n) NOEXCEPT_START {
        self->new_vars(n);
    } NOEXCEPT_END

    DLL_PUBLIC c_lbool cmsat_solve(SATSolver* self) NOEXCEPT_START {
        return toc(self->solve(nullptr));
    } NOEXCEPT_END

    DLL_PUBLIC c_lbool cmsat_solve_with_assumptions(SATSolver* self, const c_Lit* assumptions, size_t num_assumptions) NOEXCEPT_START {
        auto temp = wrap(fromc(assumptions), num_assumptions);
        return toc(self->solve(&temp));
    } NOEXCEPT_END

    DLL_PUBLIC slice_lbool cmsat_get_model(const SATSolver* self) NOEXCEPT_START {
        return unwrap<slice_lbool>(self->get_model());
    } NOEXCEPT_END

    DLL_PUBLIC slice_Lit cmsat_get_conflict(const SATSolver* self) NOEXCEPT_START {
        return unwrap<slice_Lit>(self->get_conflict());
    } NOEXCEPT_END

//Setup
    DLL_PUBLIC void cmsat_set_num_threads(SATSolver* self, unsigned n) NOEXCEPT_START {
        self->set_num_threads(n);
    } NOEXCEPT_END
}
