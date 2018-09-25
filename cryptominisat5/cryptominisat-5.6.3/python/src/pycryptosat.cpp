/*************
Python bindings to CryptoMiniSat (http://msoos.org)

Copyright (c) 2013, Ilan Schnell, Continuum Analytics, Inc.
              2014, Mate Soos
              2017, Pierre Vignet

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
**********************************/

#include <Python.h>
#include <structmember.h>
#include <limits>
#include <cassert>
#include <cryptominisat5/cryptominisat.h>
using namespace CMSat;

#define MODULE_NAME "pycryptosat"
#define MODULE_DOC "CryptoMiniSAT satisfiability solver."

// Compatibility between Python 2 and 3
#if PY_MAJOR_VERSION >= 3
#define IS_PY3K
#endif

#ifdef IS_PY3K
    #define IS_INT(x)  PyLong_Check(x)

    #define MODULE_INIT_FUNC(name) \
        PyMODINIT_FUNC PyInit_ ## name(void); \
        PyMODINIT_FUNC PyInit_ ## name(void)
#else
    #define IS_INT(x)  (PyInt_Check(x) || PyLong_Check(x))

    #define MODULE_INIT_FUNC(name) \
        static PyObject *PyInit_ ## name(void); \
        PyMODINIT_FUNC init ## name(void); \
        PyMODINIT_FUNC init ## name(void) { PyInit_ ## name(); } \
        static PyObject *PyInit_ ## name(void)
#endif

// Mask "missing initializer for member" warnings in PyTypeObject
#pragma GCC diagnostic ignored "-Wmissing-field-initializers"
// Mask "deprecated conversion from string constant to ‘char*’" warnings in kwlist arrays
#pragma GCC diagnostic ignored "-Wwrite-strings"

// Support for old and end-of-life Python versions
#if PY_MAJOR_VERSION == 2 && PY_MINOR_VERSION <= 5
    #define PyUnicode_FromString  PyString_FromString

    #define PyVarObject_HEAD_INIT(type, size) \
    PyObject_HEAD_INIT(type) size,
#endif
#if PY_MAJOR_VERSION == 2 && PY_MINOR_VERSION <= 6
    #define Py_TYPE(ob) (((PyObject*)(ob))->ob_type)
#endif


typedef struct {
    PyObject_HEAD
    /* Type-specific fields go here. */
    SATSolver* cmsat;
} Solver;

static const char solver_create_docstring[] = \
"Solver(verbose=0, time_limit=max_numeric_limits, confl_limit=max_numeric_limits, threads=1)\n\
Create Solver object.\n\
\n\
:param verbose: Verbosity level: 0: nothing printed; 15: very verbose.\n\
:param time_limit: Propagation limit: abort after this many seconds has elapsed.\n\
:param confl_limit: Propagation limit: abort after this many conflicts.\n\
    Default: never abort.\n\
:param threads: Number of threads to use.\n\
:type verbose: <int>\n\
:type time_limit: <double>\n\
:type confl_limit: <long>\n\
:type threads: <int>";

static SATSolver* setup_solver(PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {"verbose", "time_limit", "confl_limit", "threads", NULL};

    int verbose = 0;
    int num_threads = 1;
    double time_limit = std::numeric_limits<double>::max();
    long confl_limit = std::numeric_limits<long>::max();
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|idli", kwlist, &verbose, &time_limit, &confl_limit, &num_threads)) {
        return NULL;
    }
    if (verbose < 0) {
        PyErr_SetString(PyExc_ValueError, "verbosity must be at least 0");
        return NULL;
    }
    if (time_limit < 0) {
        PyErr_SetString(PyExc_ValueError, "time_limit must be at least 0");
        return NULL;
    }
    if (confl_limit < 0) {
        PyErr_SetString(PyExc_ValueError, "conflict limit must be at least 0");
        return NULL;
    }
    if (num_threads <= 0) {
        PyErr_SetString(PyExc_ValueError, "number of threads must be at least 1");
        return NULL;
    }

    SATSolver *cmsat = new SATSolver;
    cmsat->set_max_time(time_limit);
    cmsat->set_max_confl(confl_limit);
    cmsat->set_verbosity(verbose);
    cmsat->set_num_threads(num_threads);

    return cmsat;
}

static int convert_lit_to_sign_and_var(PyObject* lit, long& var, bool& sign)
{
    if (!IS_INT(lit))  {
        PyErr_SetString(PyExc_TypeError, "integer expected !");
        return 0;
    }

    long val = PyLong_AsLong(lit);
    if (val == 0) {
        PyErr_SetString(PyExc_ValueError, "non-zero integer expected");
        return 0;
    }
    if (val > std::numeric_limits<int>::max()/2
        || val < std::numeric_limits<int>::min()/2
    ) {
        PyErr_Format(PyExc_ValueError, "integer %ld is too small or too large", val);
        return 0;
    }

    sign = (val < 0);
    var = std::abs(val) - 1;

    return 1;
}

static int parse_clause(
    Solver *self
    , PyObject *clause
    , std::vector<Lit>& lits
) {
    PyObject *iterator = PyObject_GetIter(clause);
    if (iterator == NULL) {
        PyErr_SetString(PyExc_TypeError, "iterable object expected");
        return 0;
    }

    PyObject *lit;
    while ((lit = PyIter_Next(iterator)) != NULL) {
        long var;
        bool sign;
        int ret = convert_lit_to_sign_and_var(lit, var, sign);
        Py_DECREF(lit);
        if (!ret) {
            Py_DECREF(iterator);
            return 0;
        }

        if (var >= self->cmsat->nVars()) {
            for(long i = (long)self->cmsat->nVars(); i <= var ; i++) {
                self->cmsat->new_var();
            }
        }

        lits.push_back(Lit(var, sign));
    }
    Py_DECREF(iterator);
    if (PyErr_Occurred()) {
        return 0;
    }

    return 1;
}

static int parse_xor_clause(
    Solver *self
    , PyObject *clause
    , std::vector<uint32_t>& vars
) {
    PyObject *iterator = PyObject_GetIter(clause);
    if (iterator == NULL) {
        PyErr_SetString(PyExc_TypeError, "iterable object expected");
        return 0;
    }

    PyObject *lit;
    while ((lit = PyIter_Next(iterator)) != NULL) {
        long var;
        bool sign;
        int ret = convert_lit_to_sign_and_var(lit, var, sign);
        Py_DECREF(lit);
        if (!ret) {
            Py_DECREF(iterator);
            return 0;
        }
        if (sign) {
            PyErr_SetString(PyExc_ValueError, "XOR clause must contiain only positive variables (not inverted literals)");
            Py_DECREF(iterator);
            return 0;
        }

        if (var >= self->cmsat->nVars()) {
            for(long i = (long)self->cmsat->nVars(); i <= var ; i++) {
                self->cmsat->new_var();
            }
        }

        vars.push_back(var);
    }
    Py_DECREF(iterator);
    if (PyErr_Occurred()) {
        return 0;
    }

    return 1;
}

PyDoc_STRVAR(start_getting_small_clauses_doc,
"EXPERIMENTAL\n\
Start getting clauses."
);
static PyObject* start_getting_small_clauses(Solver *self, PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {"max_len", "max_glue", NULL};

    unsigned max_len;
    unsigned max_glue;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "II", kwlist, &max_len, &max_glue)) {
        return NULL;
    }

    self->cmsat->start_getting_small_clauses(max_len, max_glue);

    Py_INCREF(Py_None);
    return Py_None;
}

PyDoc_STRVAR(get_next_small_clause_doc,
"EXPERIMENTAL\n\
Start getting clauses."
);
static PyObject* get_next_small_clause(Solver *self, PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {NULL};
    PyObject *max_len;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "", kwlist)) {
        return NULL;
    }

    std::vector<Lit> lits;
    bool ret = self->cmsat->get_next_small_clause(lits);
    if (!ret) {
        Py_INCREF(Py_None);
        return Py_None;
    }


    PyObject* list = PyList_New(lits.size());
    for(size_t i = 0; i < lits.size(); i++) {
        Lit l = lits[i];
        long ll = l.var()+1;
        if (l.sign()) {
            ll *= -1;
        }

        PyList_SetItem(list, i, PyLong_FromLong(ll));
    }
    return list;
}


PyDoc_STRVAR(end_getting_small_clauses_doc,
"EXPERIMENTAL\n\
End getting clauses."
);
static PyObject* end_getting_small_clauses(Solver *self, PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {NULL};
    PyObject *max_len;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "", kwlist)) {
        return NULL;
    }
    self->cmsat->end_getting_small_clauses();

    Py_INCREF(Py_None);
    return Py_None;
}

PyDoc_STRVAR(add_clause_doc,
"add_clause(clause)\n\
Add a clause to the solver.\n\
\n\
:param arg1: A clause contains literals (ints)\n\
:return: None\n\
:type arg1: <list>\n\
:rtype: <None>"
);

static PyObject* add_clause(Solver *self, PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {"clause", NULL};
    PyObject *clause;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O", kwlist, &clause)) {
        return NULL;
    }

    std::vector<Lit> lits;
    if (!parse_clause(self, clause, lits)) {
        return 0;
    }
    self->cmsat->add_clause(lits);

    Py_INCREF(Py_None);
    return Py_None;
}

PyDoc_STRVAR(add_clauses_doc,
"add_clauses(clauses)\n\
Add iterable of clauses to the solver.\n\
\n\
:param arg1: List of clauses. Each clause contains literals (ints)\n\
:return: None\n\
:type arg1: <list>\n\
:rtype: <None>"
);

static PyObject* add_clauses(Solver *self, PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {"clauses", NULL};
    PyObject *clauses;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "O", kwlist, &clauses)) {
        return NULL;
    }

    PyObject *iterator = PyObject_GetIter(clauses);
    if (iterator == NULL) {
        PyErr_SetString(PyExc_TypeError, "iterable object expected");
        return NULL;
    }

    PyObject *clause;
    while ((clause = PyIter_Next(iterator)) != NULL) {
        PyObject *arglist = Py_BuildValue("(O)", clause);
        PyObject *ret = add_clause(self, arglist, NULL);
        Py_DECREF(ret);

        /* release reference when done */
        Py_DECREF(arglist);
        Py_DECREF(clause);
    }

    /* release reference when done */
    Py_DECREF(iterator);
    if (PyErr_Occurred()) {
        return NULL;
    }

    Py_INCREF(Py_None);
    return Py_None;
}

static PyObject* add_xor_clause(Solver *self, PyObject *args, PyObject *kwds)
{
    static char* kwlist[] = {"xor_clause", "rhs", NULL};
    PyObject *rhs;
    PyObject *clause;
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "OO", kwlist, &clause, &rhs)) {
        return NULL;
    }
    if (!PyBool_Check(rhs)) {
        PyErr_SetString(PyExc_TypeError, "rhs must be boolean");
        return NULL;
    }
    bool real_rhs = PyObject_IsTrue(rhs);

    std::vector<uint32_t> vars;
    if (!parse_xor_clause(self, clause, vars)) {
        return 0;
    }

    self->cmsat->add_xor_clause(vars, real_rhs);

    Py_INCREF(Py_None);
    return Py_None;
}

static PyObject* get_solution(SATSolver *cmsat)
{
    // Create tuple with the size of number of variables in model
    unsigned max_idx = cmsat->nVars();
    PyObject *tuple = PyTuple_New((Py_ssize_t) max_idx+1);
    if (tuple == NULL) {
        PyErr_SetString(PyExc_SystemError, "failed to create a tuple");
        return NULL;
    }

    Py_INCREF(Py_None);
    PyTuple_SET_ITEM(tuple, (Py_ssize_t)0, Py_None);

    PyObject *py_value = NULL;
    lbool v;
    for (unsigned i = 0; i < max_idx; i++) {
        v = cmsat->get_model()[i];

        if (v == l_True) {
            py_value = Py_True;
        } else if (v == l_False) {
            py_value = Py_False;
        } else if (v == l_Undef) {
            py_value = Py_None;
        } else {
            // v can only be l_False, l_True, l_Undef
            assert((v == l_False) || (v == l_True) || (v == l_Undef));
        }
        Py_INCREF(py_value);
        PyTuple_SET_ITEM(tuple, (Py_ssize_t)i+1, py_value);
    }
    return tuple;
}

static PyObject* get_raw_solution(SATSolver *cmsat) {

    // Create tuple with the size of number of variables in model
    unsigned max_idx = cmsat->nVars();
    PyObject *tuple = PyTuple_New((Py_ssize_t) max_idx);
    if (tuple == NULL) {
        PyErr_SetString(PyExc_SystemError, "failed to create a tuple");
        return NULL;
    }

    // Add each variable in model to the tuple
    PyObject *py_value = NULL;
    int sign;
    for (long var = 0; var != (long)max_idx; var++) {

        if (cmsat->get_model()[var] != l_Undef) {

            sign = (cmsat->get_model()[var] == l_True) ? 1 : -1;

            #ifdef IS_PY3K
            py_value = PyLong_FromLong((var + 1) * sign);
            #else
            py_value = PyInt_FromLong((var + 1) * sign);
            #endif

            PyTuple_SET_ITEM(tuple, (Py_ssize_t)var, py_value);
        }
    }
    return tuple;
}

PyDoc_STRVAR(nb_vars_doc,
"nb_vars()\n\
Return the number of literals in the solver.\n\
\n\
:return: Number of literals\n\
:rtype: <int>"
);

static PyObject* nb_vars(Solver *self)
{
    #ifdef IS_PY3K
    return PyLong_FromLong(self->cmsat->nVars());
    #else
    return PyInt_FromLong(self->cmsat->nVars());
    #endif
}

/*
static PyObject* nb_clauses(Solver *self)
{
    // Private attribute => need to make a public method
    return PyInt_FromLong(self->cmsat->data->solvers.size());
}*/

static int parse_assumption_lits(PyObject* assumptions, SATSolver* cmsat, std::vector<Lit>& assumption_lits)
{
    PyObject *iterator = PyObject_GetIter(assumptions);
    if (iterator == NULL) {
        PyErr_SetString(PyExc_TypeError, "interable object expected");
        return 0;
    }

    PyObject *lit;
    while ((lit = PyIter_Next(iterator)) != NULL) {
        long var;
        bool sign;
        int ret = convert_lit_to_sign_and_var(lit, var, sign);
        Py_DECREF(lit);
        if (!ret) {
            Py_DECREF(iterator);
            return 0;
        }

        if (var >= cmsat->nVars()) {
            Py_DECREF(iterator);
            PyErr_Format(PyExc_ValueError, "Variable %ld not used in clauses", var+1);
            return 0;
        }

        assumption_lits.push_back(Lit(var, sign));
    }
    Py_DECREF(iterator);
    if (PyErr_Occurred()) {
        return 0;
    }

    return 1;
}

PyDoc_STRVAR(solve_doc,
"solve(assumptions=None)\n\
Solve the system of equations that have been added with add_clause();\n\
\n\
.. example:: \n\
    from pycryptosat import Solver\n\
    >>> s = Solver()\n\
    >>> s.add_clause([1])\n\
    >>> s.add_clause([-2])\n\
    >>> s.add_clause([3])\n\
    >>> s.add_clause([-1, 2, 3])\n\
    >>> sat, solution = s.solve()\n\
    >>> print sat\n\
    True\n\
    >>> print solution\n\
    (None, True, False, True)\n\
    \n\
    We can also try to assume any variable values for a single solver run:\n\
    \n\
    sat, solution = s.solve([-3])\n\
    >>> print sat\n\
    False\n\
    >>> print solution\n\
    None\n\
\n\
:param arg1: (Optional) Allows the user to set values to specific variables\n\
    in the solver in a temporary fashion. This means that in case the problem\n\
    is satisfiable but e.g it's unsatisfiable if variable 2 is FALSE, then\n\
    solve([-2]) will return UNSAT. However, a subsequent call to solve() will\n\
    still return a solution.\n\
:type arg1: <list>\n\
:return: A tuple. First part of the tuple indicates whether the problem\n\
    is satisfiable. The second part is a tuple contains the solution,\n\
    preceded by None, so you can index into it with the variable number.\n\
    E.g. solution[1] returns the value for variabe 1.\n\
:rtype: <tuple <tuple>>"
);

static PyObject* solve(Solver *self, PyObject *args, PyObject *kwds)
{
    PyObject* assumptions = NULL;
    static char* kwlist[] = {"assumptions", NULL};
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "|O", kwlist, &assumptions)) {
        return NULL;
    }

    std::vector<Lit> assumption_lits;
    if (assumptions) {
        if (!parse_assumption_lits(assumptions, self->cmsat, assumption_lits)) {
            return 0;
        }
    }

    PyObject *result = PyTuple_New((Py_ssize_t) 2);
    if (result == NULL) {
        PyErr_SetString(PyExc_SystemError, "failed to create a tuple");
        return NULL;
    }

    lbool res;
    Py_BEGIN_ALLOW_THREADS      /* release GIL */
    res = self->cmsat->solve(&assumption_lits);
    Py_END_ALLOW_THREADS

    if (res == l_True) {
        PyObject* solution = get_solution(self->cmsat);
        if (!solution) {
            Py_DECREF(result);
            return NULL;
        }
        Py_INCREF(Py_True);

        PyTuple_SET_ITEM(result, 0, Py_True);
        PyTuple_SET_ITEM(result, 1, solution);

    } else if (res == l_False) {
        Py_INCREF(Py_False);
        Py_INCREF(Py_None);

        PyTuple_SET_ITEM(result, 0, Py_False);
        PyTuple_SET_ITEM(result, 1, Py_None);

    } else if (res == l_Undef) {
        Py_INCREF(Py_None);
        Py_INCREF(Py_None);

        PyTuple_SET_ITEM(result, 0, Py_None);
        PyTuple_SET_ITEM(result, 1, Py_None);
    } else {
        // res can only be l_False, l_True, l_Undef
        assert((res == l_False) || (res == l_True) || (res == l_Undef));
        Py_DECREF(result);
        return PyErr_NewExceptionWithDoc("pycyrptosat.IllegalState", "Error Occured in CyrptoMiniSat", NULL, NULL);
    }

    return result;
}

PyDoc_STRVAR(is_satisfiable_doc,
"is_satisfiable()\n\
Return satisfiability of the system.\n\
\n\
:return: True or False\n\
:rtype: <boolean>"
);

static PyObject* is_satisfiable(Solver *self)
{
    lbool res;
    Py_BEGIN_ALLOW_THREADS      /* release GIL */
    res = self->cmsat->solve();
    Py_END_ALLOW_THREADS

    if (res == l_True) {
        Py_INCREF(Py_True);
        return Py_True;
    } else if (res == l_False) {
        Py_INCREF(Py_False);
        return Py_False;
    } else if (res == l_Undef) {
        return Py_None;
    } else {
        // res can only be l_False, l_True, l_Undef
        assert((res == l_False) || (res == l_True) || (res == l_Undef));
        return NULL;
    }
}

PyDoc_STRVAR(msolve_selected_doc,
"msolve_selected(max_nr_of_solutions, var_selected, raw=True)\n\
Find multiple solutions to your problem, the solver is ran in a loop and each\n\
previous solution found will be banned.\n\
\n\
.. warning:: The loop will run as long as there are solutions.\n\
    a maximum of loops must be set with 'max_nr_of_solutions' parameter\n\
\n\
.. note:: As it is highly suggested in the documentation of cryptominisat,\n\
    the new clause (banned solutions) contains the variables that are \n\
    \"important\" or \"main\" to your problem (i.e. \"var_selected\" argument).\n\
    Variables that were only used to translate the original problem into CNF \n\
    should not be added.\n\
    This way, you will not get spurious solutions that don't differ in \n\
    the main, important variables.\n\
\n\
:param arg1: Maximum number of solutions before stop the search\n\
:param arg2: Variables for which the solver must find different solutions\n\
:param arg3: (Optional) Format of literals for each solution returned. \n\
    If set to True, lists of literals will be returned;\n\
    .. example:: [(1, -2, -3, -4, -5, -6, -7, -8, -9, 10,),]\n\
    if set to False, tuples of booleans will be returned,\n\
    with None at the first position.\n\
    .. example:: [(None, True, False, True,),]\n\
:type arg1: <int>\n\
:type arg2: <list>\n\
:type arg3: <boolean>\n\
:return: List of solutions (list of tuples of literals)\n\
:rtype: <list <tuple>>"
);

static PyObject* msolve_selected(Solver *self, PyObject *args, PyObject *kwds)
{
    int max_nr_of_solutions;
    int raw_solutions_activated = true;
    PyObject *var_selected;

    static char* kwlist[] = {"max_nr_of_solutions", "var_selected", "raw", NULL};

    #ifdef IS_PY3K
    // Use 'p' wildcard for the boolean on version 3.3+ of Python
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "iO|p", kwlist,
                                     &max_nr_of_solutions,
                                     &var_selected,
                                     &raw_solutions_activated)) {
        return NULL;
    }
    #else
    // Use 'i' wildcard for the boolean on version 2.x of Python
    // O (object) [PyObject *] : Store a Python object (without any conversion) in a C object pointer.
    // https://docs.python.org/2/c-api/arg.html
    if (!PyArg_ParseTupleAndKeywords(args, kwds, "iO|i", kwlist,
                                     &max_nr_of_solutions,
                                     &var_selected,
                                     &raw_solutions_activated)) {
        return NULL;
    }
    #endif

    std::vector<Lit> var_lits;
    if (!parse_clause(self, var_selected, var_lits)) {
        return 0;
    }

    // Debug
    // std::cout << "DEBUG :: Solver: Nb max solutions: " << max_nr_of_solutions << std::endl;
    // std::cout << "DEBUG :: Solver: Raw sols activated: " << ((raw_solutions_activated) ? "True" : "False") << std::endl;
    // std::cout << "DEBUG :: Solver: Nb literals: " << var_lits.size() << std::endl;

//     for (unsigned long i = 0; i < var_lits.size(); i++) {
//         std::cout << "real value: " << var_lits[i]
//                   << "; x: " << var_lits[i].toInt()
//                   << "; sign: " << var_lits[i].sign()
//                   << "; var: " << var_lits[i].var()
//                   //<< "; toInt as long " << PyLong_AsLong(var_lits[i])
//                   << '\n';
//     }

    PyObject *solutions = PyList_New(0);
    if (solutions == NULL) {
        PyErr_SetString(PyExc_SystemError, "failed to create a list");
        return NULL;
    }

    int current_nr_of_solutions = 0;
    lbool res = l_True;
    std::vector<Lit>::iterator it;
    PyObject* solution = NULL;
    while((current_nr_of_solutions < max_nr_of_solutions) && (res == l_True)) {

        Py_BEGIN_ALLOW_THREADS      /* release GIL */
        res = self->cmsat->solve();
        Py_END_ALLOW_THREADS

        current_nr_of_solutions++;

        // std::cout << "DEBUG :: Solver: Solution number: " << current_nr_of_solutions
        //           << "; Satisfiable: " << ((res == l_True) ? "True" : "False") << std::endl;

        if(res == l_True) {

            // Memorize the solution
            if (!raw_solutions_activated) {
                // Solution in v5 format
                solution = get_solution(self->cmsat);
            } else {
                // Solution in v2.9 format
                solution = get_raw_solution(self->cmsat);
            }

            if (!solution) {
                PyErr_SetString(PyExc_SystemError, "no solution");
                Py_DECREF(solutions);
                return NULL;
            }
            // Add solution
            PyList_Append(solutions, solution);
            Py_DECREF(solution);

            // Prepare next statement
            // Ban previous solution
            if (current_nr_of_solutions < max_nr_of_solutions) {

                std::vector<Lit> ban_solution;
                const std::vector<lbool> model = self->cmsat->get_model();

                // Iterate on var_selected (instead of iterate on all vars in solver)
                for (unsigned long i = 0; i < var_lits.size(); i++) {

                    // If the current variable is > 0 (false)
                    // PS: internal value of any literal is equal to i;
                    // human readable value is i+1 (begins with 1 instead of 0)
                    if (var_lits[i].sign() == false) {

                        // The current value of the variable must belong to the solver variables
                        assert(var_lits[i].var() <= (uint32_t)self->cmsat->nVars());

                        // std::cout << "human readable lit: " << var_lits[i] << "; lit sign: " << ((var_lits[i].sign() == 0) ? "false" : "true") << std::endl;
                        // std::cout << "lit value: " << var_lits[i].var() << "; model status: " << model[var_lits[i].var()] << std::endl;

                        // Get the corresponding variable in the model, whatever its sign
                        // Add it to the futur banned clause
                        ban_solution.push_back(
                            Lit(var_lits[i].var(), (model[var_lits[i].var()] == l_True) ? true : false)
                        );
                    }
                }

                // Ban current solution for the next run
                self->cmsat->add_clause(ban_solution);

                //for (unsigned long i = 0; i < ban_solution.size(); i++) {
                //    std::cout << ban_solution[i] << ';';
                //}
                //std::cout << std::endl;
            }
        } else if (res == l_False) {
            // std::cout << "DEBUG :: Solver: No more solution" << std::endl;
        } else if (res == l_Undef) {
            Py_DECREF(solutions);
            PyErr_SetString(PyExc_SystemError, "Nothing to do => sol undef");
            return NULL;
        } else {
            // res can only be l_False, l_True, l_Undef
            assert((res == l_False) || (res == l_True) || (res == l_Undef));
            Py_DECREF(solutions);
            return NULL;
        }
    }
    // Return list of all solutions
    return solutions;
}

/*************************** Method definitions *************************/

static PyMethodDef module_methods[] = {
    {NULL, NULL, 0, NULL}  /* Sentinel - marks the end of this structure */
};

static PyMethodDef Solver_methods[] = {
    {"solve",     (PyCFunction) solve,       METH_VARARGS | METH_KEYWORDS, solve_doc},
    {"add_clause",(PyCFunction) add_clause,  METH_VARARGS | METH_KEYWORDS, add_clause_doc},
    {"add_clauses", (PyCFunction) add_clauses,  METH_VARARGS | METH_KEYWORDS, add_clauses_doc},
    {"add_xor_clause",(PyCFunction) add_xor_clause,  METH_VARARGS | METH_KEYWORDS, "adds an XOR clause to the system"},
    {"nb_vars", (PyCFunction) nb_vars, METH_VARARGS | METH_KEYWORDS, nb_vars_doc},
    //{"nb_clauses", (PyCFunction) nb_clauses, METH_VARARGS | METH_KEYWORDS, "returns number of clauses"},
    {"msolve_selected", (PyCFunction) msolve_selected, METH_VARARGS | METH_KEYWORDS, msolve_selected_doc},
    {"is_satisfiable", (PyCFunction) is_satisfiable, METH_VARARGS | METH_KEYWORDS, is_satisfiable_doc},

    {"start_getting_small_clauses", (PyCFunction) start_getting_small_clauses, METH_VARARGS | METH_KEYWORDS, start_getting_small_clauses_doc},
    {"get_next_small_clause", (PyCFunction) get_next_small_clause, METH_VARARGS | METH_KEYWORDS, get_next_small_clause_doc},
    {"end_getting_small_clauses", (PyCFunction) end_getting_small_clauses, METH_VARARGS | METH_KEYWORDS, end_getting_small_clauses_doc},
    {NULL,        NULL}  /* sentinel - marks the end of this structure */
};

static void
Solver_dealloc(Solver* self)
{
    delete self->cmsat;
    Py_TYPE(self)->tp_free ((PyObject*) self);
}

static PyObject *
Solver_new(PyTypeObject *type, PyObject *args, PyObject *kwds)
{
    Solver *self;

    self = (Solver *)type->tp_alloc(type, 0);
    if (self != NULL) {
        self->cmsat = setup_solver(args, kwds);
        if (self->cmsat == NULL) {
            Py_DECREF(self);
            return NULL;
        }
    }
    return (PyObject *)self;
}

static int
Solver_init(Solver *self, PyObject *args, PyObject *kwds)
{
    self->cmsat = setup_solver(args, kwds);
    if (!self->cmsat) {
        return -1;
    }
    return 0;
}

static PyMemberDef Solver_members[] = {
    /*{"first", T_OBJECT_EX, offsetof(Noddy, first), 0,
     "first name"},
    {"last", T_OBJECT_EX, offsetof(Noddy, last), 0,
     "last name"},
    {"number", T_INT, offsetof(Noddy, number), 0,
     "noddy number"},*/
    {NULL}  /* Sentinel */
};

static PyTypeObject pycryptosat_SolverType = {
    PyVarObject_HEAD_INIT(NULL, 0) /*ob_size*/
    "pycryptosat.Solver",       /*tp_name*/
    sizeof(Solver),             /*tp_basicsize*/
    0,                          /*tp_itemsize*/
    (destructor)Solver_dealloc, /*tp_dealloc*/
    0,                          /*tp_print*/
    0,                          /*tp_getattr*/
    0,                          /*tp_setattr*/
    0,                          /*tp_compare*/
    0,                          /*tp_repr*/
    0,                          /*tp_as_number*/
    0,                          /*tp_as_sequence*/
    0,                          /*tp_as_mapping*/
    0,                          /*tp_hash */
    0,                          /*tp_call*/
    0,                          /*tp_str*/
    0,                          /*tp_getattro*/
    0,                          /*tp_setattro*/
    0,                          /*tp_as_buffer*/
    Py_TPFLAGS_DEFAULT | Py_TPFLAGS_BASETYPE, /*tp_flags*/
    solver_create_docstring,    /* tp_doc */
    0,                          /* tp_traverse */
    0,                          /* tp_clear */
    0,                          /* tp_richcompare */
    0,                          /* tp_weaklistoffset */
    0,                          /* tp_iter */
    0,                          /* tp_iternext */
    Solver_methods,             /* tp_methods */
    Solver_members,             /* tp_members */
    0,                          /* tp_getset */
    0,                          /* tp_base */
    0,                          /* tp_dict */
    0,                          /* tp_descr_get */
    0,                          /* tp_descr_set */
    0,                          /* tp_dictoffset */
    (initproc)Solver_init,      /* tp_init */
    0,                          /* tp_alloc */
    Solver_new,                 /* tp_new */
};

MODULE_INIT_FUNC(pycryptosat)
{
    PyObject* m;

    pycryptosat_SolverType.tp_new = PyType_GenericNew;
    if (PyType_Ready(&pycryptosat_SolverType) < 0) {
        // Return NULL on Python3 and on Python2 with MODULE_INIT_FUNC macro
        // In pure Python2: return nothing.
        return NULL;
    }

    #ifdef IS_PY3K
    static struct PyModuleDef moduledef = {
        PyModuleDef_HEAD_INIT,  /* m_base */
        MODULE_NAME,            /* m_name */
        MODULE_DOC,             /* m_doc */
        -1,                     /* m_size */
        module_methods,         /* m_methods */
        NULL,                   /* m_reload */
        NULL,                   /* m_traverse */
        NULL,                   /* m_clear */
        NULL,                   /* m_free */
    };

    m = PyModule_Create(&moduledef);
    #else
    m = Py_InitModule3(MODULE_NAME, module_methods, MODULE_DOC);
    #endif

    // Return NULL on Python3 and on Python2 with MODULE_INIT_FUNC macro
    // In pure Python2: return nothing.
    if (!m) {
        Py_XDECREF(m);
        return NULL;
    }

    Py_INCREF(&pycryptosat_SolverType);
    PyModule_AddObject(m, "Solver", (PyObject *)&pycryptosat_SolverType);
    PyModule_AddObject(m, "__version__", PyUnicode_FromString(LIBRARY_VERSION));

    if (PyErr_Occurred())
    {
        PyErr_SetString(PyExc_ImportError, "pycryptosat: initialisation failed");
        Py_DECREF(m);
        m = NULL;
    }
    return m;
}
