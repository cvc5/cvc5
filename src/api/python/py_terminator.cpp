/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper for the cvc5 Terminator C++ class
 */

#include "py_terminator.h"

#include <stdexcept>

// Created by Cython when providing 'public api' keywords
#include "cvc5_python_base_api.h"

namespace cvc5 {

PyTerminator::PyTerminator(PyObject* obj) : d_obj(obj)
{
  // Provided by "cvc5_python_base_api.h"
  if (import_cvc5__cvc5_python_base())
  {
    throw std::runtime_error("Error executing import_cvc5__cvc5_python_base");
  }
}

bool PyTerminator::terminate()
{
  PyGILState_STATE state = PyGILState_Ensure();
  // Does not raise, exceptions are stored in the Python object.
  bool res = cy_call_terminate(d_obj);
  PyGILState_Release(state);
  return res;
}

}  // namespace cvc5
