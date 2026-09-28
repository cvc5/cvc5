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

#ifndef CVC5__PY_TERMINATOR_H
#define CVC5__PY_TERMINATOR_H

// Python.h must come first to avoid libc macro redefinition warnings
#include <Python.h>
#include <cvc5/cvc5.h>

namespace cvc5 {

/** Terminator that calls method terminate() of a Python Terminator object. */
class PyTerminator : public Terminator
{
 public:
  /**
   * Constructor.
   * @param obj The Python Terminator object, which owns this object.
   */
  PyTerminator(PyObject* obj);
  bool terminate() override;

 private:
  /** The Python Terminator object (borrowed reference). */
  PyObject* d_obj;
};

}  // namespace cvc5

#endif /* CVC5__PY_TERMINATOR_H */
