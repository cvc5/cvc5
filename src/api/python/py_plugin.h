/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper for the cvc5 Plugin C++ class
 */

#ifndef CVC5__PY_PLUGIN_H
#define CVC5__PY_PLUGIN_H

#include <cvc5/cvc5.h>

// Created by Cython when providing 'public api' keywords
#include "cvc5_python_base_api.h"

namespace cvc5 {

class PyPlugin : public Plugin
{
 public:
  PyObject* m_obj;
  TermManager& tm;

  PyPlugin(PyObject* obj, TermManager& tm);
  virtual ~PyPlugin();

  virtual std::vector<Term> check();
  virtual void notifySatClause(const Term& cl);
  virtual void notifyTheoryLemma(const Term& lem);
  virtual std::string getName();

  std::vector<Term> plugin_check();
  void plugin_notifySatClause(const Term& cl);
  void plugin_notifyTheoryLemma(const Term& lem);
};

}  // namespace cvc5

#endif /* CVC5__PY_PLUGIN_H */