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
 */

#include "py_plugin.h"

namespace cvc5 {

PyPlugin::PyPlugin(PyObject* obj, TermManager& tm)
    : Plugin(tm), m_obj(obj), tm(tm)
{
  // Provided by "cvc5_python_base_api.h"
  if (import_cvc5__cvc5_python_base())
  {
    throw std::runtime_error("Error executing import_cvc5__cvc5_python_base");
  }
  else
  {
    Py_XINCREF(this->m_obj);
  }
}

PyPlugin::~PyPlugin() { Py_XDECREF(this->m_obj); }

std::vector<Term> PyPlugin::check()
{
  if (this->m_obj)
  {
    std::string error;
    // Call a virtual overload, if it exists
    std::vector<Term> result =
        cy_call_vec_term_func(this->m_obj, "check", &error);
    if (!error.empty()) throw std::runtime_error(error);
    return result;
  }
  else
  {
    throw std::runtime_error("'Plugin' object has not been set");
  }
}

std::vector<Term> PyPlugin::plugin_check() { return Plugin::check(); }

void PyPlugin::notifySatClause(const Term& cl)
{
  if (this->m_obj)
  {
    std::string error;
    // Call a virtual overload, if it exists
    cy_call_void_func_term(this->m_obj, "notifySatClause", cl, &error);
    if (!error.empty()) throw std::runtime_error(error);
  }
  else
  {
    throw std::runtime_error("'Plugin' object has not been set");
  }
}

void PyPlugin::plugin_notifySatClause(const Term& cl)
{
  return Plugin::notifySatClause(cl);
}

void PyPlugin::notifyTheoryLemma(const Term& lem)
{
  if (this->m_obj)
  {
    std::string error;
    // Call a virtual overload, if it exists
    cy_call_void_func_term(this->m_obj, "notifyTheoryLemma", lem, &error);
    if (!error.empty()) throw std::runtime_error(error);
  }
  else
  {
    throw std::runtime_error("'Plugin' object has not been set");
  }
}

void PyPlugin::plugin_notifyTheoryLemma(const Term& lem)
{
  return Plugin::notifyTheoryLemma(lem);
}

std::string PyPlugin::getName()
{
  if (this->m_obj)
  {
    std::string error;
    // Call a virtual overload, if it exists
    std::string result = cy_call_string_func(this->m_obj, "getName", &error);
    if (!error.empty()) throw std::runtime_error(error);
    return result;
  }
  else
  {
    throw std::runtime_error("'Plugin' object has not been set");
  }
}

}  // namespace cvc5