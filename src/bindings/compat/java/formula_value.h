/*****************************************************************************/
/*!
 *\file formula_value.h
 *\brief enumerated type for value of formulas
 *
 * Author: Alexander Fuchs
 *
 * Created: Fri Dec 07 08:00:00 2007
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 *
 * <hr>
 */
/*****************************************************************************/

#ifndef _cvc3__include__formulavalue_h_
#define _cvc3__include__formulavalue_h_

namespace CVC3 {

/*****************************************************************************/
/*
 * Type for truth value of formulas.
 */
/*****************************************************************************/
typedef enum FormulaValue {
  TRUE_VAL,
  FALSE_VAL,
  UNKNOWN_VAL
} FormulaValue;

}

#endif
