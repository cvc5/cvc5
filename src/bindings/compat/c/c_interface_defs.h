/*****************************************************************************/
/*!
 * \file c_interface_defs.h
 *
 * Author: Clark Barrett
 *
 * Created: Thu Jun  5 13:16:26 2003
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * COPYING file provided with this distribution.
 *
 * <hr>
 *
 */
/*****************************************************************************/

#include "cvc4_public.h"

#ifndef _cvc3__include__c_interface_defs_h_
#define _cvc3__include__c_interface_defs_h_

//#include "kinds.h"

#ifdef CVC3_STRONG_TYPING

        typedef struct _cvc_VC *VC;
        typedef struct _cvc_Context *Context;
        typedef struct _cvc_ExprManager *ExprManager;
        typedef struct _cvc_Flags *Flags;

        typedef struct _cvc_Expr * Expr;
        typedef struct _cvc_Op * Op;
        typedef struct _cvc_Type* Type;
#else

        //This gives absolutely no static pointer typing.
        typedef void* VC;
        typedef void* Context;
        typedef void* ExprManager;
        typedef void* Flags;

        typedef void* Expr;
        typedef void* Op;
        typedef void* Type;
        typedef void* Proof;

#endif
#endif

