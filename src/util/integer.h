/*********************                                                        */
/*! \file integer.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, cconway, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A multiprecision integer constant.
 **
 ** A multiprecision integer constant.
 **/

#ifdef __CVC4__USE_GMP_IMP
#include "util/integer_gmp_imp.h"
#endif
#ifdef __CVC4__USE_CLN_IMP
#include "util/integer_cln_imp.h"
#endif
