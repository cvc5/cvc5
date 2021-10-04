/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The cvc5 Java API.
 */

#include "cvc5_DriverOptions.h"

#include "api/cpp/cvc5.h"
#include "cvc5JavaApi.h"

using namespace cvc5::api;

/*
 * Class:     cvc5_DriverOptions
 * Method:    deletePointer
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_cvc5_DriverOptions_deletePointer(JNIEnv* env,
                                                             jclass,
                                                             jlong pointer)
{
  delete reinterpret_cast<DriverOptions*>(pointer);
}
